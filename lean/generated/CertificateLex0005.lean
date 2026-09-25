import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_3_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3024) = lexBefore s permutation3 19 := by
  exact (positive_lex_of_descriptor s 3024 permutation3 20 (by rfl)).trans ((lex_skipped s permutation3 19 20 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation3 19) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation3 19 by rw [image3_eq]; rfl))

theorem lex_3_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3025) (Sat.Literal.pos 3024) (Sat.Literal.pos 19) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation3 19 (assignment s)
    (Sat.Literal.pos 3025) (Sat.Literal.pos 3024) (Sat.Literal.pos 19) (Sat.Literal.pos 11) (positive_of_descriptor s 3025 (.lex permutation3 19) (by rfl)) (lex_3_19_prefix s) (positive_select s 19) (lex_3_19_image s)

theorem lex_3_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.pos 19), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation3 19 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3024) (Sat.Literal.pos 19) (Sat.Literal.pos 11) (lex_3_19_prefix s) (positive_select s 19) (lex_3_19_image s)

theorem lex_3_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.pos 3024)] :=
  (lex_3_19_gate s).prop _ (List.Mem.head _)

theorem lex_3_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.neg 19), (Sat.Literal.pos 11)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.pos 19), (Sat.Literal.neg 11)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.neg 19), (Sat.Literal.neg 11), (Sat.Literal.pos 3025)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.pos 19), (Sat.Literal.pos 11), (Sat.Literal.pos 3025)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3025) = lexBefore s permutation3 18 := by
  exact (positive_lex_of_descriptor s 3025 permutation3 19 (by rfl)).trans ((lex_skipped s permutation3 18 19 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation3 18) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation3 18 by rw [image3_eq]; rfl))

theorem lex_3_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3026) (Sat.Literal.pos 3025) (Sat.Literal.pos 18) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation3 18 (assignment s)
    (Sat.Literal.pos 3026) (Sat.Literal.pos 3025) (Sat.Literal.pos 18) (Sat.Literal.pos 10) (positive_of_descriptor s 3026 (.lex permutation3 18) (by rfl)) (lex_3_18_prefix s) (positive_select s 18) (lex_3_18_image s)

theorem lex_3_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.pos 18), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation3 18 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3025) (Sat.Literal.pos 18) (Sat.Literal.pos 10) (lex_3_18_prefix s) (positive_select s 18) (lex_3_18_image s)

theorem lex_3_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.pos 3025)] :=
  (lex_3_18_gate s).prop _ (List.Mem.head _)

theorem lex_3_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.neg 18), (Sat.Literal.pos 10)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.pos 18), (Sat.Literal.neg 10)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.neg 18), (Sat.Literal.neg 10), (Sat.Literal.pos 3026)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3025), (Sat.Literal.pos 18), (Sat.Literal.pos 10), (Sat.Literal.pos 3026)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3026) = lexBefore s permutation3 17 := by
  exact (positive_lex_of_descriptor s 3026 permutation3 18 (by rfl)).trans ((lex_skipped s permutation3 17 18 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation3 17) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation3 17 by rw [image3_eq]; rfl))

theorem lex_3_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3027) (Sat.Literal.pos 3026) (Sat.Literal.pos 17) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation3 17 (assignment s)
    (Sat.Literal.pos 3027) (Sat.Literal.pos 3026) (Sat.Literal.pos 17) (Sat.Literal.pos 9) (positive_of_descriptor s 3027 (.lex permutation3 17) (by rfl)) (lex_3_17_prefix s) (positive_select s 17) (lex_3_17_image s)

theorem lex_3_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.pos 17), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation3 17 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3026) (Sat.Literal.pos 17) (Sat.Literal.pos 9) (lex_3_17_prefix s) (positive_select s 17) (lex_3_17_image s)

theorem lex_3_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.pos 3026)] :=
  (lex_3_17_gate s).prop _ (List.Mem.head _)

theorem lex_3_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.neg 17), (Sat.Literal.pos 9)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.pos 17), (Sat.Literal.neg 9)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.neg 17), (Sat.Literal.neg 9), (Sat.Literal.pos 3027)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3026), (Sat.Literal.pos 17), (Sat.Literal.pos 9), (Sat.Literal.pos 3027)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3027) = lexBefore s permutation3 16 := by
  exact (positive_lex_of_descriptor s 3027 permutation3 17 (by rfl)).trans ((lex_skipped s permutation3 16 17 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation3 16) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation3 16 by rw [image3_eq]; rfl))

theorem lex_3_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3028) (Sat.Literal.pos 3027) (Sat.Literal.pos 16) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation3 16 (assignment s)
    (Sat.Literal.pos 3028) (Sat.Literal.pos 3027) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (positive_of_descriptor s 3028 (.lex permutation3 16) (by rfl)) (lex_3_16_prefix s) (positive_select s 16) (lex_3_16_image s)

theorem lex_3_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation3 16 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3027) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (lex_3_16_prefix s) (positive_select s 16) (lex_3_16_image s)

theorem lex_3_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.pos 3027)] :=
  (lex_3_16_gate s).prop _ (List.Mem.head _)

theorem lex_3_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.neg 16), (Sat.Literal.pos 8)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.neg 16), (Sat.Literal.neg 8), (Sat.Literal.pos 3028)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3027), (Sat.Literal.pos 16), (Sat.Literal.pos 8), (Sat.Literal.pos 3028)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3028) = lexBefore s permutation3 15 := by
  exact (positive_lex_of_descriptor s 3028 permutation3 16 (by rfl)).trans ((lex_skipped s permutation3 15 16 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation3 15) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation3 15 by rw [image3_eq]; rfl))

theorem lex_3_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3029) (Sat.Literal.pos 3028) (Sat.Literal.pos 15) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation3 15 (assignment s)
    (Sat.Literal.pos 3029) (Sat.Literal.pos 3028) (Sat.Literal.pos 15) (Sat.Literal.pos 23) (positive_of_descriptor s 3029 (.lex permutation3 15) (by rfl)) (lex_3_15_prefix s) (positive_select s 15) (lex_3_15_image s)

theorem lex_3_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.pos 15), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation3 15 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3028) (Sat.Literal.pos 15) (Sat.Literal.pos 23) (lex_3_15_prefix s) (positive_select s 15) (lex_3_15_image s)

theorem lex_3_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.pos 3028)] :=
  (lex_3_15_gate s).prop _ (List.Mem.head _)

theorem lex_3_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.neg 15), (Sat.Literal.pos 23)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.pos 15), (Sat.Literal.neg 23)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.neg 15), (Sat.Literal.neg 23), (Sat.Literal.pos 3029)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3028), (Sat.Literal.pos 15), (Sat.Literal.pos 23), (Sat.Literal.pos 3029)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3029) = lexBefore s permutation3 14 := by
  exact (positive_lex_of_descriptor s 3029 permutation3 15 (by rfl)).trans ((lex_skipped s permutation3 14 15 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation3 14) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation3 14 by rw [image3_eq]; rfl))

theorem lex_3_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3030) (Sat.Literal.pos 3029) (Sat.Literal.pos 14) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation3 14 (assignment s)
    (Sat.Literal.pos 3030) (Sat.Literal.pos 3029) (Sat.Literal.pos 14) (Sat.Literal.pos 22) (positive_of_descriptor s 3030 (.lex permutation3 14) (by rfl)) (lex_3_14_prefix s) (positive_select s 14) (lex_3_14_image s)

theorem lex_3_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.pos 14), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation3 14 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3029) (Sat.Literal.pos 14) (Sat.Literal.pos 22) (lex_3_14_prefix s) (positive_select s 14) (lex_3_14_image s)

theorem lex_3_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.pos 3029)] :=
  (lex_3_14_gate s).prop _ (List.Mem.head _)

theorem lex_3_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.neg 14), (Sat.Literal.pos 22)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.pos 14), (Sat.Literal.neg 22)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.neg 14), (Sat.Literal.neg 22), (Sat.Literal.pos 3030)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3029), (Sat.Literal.pos 14), (Sat.Literal.pos 22), (Sat.Literal.pos 3030)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3030) = lexBefore s permutation3 13 := by
  exact (positive_lex_of_descriptor s 3030 permutation3 14 (by rfl)).trans ((lex_skipped s permutation3 13 14 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation3 13) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation3 13 by rw [image3_eq]; rfl))

theorem lex_3_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3031) (Sat.Literal.pos 3030) (Sat.Literal.pos 13) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation3 13 (assignment s)
    (Sat.Literal.pos 3031) (Sat.Literal.pos 3030) (Sat.Literal.pos 13) (Sat.Literal.pos 21) (positive_of_descriptor s 3031 (.lex permutation3 13) (by rfl)) (lex_3_13_prefix s) (positive_select s 13) (lex_3_13_image s)

theorem lex_3_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.pos 13), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation3 13 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3030) (Sat.Literal.pos 13) (Sat.Literal.pos 21) (lex_3_13_prefix s) (positive_select s 13) (lex_3_13_image s)

theorem lex_3_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.pos 3030)] :=
  (lex_3_13_gate s).prop _ (List.Mem.head _)

theorem lex_3_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.neg 13), (Sat.Literal.pos 21)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.pos 13), (Sat.Literal.neg 21)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.neg 13), (Sat.Literal.neg 21), (Sat.Literal.pos 3031)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3030), (Sat.Literal.pos 13), (Sat.Literal.pos 21), (Sat.Literal.pos 3031)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3031) = lexBefore s permutation3 12 := by
  exact (positive_lex_of_descriptor s 3031 permutation3 13 (by rfl)).trans ((lex_skipped s permutation3 12 13 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation3 12) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation3 12 by rw [image3_eq]; rfl))

theorem lex_3_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3032) (Sat.Literal.pos 3031) (Sat.Literal.pos 12) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation3 12 (assignment s)
    (Sat.Literal.pos 3032) (Sat.Literal.pos 3031) (Sat.Literal.pos 12) (Sat.Literal.pos 20) (positive_of_descriptor s 3032 (.lex permutation3 12) (by rfl)) (lex_3_12_prefix s) (positive_select s 12) (lex_3_12_image s)

theorem lex_3_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.pos 12), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation3 12 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3031) (Sat.Literal.pos 12) (Sat.Literal.pos 20) (lex_3_12_prefix s) (positive_select s 12) (lex_3_12_image s)

theorem lex_3_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.pos 3031)] :=
  (lex_3_12_gate s).prop _ (List.Mem.head _)

theorem lex_3_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.neg 12), (Sat.Literal.pos 20)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.pos 12), (Sat.Literal.neg 20)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.neg 12), (Sat.Literal.neg 20), (Sat.Literal.pos 3032)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3031), (Sat.Literal.pos 12), (Sat.Literal.pos 20), (Sat.Literal.pos 3032)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3032) = lexBefore s permutation3 11 := by
  exact (positive_lex_of_descriptor s 3032 permutation3 12 (by rfl)).trans ((lex_skipped s permutation3 11 12 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation3 11) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation3 11 by rw [image3_eq]; rfl))

theorem lex_3_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3033) (Sat.Literal.pos 3032) (Sat.Literal.pos 11) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation3 11 (assignment s)
    (Sat.Literal.pos 3033) (Sat.Literal.pos 3032) (Sat.Literal.pos 11) (Sat.Literal.pos 19) (positive_of_descriptor s 3033 (.lex permutation3 11) (by rfl)) (lex_3_11_prefix s) (positive_select s 11) (lex_3_11_image s)

theorem lex_3_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.pos 11), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation3 11 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3032) (Sat.Literal.pos 11) (Sat.Literal.pos 19) (lex_3_11_prefix s) (positive_select s 11) (lex_3_11_image s)

theorem lex_3_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.pos 3032)] :=
  (lex_3_11_gate s).prop _ (List.Mem.head _)

theorem lex_3_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.neg 11), (Sat.Literal.pos 19)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.pos 11), (Sat.Literal.neg 19)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.neg 11), (Sat.Literal.neg 19), (Sat.Literal.pos 3033)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3032), (Sat.Literal.pos 11), (Sat.Literal.pos 19), (Sat.Literal.pos 3033)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3033) = lexBefore s permutation3 10 := by
  exact (positive_lex_of_descriptor s 3033 permutation3 11 (by rfl)).trans ((lex_skipped s permutation3 10 11 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation3 10) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation3 10 by rw [image3_eq]; rfl))

theorem lex_3_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3034) (Sat.Literal.pos 3033) (Sat.Literal.pos 10) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation3 10 (assignment s)
    (Sat.Literal.pos 3034) (Sat.Literal.pos 3033) (Sat.Literal.pos 10) (Sat.Literal.pos 18) (positive_of_descriptor s 3034 (.lex permutation3 10) (by rfl)) (lex_3_10_prefix s) (positive_select s 10) (lex_3_10_image s)

theorem lex_3_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.pos 10), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation3 10 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3033) (Sat.Literal.pos 10) (Sat.Literal.pos 18) (lex_3_10_prefix s) (positive_select s 10) (lex_3_10_image s)

theorem lex_3_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.pos 3033)] :=
  (lex_3_10_gate s).prop _ (List.Mem.head _)

theorem lex_3_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.neg 10), (Sat.Literal.pos 18)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.pos 10), (Sat.Literal.neg 18)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.neg 10), (Sat.Literal.neg 18), (Sat.Literal.pos 3034)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3033), (Sat.Literal.pos 10), (Sat.Literal.pos 18), (Sat.Literal.pos 3034)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3034) = lexBefore s permutation3 9 := by
  exact (positive_lex_of_descriptor s 3034 permutation3 10 (by rfl)).trans ((lex_skipped s permutation3 9 10 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation3 9) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation3 9 by rw [image3_eq]; rfl))

theorem lex_3_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3035) (Sat.Literal.pos 3034) (Sat.Literal.pos 9) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation3 9 (assignment s)
    (Sat.Literal.pos 3035) (Sat.Literal.pos 3034) (Sat.Literal.pos 9) (Sat.Literal.pos 17) (positive_of_descriptor s 3035 (.lex permutation3 9) (by rfl)) (lex_3_9_prefix s) (positive_select s 9) (lex_3_9_image s)

theorem lex_3_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.pos 9), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation3 9 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3034) (Sat.Literal.pos 9) (Sat.Literal.pos 17) (lex_3_9_prefix s) (positive_select s 9) (lex_3_9_image s)

theorem lex_3_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.pos 3034)] :=
  (lex_3_9_gate s).prop _ (List.Mem.head _)

theorem lex_3_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.neg 9), (Sat.Literal.pos 17)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.pos 9), (Sat.Literal.neg 17)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.neg 9), (Sat.Literal.neg 17), (Sat.Literal.pos 3035)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3034), (Sat.Literal.pos 9), (Sat.Literal.pos 17), (Sat.Literal.pos 3035)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3035) = lexBefore s permutation3 8 := by
  exact (positive_lex_of_descriptor s 3035 permutation3 9 (by rfl)).trans ((lex_skipped s permutation3 8 9 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation3 8) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation3 8 by rw [image3_eq]; rfl))

theorem lex_3_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3036) (Sat.Literal.pos 3035) (Sat.Literal.pos 8) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation3 8 (assignment s)
    (Sat.Literal.pos 3036) (Sat.Literal.pos 3035) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (positive_of_descriptor s 3036 (.lex permutation3 8) (by rfl)) (lex_3_8_prefix s) (positive_select s 8) (lex_3_8_image s)

theorem lex_3_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation3 8 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3035) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (lex_3_8_prefix s) (positive_select s 8) (lex_3_8_image s)

theorem lex_3_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3036), (Sat.Literal.pos 3035)] :=
  (lex_3_8_gate s).prop _ (List.Mem.head _)

theorem lex_3_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3036), (Sat.Literal.neg 8), (Sat.Literal.pos 16)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3036), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.neg 8), (Sat.Literal.neg 16), (Sat.Literal.pos 3036)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3035), (Sat.Literal.pos 8), (Sat.Literal.pos 16), (Sat.Literal.pos 3036)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation4 239 := by
  exact (negative_falsum s).trans ((lex_first s permutation4 239 (by intro j hj; rw [image4_eq]; exact fixedOnRange_spec image4 240 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_4_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation4 239) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation4 239 by rw [image4_eq]; rfl))

theorem lex_4_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3037) (Sat.Literal.neg 256) (Sat.Literal.pos 239) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation4 239 (assignment s)
    (Sat.Literal.pos 3037) (Sat.Literal.neg 256) (Sat.Literal.pos 239) (Sat.Literal.pos 223) (positive_of_descriptor s 3037 (.lex permutation4 239) (by rfl)) (lex_4_239_prefix s) (positive_select s 239) (lex_4_239_image s)

theorem lex_4_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 239), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation4 239 (hmax permutation4) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 239) (Sat.Literal.pos 223) (lex_4_239_prefix s) (positive_select s 239) (lex_4_239_image s)

theorem lex_4_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.neg 256)] :=
  (lex_4_239_gate s).prop _ (List.Mem.head _)

theorem lex_4_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.neg 239), (Sat.Literal.pos 223)] :=
  (lex_4_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.pos 239), (Sat.Literal.neg 223)] :=
  (lex_4_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 239), (Sat.Literal.neg 223), (Sat.Literal.pos 3037)] :=
  (lex_4_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 239), (Sat.Literal.pos 223), (Sat.Literal.pos 3037)] :=
  (lex_4_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3037) = lexBefore s permutation4 238 := by
  exact (positive_lex_of_descriptor s 3037 permutation4 239 (by rfl)).trans ((lex_skipped s permutation4 238 239 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation4 238) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation4 238 by rw [image4_eq]; rfl))

theorem lex_4_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3038) (Sat.Literal.pos 3037) (Sat.Literal.pos 238) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation4 238 (assignment s)
    (Sat.Literal.pos 3038) (Sat.Literal.pos 3037) (Sat.Literal.pos 238) (Sat.Literal.pos 222) (positive_of_descriptor s 3038 (.lex permutation4 238) (by rfl)) (lex_4_238_prefix s) (positive_select s 238) (lex_4_238_image s)

theorem lex_4_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.pos 238), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation4 238 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3037) (Sat.Literal.pos 238) (Sat.Literal.pos 222) (lex_4_238_prefix s) (positive_select s 238) (lex_4_238_image s)

theorem lex_4_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.pos 3037)] :=
  (lex_4_238_gate s).prop _ (List.Mem.head _)

theorem lex_4_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.neg 238), (Sat.Literal.pos 222)] :=
  (lex_4_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.pos 238), (Sat.Literal.neg 222)] :=
  (lex_4_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.neg 238), (Sat.Literal.neg 222), (Sat.Literal.pos 3038)] :=
  (lex_4_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3037), (Sat.Literal.pos 238), (Sat.Literal.pos 222), (Sat.Literal.pos 3038)] :=
  (lex_4_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3038) = lexBefore s permutation4 237 := by
  exact (positive_lex_of_descriptor s 3038 permutation4 238 (by rfl)).trans ((lex_skipped s permutation4 237 238 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation4 237) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation4 237 by rw [image4_eq]; rfl))

theorem lex_4_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3039) (Sat.Literal.pos 3038) (Sat.Literal.pos 237) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation4 237 (assignment s)
    (Sat.Literal.pos 3039) (Sat.Literal.pos 3038) (Sat.Literal.pos 237) (Sat.Literal.pos 221) (positive_of_descriptor s 3039 (.lex permutation4 237) (by rfl)) (lex_4_237_prefix s) (positive_select s 237) (lex_4_237_image s)

theorem lex_4_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.pos 237), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation4 237 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3038) (Sat.Literal.pos 237) (Sat.Literal.pos 221) (lex_4_237_prefix s) (positive_select s 237) (lex_4_237_image s)

theorem lex_4_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.pos 3038)] :=
  (lex_4_237_gate s).prop _ (List.Mem.head _)

theorem lex_4_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.neg 237), (Sat.Literal.pos 221)] :=
  (lex_4_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.pos 237), (Sat.Literal.neg 221)] :=
  (lex_4_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.neg 237), (Sat.Literal.neg 221), (Sat.Literal.pos 3039)] :=
  (lex_4_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3038), (Sat.Literal.pos 237), (Sat.Literal.pos 221), (Sat.Literal.pos 3039)] :=
  (lex_4_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3039) = lexBefore s permutation4 236 := by
  exact (positive_lex_of_descriptor s 3039 permutation4 237 (by rfl)).trans ((lex_skipped s permutation4 236 237 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation4 236) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation4 236 by rw [image4_eq]; rfl))

theorem lex_4_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3040) (Sat.Literal.pos 3039) (Sat.Literal.pos 236) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation4 236 (assignment s)
    (Sat.Literal.pos 3040) (Sat.Literal.pos 3039) (Sat.Literal.pos 236) (Sat.Literal.pos 220) (positive_of_descriptor s 3040 (.lex permutation4 236) (by rfl)) (lex_4_236_prefix s) (positive_select s 236) (lex_4_236_image s)

theorem lex_4_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.pos 236), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation4 236 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3039) (Sat.Literal.pos 236) (Sat.Literal.pos 220) (lex_4_236_prefix s) (positive_select s 236) (lex_4_236_image s)

theorem lex_4_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.pos 3039)] :=
  (lex_4_236_gate s).prop _ (List.Mem.head _)

theorem lex_4_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.neg 236), (Sat.Literal.pos 220)] :=
  (lex_4_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.pos 236), (Sat.Literal.neg 220)] :=
  (lex_4_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.neg 236), (Sat.Literal.neg 220), (Sat.Literal.pos 3040)] :=
  (lex_4_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3039), (Sat.Literal.pos 236), (Sat.Literal.pos 220), (Sat.Literal.pos 3040)] :=
  (lex_4_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3040) = lexBefore s permutation4 235 := by
  exact (positive_lex_of_descriptor s 3040 permutation4 236 (by rfl)).trans ((lex_skipped s permutation4 235 236 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation4 235) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation4 235 by rw [image4_eq]; rfl))

theorem lex_4_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3041) (Sat.Literal.pos 3040) (Sat.Literal.pos 235) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation4 235 (assignment s)
    (Sat.Literal.pos 3041) (Sat.Literal.pos 3040) (Sat.Literal.pos 235) (Sat.Literal.pos 219) (positive_of_descriptor s 3041 (.lex permutation4 235) (by rfl)) (lex_4_235_prefix s) (positive_select s 235) (lex_4_235_image s)

theorem lex_4_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.pos 235), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation4 235 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3040) (Sat.Literal.pos 235) (Sat.Literal.pos 219) (lex_4_235_prefix s) (positive_select s 235) (lex_4_235_image s)

theorem lex_4_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.pos 3040)] :=
  (lex_4_235_gate s).prop _ (List.Mem.head _)

theorem lex_4_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.neg 235), (Sat.Literal.pos 219)] :=
  (lex_4_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.pos 235), (Sat.Literal.neg 219)] :=
  (lex_4_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.neg 235), (Sat.Literal.neg 219), (Sat.Literal.pos 3041)] :=
  (lex_4_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3040), (Sat.Literal.pos 235), (Sat.Literal.pos 219), (Sat.Literal.pos 3041)] :=
  (lex_4_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3041) = lexBefore s permutation4 234 := by
  exact (positive_lex_of_descriptor s 3041 permutation4 235 (by rfl)).trans ((lex_skipped s permutation4 234 235 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation4 234) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation4 234 by rw [image4_eq]; rfl))

theorem lex_4_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3042) (Sat.Literal.pos 3041) (Sat.Literal.pos 234) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation4 234 (assignment s)
    (Sat.Literal.pos 3042) (Sat.Literal.pos 3041) (Sat.Literal.pos 234) (Sat.Literal.pos 218) (positive_of_descriptor s 3042 (.lex permutation4 234) (by rfl)) (lex_4_234_prefix s) (positive_select s 234) (lex_4_234_image s)

theorem lex_4_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.pos 234), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation4 234 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3041) (Sat.Literal.pos 234) (Sat.Literal.pos 218) (lex_4_234_prefix s) (positive_select s 234) (lex_4_234_image s)

theorem lex_4_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.pos 3041)] :=
  (lex_4_234_gate s).prop _ (List.Mem.head _)

theorem lex_4_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.neg 234), (Sat.Literal.pos 218)] :=
  (lex_4_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.pos 234), (Sat.Literal.neg 218)] :=
  (lex_4_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.neg 234), (Sat.Literal.neg 218), (Sat.Literal.pos 3042)] :=
  (lex_4_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3041), (Sat.Literal.pos 234), (Sat.Literal.pos 218), (Sat.Literal.pos 3042)] :=
  (lex_4_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3042) = lexBefore s permutation4 233 := by
  exact (positive_lex_of_descriptor s 3042 permutation4 234 (by rfl)).trans ((lex_skipped s permutation4 233 234 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation4 233) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation4 233 by rw [image4_eq]; rfl))

theorem lex_4_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3043) (Sat.Literal.pos 3042) (Sat.Literal.pos 233) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation4 233 (assignment s)
    (Sat.Literal.pos 3043) (Sat.Literal.pos 3042) (Sat.Literal.pos 233) (Sat.Literal.pos 217) (positive_of_descriptor s 3043 (.lex permutation4 233) (by rfl)) (lex_4_233_prefix s) (positive_select s 233) (lex_4_233_image s)

theorem lex_4_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.pos 233), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation4 233 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3042) (Sat.Literal.pos 233) (Sat.Literal.pos 217) (lex_4_233_prefix s) (positive_select s 233) (lex_4_233_image s)

theorem lex_4_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.pos 3042)] :=
  (lex_4_233_gate s).prop _ (List.Mem.head _)

theorem lex_4_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.neg 233), (Sat.Literal.pos 217)] :=
  (lex_4_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.pos 233), (Sat.Literal.neg 217)] :=
  (lex_4_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.neg 233), (Sat.Literal.neg 217), (Sat.Literal.pos 3043)] :=
  (lex_4_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3042), (Sat.Literal.pos 233), (Sat.Literal.pos 217), (Sat.Literal.pos 3043)] :=
  (lex_4_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3043) = lexBefore s permutation4 232 := by
  exact (positive_lex_of_descriptor s 3043 permutation4 233 (by rfl)).trans ((lex_skipped s permutation4 232 233 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation4 232) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation4 232 by rw [image4_eq]; rfl))

theorem lex_4_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3044) (Sat.Literal.pos 3043) (Sat.Literal.pos 232) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation4 232 (assignment s)
    (Sat.Literal.pos 3044) (Sat.Literal.pos 3043) (Sat.Literal.pos 232) (Sat.Literal.pos 216) (positive_of_descriptor s 3044 (.lex permutation4 232) (by rfl)) (lex_4_232_prefix s) (positive_select s 232) (lex_4_232_image s)

theorem lex_4_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.pos 232), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation4 232 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3043) (Sat.Literal.pos 232) (Sat.Literal.pos 216) (lex_4_232_prefix s) (positive_select s 232) (lex_4_232_image s)

theorem lex_4_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.pos 3043)] :=
  (lex_4_232_gate s).prop _ (List.Mem.head _)

theorem lex_4_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.neg 232), (Sat.Literal.pos 216)] :=
  (lex_4_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.pos 232), (Sat.Literal.neg 216)] :=
  (lex_4_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.neg 232), (Sat.Literal.neg 216), (Sat.Literal.pos 3044)] :=
  (lex_4_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3043), (Sat.Literal.pos 232), (Sat.Literal.pos 216), (Sat.Literal.pos 3044)] :=
  (lex_4_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3044) = lexBefore s permutation4 231 := by
  exact (positive_lex_of_descriptor s 3044 permutation4 232 (by rfl)).trans ((lex_skipped s permutation4 231 232 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation4 231) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation4 231 by rw [image4_eq]; rfl))

theorem lex_4_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3045) (Sat.Literal.pos 3044) (Sat.Literal.pos 231) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation4 231 (assignment s)
    (Sat.Literal.pos 3045) (Sat.Literal.pos 3044) (Sat.Literal.pos 231) (Sat.Literal.pos 215) (positive_of_descriptor s 3045 (.lex permutation4 231) (by rfl)) (lex_4_231_prefix s) (positive_select s 231) (lex_4_231_image s)

theorem lex_4_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.pos 231), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation4 231 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3044) (Sat.Literal.pos 231) (Sat.Literal.pos 215) (lex_4_231_prefix s) (positive_select s 231) (lex_4_231_image s)

theorem lex_4_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.pos 3044)] :=
  (lex_4_231_gate s).prop _ (List.Mem.head _)

theorem lex_4_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.neg 231), (Sat.Literal.pos 215)] :=
  (lex_4_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.pos 231), (Sat.Literal.neg 215)] :=
  (lex_4_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.neg 231), (Sat.Literal.neg 215), (Sat.Literal.pos 3045)] :=
  (lex_4_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3044), (Sat.Literal.pos 231), (Sat.Literal.pos 215), (Sat.Literal.pos 3045)] :=
  (lex_4_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3045) = lexBefore s permutation4 230 := by
  exact (positive_lex_of_descriptor s 3045 permutation4 231 (by rfl)).trans ((lex_skipped s permutation4 230 231 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation4 230) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation4 230 by rw [image4_eq]; rfl))

theorem lex_4_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3046) (Sat.Literal.pos 3045) (Sat.Literal.pos 230) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation4 230 (assignment s)
    (Sat.Literal.pos 3046) (Sat.Literal.pos 3045) (Sat.Literal.pos 230) (Sat.Literal.pos 214) (positive_of_descriptor s 3046 (.lex permutation4 230) (by rfl)) (lex_4_230_prefix s) (positive_select s 230) (lex_4_230_image s)

theorem lex_4_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.pos 230), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation4 230 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3045) (Sat.Literal.pos 230) (Sat.Literal.pos 214) (lex_4_230_prefix s) (positive_select s 230) (lex_4_230_image s)

theorem lex_4_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.pos 3045)] :=
  (lex_4_230_gate s).prop _ (List.Mem.head _)

theorem lex_4_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.neg 230), (Sat.Literal.pos 214)] :=
  (lex_4_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.pos 230), (Sat.Literal.neg 214)] :=
  (lex_4_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.neg 230), (Sat.Literal.neg 214), (Sat.Literal.pos 3046)] :=
  (lex_4_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3045), (Sat.Literal.pos 230), (Sat.Literal.pos 214), (Sat.Literal.pos 3046)] :=
  (lex_4_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3046) = lexBefore s permutation4 229 := by
  exact (positive_lex_of_descriptor s 3046 permutation4 230 (by rfl)).trans ((lex_skipped s permutation4 229 230 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation4 229) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation4 229 by rw [image4_eq]; rfl))

theorem lex_4_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3047) (Sat.Literal.pos 3046) (Sat.Literal.pos 229) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation4 229 (assignment s)
    (Sat.Literal.pos 3047) (Sat.Literal.pos 3046) (Sat.Literal.pos 229) (Sat.Literal.pos 213) (positive_of_descriptor s 3047 (.lex permutation4 229) (by rfl)) (lex_4_229_prefix s) (positive_select s 229) (lex_4_229_image s)

theorem lex_4_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.pos 229), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation4 229 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3046) (Sat.Literal.pos 229) (Sat.Literal.pos 213) (lex_4_229_prefix s) (positive_select s 229) (lex_4_229_image s)

theorem lex_4_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.pos 3046)] :=
  (lex_4_229_gate s).prop _ (List.Mem.head _)

theorem lex_4_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.neg 229), (Sat.Literal.pos 213)] :=
  (lex_4_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.pos 229), (Sat.Literal.neg 213)] :=
  (lex_4_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.neg 229), (Sat.Literal.neg 213), (Sat.Literal.pos 3047)] :=
  (lex_4_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3046), (Sat.Literal.pos 229), (Sat.Literal.pos 213), (Sat.Literal.pos 3047)] :=
  (lex_4_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3047) = lexBefore s permutation4 228 := by
  exact (positive_lex_of_descriptor s 3047 permutation4 229 (by rfl)).trans ((lex_skipped s permutation4 228 229 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation4 228) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation4 228 by rw [image4_eq]; rfl))

theorem lex_4_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3048) (Sat.Literal.pos 3047) (Sat.Literal.pos 228) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation4 228 (assignment s)
    (Sat.Literal.pos 3048) (Sat.Literal.pos 3047) (Sat.Literal.pos 228) (Sat.Literal.pos 212) (positive_of_descriptor s 3048 (.lex permutation4 228) (by rfl)) (lex_4_228_prefix s) (positive_select s 228) (lex_4_228_image s)

theorem lex_4_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.pos 228), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation4 228 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3047) (Sat.Literal.pos 228) (Sat.Literal.pos 212) (lex_4_228_prefix s) (positive_select s 228) (lex_4_228_image s)

theorem lex_4_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.pos 3047)] :=
  (lex_4_228_gate s).prop _ (List.Mem.head _)

theorem lex_4_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.neg 228), (Sat.Literal.pos 212)] :=
  (lex_4_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.pos 228), (Sat.Literal.neg 212)] :=
  (lex_4_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.neg 228), (Sat.Literal.neg 212), (Sat.Literal.pos 3048)] :=
  (lex_4_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3047), (Sat.Literal.pos 228), (Sat.Literal.pos 212), (Sat.Literal.pos 3048)] :=
  (lex_4_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3048) = lexBefore s permutation4 227 := by
  exact (positive_lex_of_descriptor s 3048 permutation4 228 (by rfl)).trans ((lex_skipped s permutation4 227 228 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation4 227) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation4 227 by rw [image4_eq]; rfl))

theorem lex_4_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3049) (Sat.Literal.pos 3048) (Sat.Literal.pos 227) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation4 227 (assignment s)
    (Sat.Literal.pos 3049) (Sat.Literal.pos 3048) (Sat.Literal.pos 227) (Sat.Literal.pos 211) (positive_of_descriptor s 3049 (.lex permutation4 227) (by rfl)) (lex_4_227_prefix s) (positive_select s 227) (lex_4_227_image s)

theorem lex_4_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.pos 227), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation4 227 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3048) (Sat.Literal.pos 227) (Sat.Literal.pos 211) (lex_4_227_prefix s) (positive_select s 227) (lex_4_227_image s)

theorem lex_4_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.pos 3048)] :=
  (lex_4_227_gate s).prop _ (List.Mem.head _)

theorem lex_4_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.neg 227), (Sat.Literal.pos 211)] :=
  (lex_4_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.pos 227), (Sat.Literal.neg 211)] :=
  (lex_4_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.neg 227), (Sat.Literal.neg 211), (Sat.Literal.pos 3049)] :=
  (lex_4_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3048), (Sat.Literal.pos 227), (Sat.Literal.pos 211), (Sat.Literal.pos 3049)] :=
  (lex_4_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3049) = lexBefore s permutation4 226 := by
  exact (positive_lex_of_descriptor s 3049 permutation4 227 (by rfl)).trans ((lex_skipped s permutation4 226 227 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation4 226) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation4 226 by rw [image4_eq]; rfl))

theorem lex_4_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3050) (Sat.Literal.pos 3049) (Sat.Literal.pos 226) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation4 226 (assignment s)
    (Sat.Literal.pos 3050) (Sat.Literal.pos 3049) (Sat.Literal.pos 226) (Sat.Literal.pos 210) (positive_of_descriptor s 3050 (.lex permutation4 226) (by rfl)) (lex_4_226_prefix s) (positive_select s 226) (lex_4_226_image s)

theorem lex_4_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.pos 226), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation4 226 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3049) (Sat.Literal.pos 226) (Sat.Literal.pos 210) (lex_4_226_prefix s) (positive_select s 226) (lex_4_226_image s)

theorem lex_4_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.pos 3049)] :=
  (lex_4_226_gate s).prop _ (List.Mem.head _)

theorem lex_4_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.neg 226), (Sat.Literal.pos 210)] :=
  (lex_4_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.pos 226), (Sat.Literal.neg 210)] :=
  (lex_4_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.neg 226), (Sat.Literal.neg 210), (Sat.Literal.pos 3050)] :=
  (lex_4_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3049), (Sat.Literal.pos 226), (Sat.Literal.pos 210), (Sat.Literal.pos 3050)] :=
  (lex_4_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3050) = lexBefore s permutation4 225 := by
  exact (positive_lex_of_descriptor s 3050 permutation4 226 (by rfl)).trans ((lex_skipped s permutation4 225 226 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation4 225) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation4 225 by rw [image4_eq]; rfl))

theorem lex_4_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3051) (Sat.Literal.pos 3050) (Sat.Literal.pos 225) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation4 225 (assignment s)
    (Sat.Literal.pos 3051) (Sat.Literal.pos 3050) (Sat.Literal.pos 225) (Sat.Literal.pos 209) (positive_of_descriptor s 3051 (.lex permutation4 225) (by rfl)) (lex_4_225_prefix s) (positive_select s 225) (lex_4_225_image s)

theorem lex_4_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.pos 225), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation4 225 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3050) (Sat.Literal.pos 225) (Sat.Literal.pos 209) (lex_4_225_prefix s) (positive_select s 225) (lex_4_225_image s)

theorem lex_4_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.pos 3050)] :=
  (lex_4_225_gate s).prop _ (List.Mem.head _)

theorem lex_4_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.neg 225), (Sat.Literal.pos 209)] :=
  (lex_4_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.pos 225), (Sat.Literal.neg 209)] :=
  (lex_4_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.neg 225), (Sat.Literal.neg 209), (Sat.Literal.pos 3051)] :=
  (lex_4_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3050), (Sat.Literal.pos 225), (Sat.Literal.pos 209), (Sat.Literal.pos 3051)] :=
  (lex_4_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3051) = lexBefore s permutation4 224 := by
  exact (positive_lex_of_descriptor s 3051 permutation4 225 (by rfl)).trans ((lex_skipped s permutation4 224 225 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation4 224) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation4 224 by rw [image4_eq]; rfl))

theorem lex_4_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3052) (Sat.Literal.pos 3051) (Sat.Literal.pos 224) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation4 224 (assignment s)
    (Sat.Literal.pos 3052) (Sat.Literal.pos 3051) (Sat.Literal.pos 224) (Sat.Literal.pos 208) (positive_of_descriptor s 3052 (.lex permutation4 224) (by rfl)) (lex_4_224_prefix s) (positive_select s 224) (lex_4_224_image s)

theorem lex_4_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.pos 224), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation4 224 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3051) (Sat.Literal.pos 224) (Sat.Literal.pos 208) (lex_4_224_prefix s) (positive_select s 224) (lex_4_224_image s)

theorem lex_4_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.pos 3051)] :=
  (lex_4_224_gate s).prop _ (List.Mem.head _)

theorem lex_4_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.neg 224), (Sat.Literal.pos 208)] :=
  (lex_4_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.pos 224), (Sat.Literal.neg 208)] :=
  (lex_4_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.neg 224), (Sat.Literal.neg 208), (Sat.Literal.pos 3052)] :=
  (lex_4_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3051), (Sat.Literal.pos 224), (Sat.Literal.pos 208), (Sat.Literal.pos 3052)] :=
  (lex_4_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3052) = lexBefore s permutation4 223 := by
  exact (positive_lex_of_descriptor s 3052 permutation4 224 (by rfl)).trans ((lex_skipped s permutation4 223 224 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation4 223) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation4 223 by rw [image4_eq]; rfl))

theorem lex_4_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3053) (Sat.Literal.pos 3052) (Sat.Literal.pos 223) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation4 223 (assignment s)
    (Sat.Literal.pos 3053) (Sat.Literal.pos 3052) (Sat.Literal.pos 223) (Sat.Literal.pos 239) (positive_of_descriptor s 3053 (.lex permutation4 223) (by rfl)) (lex_4_223_prefix s) (positive_select s 223) (lex_4_223_image s)

theorem lex_4_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.pos 223), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation4 223 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3052) (Sat.Literal.pos 223) (Sat.Literal.pos 239) (lex_4_223_prefix s) (positive_select s 223) (lex_4_223_image s)

theorem lex_4_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.pos 3052)] :=
  (lex_4_223_gate s).prop _ (List.Mem.head _)

theorem lex_4_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.neg 223), (Sat.Literal.pos 239)] :=
  (lex_4_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.pos 223), (Sat.Literal.neg 239)] :=
  (lex_4_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.neg 223), (Sat.Literal.neg 239), (Sat.Literal.pos 3053)] :=
  (lex_4_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3052), (Sat.Literal.pos 223), (Sat.Literal.pos 239), (Sat.Literal.pos 3053)] :=
  (lex_4_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3053) = lexBefore s permutation4 222 := by
  exact (positive_lex_of_descriptor s 3053 permutation4 223 (by rfl)).trans ((lex_skipped s permutation4 222 223 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation4 222) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation4 222 by rw [image4_eq]; rfl))

theorem lex_4_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3054) (Sat.Literal.pos 3053) (Sat.Literal.pos 222) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation4 222 (assignment s)
    (Sat.Literal.pos 3054) (Sat.Literal.pos 3053) (Sat.Literal.pos 222) (Sat.Literal.pos 238) (positive_of_descriptor s 3054 (.lex permutation4 222) (by rfl)) (lex_4_222_prefix s) (positive_select s 222) (lex_4_222_image s)

theorem lex_4_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.pos 222), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation4 222 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3053) (Sat.Literal.pos 222) (Sat.Literal.pos 238) (lex_4_222_prefix s) (positive_select s 222) (lex_4_222_image s)

theorem lex_4_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.pos 3053)] :=
  (lex_4_222_gate s).prop _ (List.Mem.head _)

theorem lex_4_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.neg 222), (Sat.Literal.pos 238)] :=
  (lex_4_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.pos 222), (Sat.Literal.neg 238)] :=
  (lex_4_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.neg 222), (Sat.Literal.neg 238), (Sat.Literal.pos 3054)] :=
  (lex_4_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3053), (Sat.Literal.pos 222), (Sat.Literal.pos 238), (Sat.Literal.pos 3054)] :=
  (lex_4_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3054) = lexBefore s permutation4 221 := by
  exact (positive_lex_of_descriptor s 3054 permutation4 222 (by rfl)).trans ((lex_skipped s permutation4 221 222 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation4 221) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation4 221 by rw [image4_eq]; rfl))

theorem lex_4_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3055) (Sat.Literal.pos 3054) (Sat.Literal.pos 221) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation4 221 (assignment s)
    (Sat.Literal.pos 3055) (Sat.Literal.pos 3054) (Sat.Literal.pos 221) (Sat.Literal.pos 237) (positive_of_descriptor s 3055 (.lex permutation4 221) (by rfl)) (lex_4_221_prefix s) (positive_select s 221) (lex_4_221_image s)

theorem lex_4_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.pos 221), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation4 221 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3054) (Sat.Literal.pos 221) (Sat.Literal.pos 237) (lex_4_221_prefix s) (positive_select s 221) (lex_4_221_image s)

theorem lex_4_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.pos 3054)] :=
  (lex_4_221_gate s).prop _ (List.Mem.head _)

theorem lex_4_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.neg 221), (Sat.Literal.pos 237)] :=
  (lex_4_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.pos 221), (Sat.Literal.neg 237)] :=
  (lex_4_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.neg 221), (Sat.Literal.neg 237), (Sat.Literal.pos 3055)] :=
  (lex_4_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3054), (Sat.Literal.pos 221), (Sat.Literal.pos 237), (Sat.Literal.pos 3055)] :=
  (lex_4_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3055) = lexBefore s permutation4 220 := by
  exact (positive_lex_of_descriptor s 3055 permutation4 221 (by rfl)).trans ((lex_skipped s permutation4 220 221 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation4 220) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation4 220 by rw [image4_eq]; rfl))

theorem lex_4_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3056) (Sat.Literal.pos 3055) (Sat.Literal.pos 220) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation4 220 (assignment s)
    (Sat.Literal.pos 3056) (Sat.Literal.pos 3055) (Sat.Literal.pos 220) (Sat.Literal.pos 236) (positive_of_descriptor s 3056 (.lex permutation4 220) (by rfl)) (lex_4_220_prefix s) (positive_select s 220) (lex_4_220_image s)

theorem lex_4_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.pos 220), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation4 220 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3055) (Sat.Literal.pos 220) (Sat.Literal.pos 236) (lex_4_220_prefix s) (positive_select s 220) (lex_4_220_image s)

theorem lex_4_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.pos 3055)] :=
  (lex_4_220_gate s).prop _ (List.Mem.head _)

theorem lex_4_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.neg 220), (Sat.Literal.pos 236)] :=
  (lex_4_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.pos 220), (Sat.Literal.neg 236)] :=
  (lex_4_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.neg 220), (Sat.Literal.neg 236), (Sat.Literal.pos 3056)] :=
  (lex_4_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3055), (Sat.Literal.pos 220), (Sat.Literal.pos 236), (Sat.Literal.pos 3056)] :=
  (lex_4_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3056) = lexBefore s permutation4 219 := by
  exact (positive_lex_of_descriptor s 3056 permutation4 220 (by rfl)).trans ((lex_skipped s permutation4 219 220 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation4 219) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation4 219 by rw [image4_eq]; rfl))

theorem lex_4_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3057) (Sat.Literal.pos 3056) (Sat.Literal.pos 219) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation4 219 (assignment s)
    (Sat.Literal.pos 3057) (Sat.Literal.pos 3056) (Sat.Literal.pos 219) (Sat.Literal.pos 235) (positive_of_descriptor s 3057 (.lex permutation4 219) (by rfl)) (lex_4_219_prefix s) (positive_select s 219) (lex_4_219_image s)

theorem lex_4_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.pos 219), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation4 219 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3056) (Sat.Literal.pos 219) (Sat.Literal.pos 235) (lex_4_219_prefix s) (positive_select s 219) (lex_4_219_image s)

theorem lex_4_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.pos 3056)] :=
  (lex_4_219_gate s).prop _ (List.Mem.head _)

theorem lex_4_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.neg 219), (Sat.Literal.pos 235)] :=
  (lex_4_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.pos 219), (Sat.Literal.neg 235)] :=
  (lex_4_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.neg 219), (Sat.Literal.neg 235), (Sat.Literal.pos 3057)] :=
  (lex_4_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3056), (Sat.Literal.pos 219), (Sat.Literal.pos 235), (Sat.Literal.pos 3057)] :=
  (lex_4_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3057) = lexBefore s permutation4 218 := by
  exact (positive_lex_of_descriptor s 3057 permutation4 219 (by rfl)).trans ((lex_skipped s permutation4 218 219 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation4 218) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation4 218 by rw [image4_eq]; rfl))

theorem lex_4_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3058) (Sat.Literal.pos 3057) (Sat.Literal.pos 218) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation4 218 (assignment s)
    (Sat.Literal.pos 3058) (Sat.Literal.pos 3057) (Sat.Literal.pos 218) (Sat.Literal.pos 234) (positive_of_descriptor s 3058 (.lex permutation4 218) (by rfl)) (lex_4_218_prefix s) (positive_select s 218) (lex_4_218_image s)

theorem lex_4_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.pos 218), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation4 218 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3057) (Sat.Literal.pos 218) (Sat.Literal.pos 234) (lex_4_218_prefix s) (positive_select s 218) (lex_4_218_image s)

theorem lex_4_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.pos 3057)] :=
  (lex_4_218_gate s).prop _ (List.Mem.head _)

theorem lex_4_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.neg 218), (Sat.Literal.pos 234)] :=
  (lex_4_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.pos 218), (Sat.Literal.neg 234)] :=
  (lex_4_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.neg 218), (Sat.Literal.neg 234), (Sat.Literal.pos 3058)] :=
  (lex_4_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3057), (Sat.Literal.pos 218), (Sat.Literal.pos 234), (Sat.Literal.pos 3058)] :=
  (lex_4_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3058) = lexBefore s permutation4 217 := by
  exact (positive_lex_of_descriptor s 3058 permutation4 218 (by rfl)).trans ((lex_skipped s permutation4 217 218 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation4 217) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation4 217 by rw [image4_eq]; rfl))

theorem lex_4_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3059) (Sat.Literal.pos 3058) (Sat.Literal.pos 217) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation4 217 (assignment s)
    (Sat.Literal.pos 3059) (Sat.Literal.pos 3058) (Sat.Literal.pos 217) (Sat.Literal.pos 233) (positive_of_descriptor s 3059 (.lex permutation4 217) (by rfl)) (lex_4_217_prefix s) (positive_select s 217) (lex_4_217_image s)

theorem lex_4_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.pos 217), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation4 217 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3058) (Sat.Literal.pos 217) (Sat.Literal.pos 233) (lex_4_217_prefix s) (positive_select s 217) (lex_4_217_image s)

theorem lex_4_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.pos 3058)] :=
  (lex_4_217_gate s).prop _ (List.Mem.head _)

theorem lex_4_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.neg 217), (Sat.Literal.pos 233)] :=
  (lex_4_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.pos 217), (Sat.Literal.neg 233)] :=
  (lex_4_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.neg 217), (Sat.Literal.neg 233), (Sat.Literal.pos 3059)] :=
  (lex_4_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3058), (Sat.Literal.pos 217), (Sat.Literal.pos 233), (Sat.Literal.pos 3059)] :=
  (lex_4_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3059) = lexBefore s permutation4 216 := by
  exact (positive_lex_of_descriptor s 3059 permutation4 217 (by rfl)).trans ((lex_skipped s permutation4 216 217 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation4 216) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation4 216 by rw [image4_eq]; rfl))

theorem lex_4_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3060) (Sat.Literal.pos 3059) (Sat.Literal.pos 216) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation4 216 (assignment s)
    (Sat.Literal.pos 3060) (Sat.Literal.pos 3059) (Sat.Literal.pos 216) (Sat.Literal.pos 232) (positive_of_descriptor s 3060 (.lex permutation4 216) (by rfl)) (lex_4_216_prefix s) (positive_select s 216) (lex_4_216_image s)

theorem lex_4_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.pos 216), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation4 216 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3059) (Sat.Literal.pos 216) (Sat.Literal.pos 232) (lex_4_216_prefix s) (positive_select s 216) (lex_4_216_image s)

theorem lex_4_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.pos 3059)] :=
  (lex_4_216_gate s).prop _ (List.Mem.head _)

theorem lex_4_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.neg 216), (Sat.Literal.pos 232)] :=
  (lex_4_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.pos 216), (Sat.Literal.neg 232)] :=
  (lex_4_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.neg 216), (Sat.Literal.neg 232), (Sat.Literal.pos 3060)] :=
  (lex_4_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3059), (Sat.Literal.pos 216), (Sat.Literal.pos 232), (Sat.Literal.pos 3060)] :=
  (lex_4_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3060) = lexBefore s permutation4 215 := by
  exact (positive_lex_of_descriptor s 3060 permutation4 216 (by rfl)).trans ((lex_skipped s permutation4 215 216 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation4 215) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation4 215 by rw [image4_eq]; rfl))

theorem lex_4_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3061) (Sat.Literal.pos 3060) (Sat.Literal.pos 215) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation4 215 (assignment s)
    (Sat.Literal.pos 3061) (Sat.Literal.pos 3060) (Sat.Literal.pos 215) (Sat.Literal.pos 231) (positive_of_descriptor s 3061 (.lex permutation4 215) (by rfl)) (lex_4_215_prefix s) (positive_select s 215) (lex_4_215_image s)

theorem lex_4_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.pos 215), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation4 215 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3060) (Sat.Literal.pos 215) (Sat.Literal.pos 231) (lex_4_215_prefix s) (positive_select s 215) (lex_4_215_image s)

theorem lex_4_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.pos 3060)] :=
  (lex_4_215_gate s).prop _ (List.Mem.head _)

theorem lex_4_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.neg 215), (Sat.Literal.pos 231)] :=
  (lex_4_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.pos 215), (Sat.Literal.neg 231)] :=
  (lex_4_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.neg 215), (Sat.Literal.neg 231), (Sat.Literal.pos 3061)] :=
  (lex_4_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3060), (Sat.Literal.pos 215), (Sat.Literal.pos 231), (Sat.Literal.pos 3061)] :=
  (lex_4_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3061) = lexBefore s permutation4 214 := by
  exact (positive_lex_of_descriptor s 3061 permutation4 215 (by rfl)).trans ((lex_skipped s permutation4 214 215 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation4 214) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation4 214 by rw [image4_eq]; rfl))

theorem lex_4_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3062) (Sat.Literal.pos 3061) (Sat.Literal.pos 214) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation4 214 (assignment s)
    (Sat.Literal.pos 3062) (Sat.Literal.pos 3061) (Sat.Literal.pos 214) (Sat.Literal.pos 230) (positive_of_descriptor s 3062 (.lex permutation4 214) (by rfl)) (lex_4_214_prefix s) (positive_select s 214) (lex_4_214_image s)

theorem lex_4_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.pos 214), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation4 214 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3061) (Sat.Literal.pos 214) (Sat.Literal.pos 230) (lex_4_214_prefix s) (positive_select s 214) (lex_4_214_image s)

theorem lex_4_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.pos 3061)] :=
  (lex_4_214_gate s).prop _ (List.Mem.head _)

theorem lex_4_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.neg 214), (Sat.Literal.pos 230)] :=
  (lex_4_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.pos 214), (Sat.Literal.neg 230)] :=
  (lex_4_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.neg 214), (Sat.Literal.neg 230), (Sat.Literal.pos 3062)] :=
  (lex_4_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3061), (Sat.Literal.pos 214), (Sat.Literal.pos 230), (Sat.Literal.pos 3062)] :=
  (lex_4_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3062) = lexBefore s permutation4 213 := by
  exact (positive_lex_of_descriptor s 3062 permutation4 214 (by rfl)).trans ((lex_skipped s permutation4 213 214 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation4 213) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation4 213 by rw [image4_eq]; rfl))

theorem lex_4_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3063) (Sat.Literal.pos 3062) (Sat.Literal.pos 213) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation4 213 (assignment s)
    (Sat.Literal.pos 3063) (Sat.Literal.pos 3062) (Sat.Literal.pos 213) (Sat.Literal.pos 229) (positive_of_descriptor s 3063 (.lex permutation4 213) (by rfl)) (lex_4_213_prefix s) (positive_select s 213) (lex_4_213_image s)

theorem lex_4_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.pos 213), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation4 213 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3062) (Sat.Literal.pos 213) (Sat.Literal.pos 229) (lex_4_213_prefix s) (positive_select s 213) (lex_4_213_image s)

theorem lex_4_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.pos 3062)] :=
  (lex_4_213_gate s).prop _ (List.Mem.head _)

theorem lex_4_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.neg 213), (Sat.Literal.pos 229)] :=
  (lex_4_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.pos 213), (Sat.Literal.neg 229)] :=
  (lex_4_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.neg 213), (Sat.Literal.neg 229), (Sat.Literal.pos 3063)] :=
  (lex_4_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3062), (Sat.Literal.pos 213), (Sat.Literal.pos 229), (Sat.Literal.pos 3063)] :=
  (lex_4_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3063) = lexBefore s permutation4 212 := by
  exact (positive_lex_of_descriptor s 3063 permutation4 213 (by rfl)).trans ((lex_skipped s permutation4 212 213 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation4 212) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation4 212 by rw [image4_eq]; rfl))

theorem lex_4_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3064) (Sat.Literal.pos 3063) (Sat.Literal.pos 212) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation4 212 (assignment s)
    (Sat.Literal.pos 3064) (Sat.Literal.pos 3063) (Sat.Literal.pos 212) (Sat.Literal.pos 228) (positive_of_descriptor s 3064 (.lex permutation4 212) (by rfl)) (lex_4_212_prefix s) (positive_select s 212) (lex_4_212_image s)

theorem lex_4_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.pos 212), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation4 212 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3063) (Sat.Literal.pos 212) (Sat.Literal.pos 228) (lex_4_212_prefix s) (positive_select s 212) (lex_4_212_image s)

theorem lex_4_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.pos 3063)] :=
  (lex_4_212_gate s).prop _ (List.Mem.head _)

theorem lex_4_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.neg 212), (Sat.Literal.pos 228)] :=
  (lex_4_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.pos 212), (Sat.Literal.neg 228)] :=
  (lex_4_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.neg 212), (Sat.Literal.neg 228), (Sat.Literal.pos 3064)] :=
  (lex_4_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3063), (Sat.Literal.pos 212), (Sat.Literal.pos 228), (Sat.Literal.pos 3064)] :=
  (lex_4_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3064) = lexBefore s permutation4 211 := by
  exact (positive_lex_of_descriptor s 3064 permutation4 212 (by rfl)).trans ((lex_skipped s permutation4 211 212 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation4 211) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation4 211 by rw [image4_eq]; rfl))

theorem lex_4_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3065) (Sat.Literal.pos 3064) (Sat.Literal.pos 211) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation4 211 (assignment s)
    (Sat.Literal.pos 3065) (Sat.Literal.pos 3064) (Sat.Literal.pos 211) (Sat.Literal.pos 227) (positive_of_descriptor s 3065 (.lex permutation4 211) (by rfl)) (lex_4_211_prefix s) (positive_select s 211) (lex_4_211_image s)

theorem lex_4_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.pos 211), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation4 211 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3064) (Sat.Literal.pos 211) (Sat.Literal.pos 227) (lex_4_211_prefix s) (positive_select s 211) (lex_4_211_image s)

theorem lex_4_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.pos 3064)] :=
  (lex_4_211_gate s).prop _ (List.Mem.head _)

theorem lex_4_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.neg 211), (Sat.Literal.pos 227)] :=
  (lex_4_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.pos 211), (Sat.Literal.neg 227)] :=
  (lex_4_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.neg 211), (Sat.Literal.neg 227), (Sat.Literal.pos 3065)] :=
  (lex_4_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3064), (Sat.Literal.pos 211), (Sat.Literal.pos 227), (Sat.Literal.pos 3065)] :=
  (lex_4_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3065) = lexBefore s permutation4 210 := by
  exact (positive_lex_of_descriptor s 3065 permutation4 211 (by rfl)).trans ((lex_skipped s permutation4 210 211 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation4 210) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation4 210 by rw [image4_eq]; rfl))

theorem lex_4_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3066) (Sat.Literal.pos 3065) (Sat.Literal.pos 210) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation4 210 (assignment s)
    (Sat.Literal.pos 3066) (Sat.Literal.pos 3065) (Sat.Literal.pos 210) (Sat.Literal.pos 226) (positive_of_descriptor s 3066 (.lex permutation4 210) (by rfl)) (lex_4_210_prefix s) (positive_select s 210) (lex_4_210_image s)

theorem lex_4_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.pos 210), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation4 210 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3065) (Sat.Literal.pos 210) (Sat.Literal.pos 226) (lex_4_210_prefix s) (positive_select s 210) (lex_4_210_image s)

theorem lex_4_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.pos 3065)] :=
  (lex_4_210_gate s).prop _ (List.Mem.head _)

theorem lex_4_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.neg 210), (Sat.Literal.pos 226)] :=
  (lex_4_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.pos 210), (Sat.Literal.neg 226)] :=
  (lex_4_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.neg 210), (Sat.Literal.neg 226), (Sat.Literal.pos 3066)] :=
  (lex_4_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3065), (Sat.Literal.pos 210), (Sat.Literal.pos 226), (Sat.Literal.pos 3066)] :=
  (lex_4_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3066) = lexBefore s permutation4 209 := by
  exact (positive_lex_of_descriptor s 3066 permutation4 210 (by rfl)).trans ((lex_skipped s permutation4 209 210 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation4 209) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation4 209 by rw [image4_eq]; rfl))

theorem lex_4_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3067) (Sat.Literal.pos 3066) (Sat.Literal.pos 209) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation4 209 (assignment s)
    (Sat.Literal.pos 3067) (Sat.Literal.pos 3066) (Sat.Literal.pos 209) (Sat.Literal.pos 225) (positive_of_descriptor s 3067 (.lex permutation4 209) (by rfl)) (lex_4_209_prefix s) (positive_select s 209) (lex_4_209_image s)

theorem lex_4_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.pos 209), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation4 209 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3066) (Sat.Literal.pos 209) (Sat.Literal.pos 225) (lex_4_209_prefix s) (positive_select s 209) (lex_4_209_image s)

theorem lex_4_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.pos 3066)] :=
  (lex_4_209_gate s).prop _ (List.Mem.head _)

theorem lex_4_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.neg 209), (Sat.Literal.pos 225)] :=
  (lex_4_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.pos 209), (Sat.Literal.neg 225)] :=
  (lex_4_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.neg 209), (Sat.Literal.neg 225), (Sat.Literal.pos 3067)] :=
  (lex_4_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3066), (Sat.Literal.pos 209), (Sat.Literal.pos 225), (Sat.Literal.pos 3067)] :=
  (lex_4_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3067) = lexBefore s permutation4 208 := by
  exact (positive_lex_of_descriptor s 3067 permutation4 209 (by rfl)).trans ((lex_skipped s permutation4 208 209 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation4 208) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation4 208 by rw [image4_eq]; rfl))

theorem lex_4_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3068) (Sat.Literal.pos 3067) (Sat.Literal.pos 208) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation4 208 (assignment s)
    (Sat.Literal.pos 3068) (Sat.Literal.pos 3067) (Sat.Literal.pos 208) (Sat.Literal.pos 224) (positive_of_descriptor s 3068 (.lex permutation4 208) (by rfl)) (lex_4_208_prefix s) (positive_select s 208) (lex_4_208_image s)

theorem lex_4_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.pos 208), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation4 208 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3067) (Sat.Literal.pos 208) (Sat.Literal.pos 224) (lex_4_208_prefix s) (positive_select s 208) (lex_4_208_image s)

theorem lex_4_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.pos 3067)] :=
  (lex_4_208_gate s).prop _ (List.Mem.head _)

theorem lex_4_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.neg 208), (Sat.Literal.pos 224)] :=
  (lex_4_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.pos 208), (Sat.Literal.neg 224)] :=
  (lex_4_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.neg 208), (Sat.Literal.neg 224), (Sat.Literal.pos 3068)] :=
  (lex_4_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3067), (Sat.Literal.pos 208), (Sat.Literal.pos 224), (Sat.Literal.pos 3068)] :=
  (lex_4_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3068) = lexBefore s permutation4 175 := by
  exact (positive_lex_of_descriptor s 3068 permutation4 208 (by rfl)).trans ((lex_skipped s permutation4 175 208 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 176 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation4 175) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation4 175 by rw [image4_eq]; rfl))

theorem lex_4_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3069) (Sat.Literal.pos 3068) (Sat.Literal.pos 175) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation4 175 (assignment s)
    (Sat.Literal.pos 3069) (Sat.Literal.pos 3068) (Sat.Literal.pos 175) (Sat.Literal.pos 159) (positive_of_descriptor s 3069 (.lex permutation4 175) (by rfl)) (lex_4_175_prefix s) (positive_select s 175) (lex_4_175_image s)

theorem lex_4_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.pos 175), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation4 175 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3068) (Sat.Literal.pos 175) (Sat.Literal.pos 159) (lex_4_175_prefix s) (positive_select s 175) (lex_4_175_image s)

theorem lex_4_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.pos 3068)] :=
  (lex_4_175_gate s).prop _ (List.Mem.head _)

theorem lex_4_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.neg 175), (Sat.Literal.pos 159)] :=
  (lex_4_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.pos 175), (Sat.Literal.neg 159)] :=
  (lex_4_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.neg 175), (Sat.Literal.neg 159), (Sat.Literal.pos 3069)] :=
  (lex_4_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3068), (Sat.Literal.pos 175), (Sat.Literal.pos 159), (Sat.Literal.pos 3069)] :=
  (lex_4_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3069) = lexBefore s permutation4 174 := by
  exact (positive_lex_of_descriptor s 3069 permutation4 175 (by rfl)).trans ((lex_skipped s permutation4 174 175 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation4 174) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation4 174 by rw [image4_eq]; rfl))

theorem lex_4_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3070) (Sat.Literal.pos 3069) (Sat.Literal.pos 174) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation4 174 (assignment s)
    (Sat.Literal.pos 3070) (Sat.Literal.pos 3069) (Sat.Literal.pos 174) (Sat.Literal.pos 158) (positive_of_descriptor s 3070 (.lex permutation4 174) (by rfl)) (lex_4_174_prefix s) (positive_select s 174) (lex_4_174_image s)

theorem lex_4_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.pos 174), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation4 174 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3069) (Sat.Literal.pos 174) (Sat.Literal.pos 158) (lex_4_174_prefix s) (positive_select s 174) (lex_4_174_image s)

theorem lex_4_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.pos 3069)] :=
  (lex_4_174_gate s).prop _ (List.Mem.head _)

theorem lex_4_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.neg 174), (Sat.Literal.pos 158)] :=
  (lex_4_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.pos 174), (Sat.Literal.neg 158)] :=
  (lex_4_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.neg 174), (Sat.Literal.neg 158), (Sat.Literal.pos 3070)] :=
  (lex_4_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3069), (Sat.Literal.pos 174), (Sat.Literal.pos 158), (Sat.Literal.pos 3070)] :=
  (lex_4_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3070) = lexBefore s permutation4 173 := by
  exact (positive_lex_of_descriptor s 3070 permutation4 174 (by rfl)).trans ((lex_skipped s permutation4 173 174 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation4 173) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation4 173 by rw [image4_eq]; rfl))

theorem lex_4_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3071) (Sat.Literal.pos 3070) (Sat.Literal.pos 173) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation4 173 (assignment s)
    (Sat.Literal.pos 3071) (Sat.Literal.pos 3070) (Sat.Literal.pos 173) (Sat.Literal.pos 157) (positive_of_descriptor s 3071 (.lex permutation4 173) (by rfl)) (lex_4_173_prefix s) (positive_select s 173) (lex_4_173_image s)

theorem lex_4_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.pos 173), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation4 173 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3070) (Sat.Literal.pos 173) (Sat.Literal.pos 157) (lex_4_173_prefix s) (positive_select s 173) (lex_4_173_image s)

theorem lex_4_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.pos 3070)] :=
  (lex_4_173_gate s).prop _ (List.Mem.head _)

theorem lex_4_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.neg 173), (Sat.Literal.pos 157)] :=
  (lex_4_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.pos 173), (Sat.Literal.neg 157)] :=
  (lex_4_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.neg 173), (Sat.Literal.neg 157), (Sat.Literal.pos 3071)] :=
  (lex_4_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3070), (Sat.Literal.pos 173), (Sat.Literal.pos 157), (Sat.Literal.pos 3071)] :=
  (lex_4_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3071) = lexBefore s permutation4 172 := by
  exact (positive_lex_of_descriptor s 3071 permutation4 173 (by rfl)).trans ((lex_skipped s permutation4 172 173 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation4 172) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation4 172 by rw [image4_eq]; rfl))

theorem lex_4_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3072) (Sat.Literal.pos 3071) (Sat.Literal.pos 172) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation4 172 (assignment s)
    (Sat.Literal.pos 3072) (Sat.Literal.pos 3071) (Sat.Literal.pos 172) (Sat.Literal.pos 156) (positive_of_descriptor s 3072 (.lex permutation4 172) (by rfl)) (lex_4_172_prefix s) (positive_select s 172) (lex_4_172_image s)

theorem lex_4_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.pos 172), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation4 172 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3071) (Sat.Literal.pos 172) (Sat.Literal.pos 156) (lex_4_172_prefix s) (positive_select s 172) (lex_4_172_image s)

theorem lex_4_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.pos 3071)] :=
  (lex_4_172_gate s).prop _ (List.Mem.head _)

theorem lex_4_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.neg 172), (Sat.Literal.pos 156)] :=
  (lex_4_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.pos 172), (Sat.Literal.neg 156)] :=
  (lex_4_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.neg 172), (Sat.Literal.neg 156), (Sat.Literal.pos 3072)] :=
  (lex_4_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3071), (Sat.Literal.pos 172), (Sat.Literal.pos 156), (Sat.Literal.pos 3072)] :=
  (lex_4_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3072) = lexBefore s permutation4 171 := by
  exact (positive_lex_of_descriptor s 3072 permutation4 172 (by rfl)).trans ((lex_skipped s permutation4 171 172 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation4 171) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation4 171 by rw [image4_eq]; rfl))

theorem lex_4_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3073) (Sat.Literal.pos 3072) (Sat.Literal.pos 171) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation4 171 (assignment s)
    (Sat.Literal.pos 3073) (Sat.Literal.pos 3072) (Sat.Literal.pos 171) (Sat.Literal.pos 155) (positive_of_descriptor s 3073 (.lex permutation4 171) (by rfl)) (lex_4_171_prefix s) (positive_select s 171) (lex_4_171_image s)

theorem lex_4_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.pos 171), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation4 171 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3072) (Sat.Literal.pos 171) (Sat.Literal.pos 155) (lex_4_171_prefix s) (positive_select s 171) (lex_4_171_image s)

theorem lex_4_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.pos 3072)] :=
  (lex_4_171_gate s).prop _ (List.Mem.head _)

theorem lex_4_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.neg 171), (Sat.Literal.pos 155)] :=
  (lex_4_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.pos 171), (Sat.Literal.neg 155)] :=
  (lex_4_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.neg 171), (Sat.Literal.neg 155), (Sat.Literal.pos 3073)] :=
  (lex_4_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3072), (Sat.Literal.pos 171), (Sat.Literal.pos 155), (Sat.Literal.pos 3073)] :=
  (lex_4_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3073) = lexBefore s permutation4 170 := by
  exact (positive_lex_of_descriptor s 3073 permutation4 171 (by rfl)).trans ((lex_skipped s permutation4 170 171 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation4 170) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation4 170 by rw [image4_eq]; rfl))

theorem lex_4_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3074) (Sat.Literal.pos 3073) (Sat.Literal.pos 170) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation4 170 (assignment s)
    (Sat.Literal.pos 3074) (Sat.Literal.pos 3073) (Sat.Literal.pos 170) (Sat.Literal.pos 154) (positive_of_descriptor s 3074 (.lex permutation4 170) (by rfl)) (lex_4_170_prefix s) (positive_select s 170) (lex_4_170_image s)

theorem lex_4_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.pos 170), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation4 170 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3073) (Sat.Literal.pos 170) (Sat.Literal.pos 154) (lex_4_170_prefix s) (positive_select s 170) (lex_4_170_image s)

theorem lex_4_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.pos 3073)] :=
  (lex_4_170_gate s).prop _ (List.Mem.head _)

theorem lex_4_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.neg 170), (Sat.Literal.pos 154)] :=
  (lex_4_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.pos 170), (Sat.Literal.neg 154)] :=
  (lex_4_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.neg 170), (Sat.Literal.neg 154), (Sat.Literal.pos 3074)] :=
  (lex_4_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3073), (Sat.Literal.pos 170), (Sat.Literal.pos 154), (Sat.Literal.pos 3074)] :=
  (lex_4_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3074) = lexBefore s permutation4 169 := by
  exact (positive_lex_of_descriptor s 3074 permutation4 170 (by rfl)).trans ((lex_skipped s permutation4 169 170 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation4 169) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation4 169 by rw [image4_eq]; rfl))

theorem lex_4_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3075) (Sat.Literal.pos 3074) (Sat.Literal.pos 169) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation4 169 (assignment s)
    (Sat.Literal.pos 3075) (Sat.Literal.pos 3074) (Sat.Literal.pos 169) (Sat.Literal.pos 153) (positive_of_descriptor s 3075 (.lex permutation4 169) (by rfl)) (lex_4_169_prefix s) (positive_select s 169) (lex_4_169_image s)

theorem lex_4_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.pos 169), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation4 169 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3074) (Sat.Literal.pos 169) (Sat.Literal.pos 153) (lex_4_169_prefix s) (positive_select s 169) (lex_4_169_image s)

theorem lex_4_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.pos 3074)] :=
  (lex_4_169_gate s).prop _ (List.Mem.head _)

theorem lex_4_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.neg 169), (Sat.Literal.pos 153)] :=
  (lex_4_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.pos 169), (Sat.Literal.neg 153)] :=
  (lex_4_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.neg 169), (Sat.Literal.neg 153), (Sat.Literal.pos 3075)] :=
  (lex_4_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3074), (Sat.Literal.pos 169), (Sat.Literal.pos 153), (Sat.Literal.pos 3075)] :=
  (lex_4_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3075) = lexBefore s permutation4 168 := by
  exact (positive_lex_of_descriptor s 3075 permutation4 169 (by rfl)).trans ((lex_skipped s permutation4 168 169 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation4 168) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation4 168 by rw [image4_eq]; rfl))

theorem lex_4_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3076) (Sat.Literal.pos 3075) (Sat.Literal.pos 168) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation4 168 (assignment s)
    (Sat.Literal.pos 3076) (Sat.Literal.pos 3075) (Sat.Literal.pos 168) (Sat.Literal.pos 152) (positive_of_descriptor s 3076 (.lex permutation4 168) (by rfl)) (lex_4_168_prefix s) (positive_select s 168) (lex_4_168_image s)

theorem lex_4_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.pos 168), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation4 168 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3075) (Sat.Literal.pos 168) (Sat.Literal.pos 152) (lex_4_168_prefix s) (positive_select s 168) (lex_4_168_image s)

theorem lex_4_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.pos 3075)] :=
  (lex_4_168_gate s).prop _ (List.Mem.head _)

theorem lex_4_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.neg 168), (Sat.Literal.pos 152)] :=
  (lex_4_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.pos 168), (Sat.Literal.neg 152)] :=
  (lex_4_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.neg 168), (Sat.Literal.neg 152), (Sat.Literal.pos 3076)] :=
  (lex_4_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3075), (Sat.Literal.pos 168), (Sat.Literal.pos 152), (Sat.Literal.pos 3076)] :=
  (lex_4_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3076) = lexBefore s permutation4 167 := by
  exact (positive_lex_of_descriptor s 3076 permutation4 168 (by rfl)).trans ((lex_skipped s permutation4 167 168 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation4 167) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation4 167 by rw [image4_eq]; rfl))

theorem lex_4_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3077) (Sat.Literal.pos 3076) (Sat.Literal.pos 167) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation4 167 (assignment s)
    (Sat.Literal.pos 3077) (Sat.Literal.pos 3076) (Sat.Literal.pos 167) (Sat.Literal.pos 151) (positive_of_descriptor s 3077 (.lex permutation4 167) (by rfl)) (lex_4_167_prefix s) (positive_select s 167) (lex_4_167_image s)

theorem lex_4_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.pos 167), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation4 167 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3076) (Sat.Literal.pos 167) (Sat.Literal.pos 151) (lex_4_167_prefix s) (positive_select s 167) (lex_4_167_image s)

theorem lex_4_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.pos 3076)] :=
  (lex_4_167_gate s).prop _ (List.Mem.head _)

theorem lex_4_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.neg 167), (Sat.Literal.pos 151)] :=
  (lex_4_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.pos 167), (Sat.Literal.neg 151)] :=
  (lex_4_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.neg 167), (Sat.Literal.neg 151), (Sat.Literal.pos 3077)] :=
  (lex_4_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3076), (Sat.Literal.pos 167), (Sat.Literal.pos 151), (Sat.Literal.pos 3077)] :=
  (lex_4_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3077) = lexBefore s permutation4 166 := by
  exact (positive_lex_of_descriptor s 3077 permutation4 167 (by rfl)).trans ((lex_skipped s permutation4 166 167 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation4 166) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation4 166 by rw [image4_eq]; rfl))

theorem lex_4_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3078) (Sat.Literal.pos 3077) (Sat.Literal.pos 166) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation4 166 (assignment s)
    (Sat.Literal.pos 3078) (Sat.Literal.pos 3077) (Sat.Literal.pos 166) (Sat.Literal.pos 150) (positive_of_descriptor s 3078 (.lex permutation4 166) (by rfl)) (lex_4_166_prefix s) (positive_select s 166) (lex_4_166_image s)

theorem lex_4_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.pos 166), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation4 166 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3077) (Sat.Literal.pos 166) (Sat.Literal.pos 150) (lex_4_166_prefix s) (positive_select s 166) (lex_4_166_image s)

theorem lex_4_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.pos 3077)] :=
  (lex_4_166_gate s).prop _ (List.Mem.head _)

theorem lex_4_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.neg 166), (Sat.Literal.pos 150)] :=
  (lex_4_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.pos 166), (Sat.Literal.neg 150)] :=
  (lex_4_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.neg 166), (Sat.Literal.neg 150), (Sat.Literal.pos 3078)] :=
  (lex_4_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3077), (Sat.Literal.pos 166), (Sat.Literal.pos 150), (Sat.Literal.pos 3078)] :=
  (lex_4_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3078) = lexBefore s permutation4 165 := by
  exact (positive_lex_of_descriptor s 3078 permutation4 166 (by rfl)).trans ((lex_skipped s permutation4 165 166 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation4 165) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation4 165 by rw [image4_eq]; rfl))

theorem lex_4_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3079) (Sat.Literal.pos 3078) (Sat.Literal.pos 165) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation4 165 (assignment s)
    (Sat.Literal.pos 3079) (Sat.Literal.pos 3078) (Sat.Literal.pos 165) (Sat.Literal.pos 149) (positive_of_descriptor s 3079 (.lex permutation4 165) (by rfl)) (lex_4_165_prefix s) (positive_select s 165) (lex_4_165_image s)

theorem lex_4_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.pos 165), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation4 165 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3078) (Sat.Literal.pos 165) (Sat.Literal.pos 149) (lex_4_165_prefix s) (positive_select s 165) (lex_4_165_image s)

theorem lex_4_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.pos 3078)] :=
  (lex_4_165_gate s).prop _ (List.Mem.head _)

theorem lex_4_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.neg 165), (Sat.Literal.pos 149)] :=
  (lex_4_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.pos 165), (Sat.Literal.neg 149)] :=
  (lex_4_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.neg 165), (Sat.Literal.neg 149), (Sat.Literal.pos 3079)] :=
  (lex_4_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3078), (Sat.Literal.pos 165), (Sat.Literal.pos 149), (Sat.Literal.pos 3079)] :=
  (lex_4_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3079) = lexBefore s permutation4 164 := by
  exact (positive_lex_of_descriptor s 3079 permutation4 165 (by rfl)).trans ((lex_skipped s permutation4 164 165 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation4 164) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation4 164 by rw [image4_eq]; rfl))

theorem lex_4_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3080) (Sat.Literal.pos 3079) (Sat.Literal.pos 164) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation4 164 (assignment s)
    (Sat.Literal.pos 3080) (Sat.Literal.pos 3079) (Sat.Literal.pos 164) (Sat.Literal.pos 148) (positive_of_descriptor s 3080 (.lex permutation4 164) (by rfl)) (lex_4_164_prefix s) (positive_select s 164) (lex_4_164_image s)

theorem lex_4_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.pos 164), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation4 164 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3079) (Sat.Literal.pos 164) (Sat.Literal.pos 148) (lex_4_164_prefix s) (positive_select s 164) (lex_4_164_image s)

theorem lex_4_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.pos 3079)] :=
  (lex_4_164_gate s).prop _ (List.Mem.head _)

theorem lex_4_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.neg 164), (Sat.Literal.pos 148)] :=
  (lex_4_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.pos 164), (Sat.Literal.neg 148)] :=
  (lex_4_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.neg 164), (Sat.Literal.neg 148), (Sat.Literal.pos 3080)] :=
  (lex_4_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3079), (Sat.Literal.pos 164), (Sat.Literal.pos 148), (Sat.Literal.pos 3080)] :=
  (lex_4_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3080) = lexBefore s permutation4 163 := by
  exact (positive_lex_of_descriptor s 3080 permutation4 164 (by rfl)).trans ((lex_skipped s permutation4 163 164 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation4 163) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation4 163 by rw [image4_eq]; rfl))

theorem lex_4_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3081) (Sat.Literal.pos 3080) (Sat.Literal.pos 163) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation4 163 (assignment s)
    (Sat.Literal.pos 3081) (Sat.Literal.pos 3080) (Sat.Literal.pos 163) (Sat.Literal.pos 147) (positive_of_descriptor s 3081 (.lex permutation4 163) (by rfl)) (lex_4_163_prefix s) (positive_select s 163) (lex_4_163_image s)

theorem lex_4_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.pos 163), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation4 163 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3080) (Sat.Literal.pos 163) (Sat.Literal.pos 147) (lex_4_163_prefix s) (positive_select s 163) (lex_4_163_image s)

theorem lex_4_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.pos 3080)] :=
  (lex_4_163_gate s).prop _ (List.Mem.head _)

theorem lex_4_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.neg 163), (Sat.Literal.pos 147)] :=
  (lex_4_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.pos 163), (Sat.Literal.neg 147)] :=
  (lex_4_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.neg 163), (Sat.Literal.neg 147), (Sat.Literal.pos 3081)] :=
  (lex_4_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3080), (Sat.Literal.pos 163), (Sat.Literal.pos 147), (Sat.Literal.pos 3081)] :=
  (lex_4_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3081) = lexBefore s permutation4 162 := by
  exact (positive_lex_of_descriptor s 3081 permutation4 163 (by rfl)).trans ((lex_skipped s permutation4 162 163 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation4 162) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation4 162 by rw [image4_eq]; rfl))

theorem lex_4_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3082) (Sat.Literal.pos 3081) (Sat.Literal.pos 162) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation4 162 (assignment s)
    (Sat.Literal.pos 3082) (Sat.Literal.pos 3081) (Sat.Literal.pos 162) (Sat.Literal.pos 146) (positive_of_descriptor s 3082 (.lex permutation4 162) (by rfl)) (lex_4_162_prefix s) (positive_select s 162) (lex_4_162_image s)

theorem lex_4_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.pos 162), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation4 162 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3081) (Sat.Literal.pos 162) (Sat.Literal.pos 146) (lex_4_162_prefix s) (positive_select s 162) (lex_4_162_image s)

theorem lex_4_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.pos 3081)] :=
  (lex_4_162_gate s).prop _ (List.Mem.head _)

theorem lex_4_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.neg 162), (Sat.Literal.pos 146)] :=
  (lex_4_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.pos 162), (Sat.Literal.neg 146)] :=
  (lex_4_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.neg 162), (Sat.Literal.neg 146), (Sat.Literal.pos 3082)] :=
  (lex_4_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3081), (Sat.Literal.pos 162), (Sat.Literal.pos 146), (Sat.Literal.pos 3082)] :=
  (lex_4_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3082) = lexBefore s permutation4 161 := by
  exact (positive_lex_of_descriptor s 3082 permutation4 162 (by rfl)).trans ((lex_skipped s permutation4 161 162 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation4 161) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation4 161 by rw [image4_eq]; rfl))

theorem lex_4_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3083) (Sat.Literal.pos 3082) (Sat.Literal.pos 161) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation4 161 (assignment s)
    (Sat.Literal.pos 3083) (Sat.Literal.pos 3082) (Sat.Literal.pos 161) (Sat.Literal.pos 145) (positive_of_descriptor s 3083 (.lex permutation4 161) (by rfl)) (lex_4_161_prefix s) (positive_select s 161) (lex_4_161_image s)

theorem lex_4_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.pos 161), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation4 161 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3082) (Sat.Literal.pos 161) (Sat.Literal.pos 145) (lex_4_161_prefix s) (positive_select s 161) (lex_4_161_image s)

theorem lex_4_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.pos 3082)] :=
  (lex_4_161_gate s).prop _ (List.Mem.head _)

theorem lex_4_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.neg 161), (Sat.Literal.pos 145)] :=
  (lex_4_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.pos 161), (Sat.Literal.neg 145)] :=
  (lex_4_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.neg 161), (Sat.Literal.neg 145), (Sat.Literal.pos 3083)] :=
  (lex_4_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3082), (Sat.Literal.pos 161), (Sat.Literal.pos 145), (Sat.Literal.pos 3083)] :=
  (lex_4_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3083) = lexBefore s permutation4 160 := by
  exact (positive_lex_of_descriptor s 3083 permutation4 161 (by rfl)).trans ((lex_skipped s permutation4 160 161 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation4 160) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation4 160 by rw [image4_eq]; rfl))

theorem lex_4_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3084) (Sat.Literal.pos 3083) (Sat.Literal.pos 160) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation4 160 (assignment s)
    (Sat.Literal.pos 3084) (Sat.Literal.pos 3083) (Sat.Literal.pos 160) (Sat.Literal.pos 144) (positive_of_descriptor s 3084 (.lex permutation4 160) (by rfl)) (lex_4_160_prefix s) (positive_select s 160) (lex_4_160_image s)

theorem lex_4_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.pos 160), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation4 160 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3083) (Sat.Literal.pos 160) (Sat.Literal.pos 144) (lex_4_160_prefix s) (positive_select s 160) (lex_4_160_image s)

theorem lex_4_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.pos 3083)] :=
  (lex_4_160_gate s).prop _ (List.Mem.head _)

theorem lex_4_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.neg 160), (Sat.Literal.pos 144)] :=
  (lex_4_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.pos 160), (Sat.Literal.neg 144)] :=
  (lex_4_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.neg 160), (Sat.Literal.neg 144), (Sat.Literal.pos 3084)] :=
  (lex_4_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3083), (Sat.Literal.pos 160), (Sat.Literal.pos 144), (Sat.Literal.pos 3084)] :=
  (lex_4_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3084) = lexBefore s permutation4 159 := by
  exact (positive_lex_of_descriptor s 3084 permutation4 160 (by rfl)).trans ((lex_skipped s permutation4 159 160 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation4 159) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation4 159 by rw [image4_eq]; rfl))

theorem lex_4_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3085) (Sat.Literal.pos 3084) (Sat.Literal.pos 159) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation4 159 (assignment s)
    (Sat.Literal.pos 3085) (Sat.Literal.pos 3084) (Sat.Literal.pos 159) (Sat.Literal.pos 175) (positive_of_descriptor s 3085 (.lex permutation4 159) (by rfl)) (lex_4_159_prefix s) (positive_select s 159) (lex_4_159_image s)

theorem lex_4_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.pos 159), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation4 159 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3084) (Sat.Literal.pos 159) (Sat.Literal.pos 175) (lex_4_159_prefix s) (positive_select s 159) (lex_4_159_image s)

theorem lex_4_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.pos 3084)] :=
  (lex_4_159_gate s).prop _ (List.Mem.head _)

theorem lex_4_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.neg 159), (Sat.Literal.pos 175)] :=
  (lex_4_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.pos 159), (Sat.Literal.neg 175)] :=
  (lex_4_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.neg 159), (Sat.Literal.neg 175), (Sat.Literal.pos 3085)] :=
  (lex_4_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3084), (Sat.Literal.pos 159), (Sat.Literal.pos 175), (Sat.Literal.pos 3085)] :=
  (lex_4_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3085) = lexBefore s permutation4 158 := by
  exact (positive_lex_of_descriptor s 3085 permutation4 159 (by rfl)).trans ((lex_skipped s permutation4 158 159 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation4 158) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation4 158 by rw [image4_eq]; rfl))

theorem lex_4_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3086) (Sat.Literal.pos 3085) (Sat.Literal.pos 158) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation4 158 (assignment s)
    (Sat.Literal.pos 3086) (Sat.Literal.pos 3085) (Sat.Literal.pos 158) (Sat.Literal.pos 174) (positive_of_descriptor s 3086 (.lex permutation4 158) (by rfl)) (lex_4_158_prefix s) (positive_select s 158) (lex_4_158_image s)

theorem lex_4_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.pos 158), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation4 158 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3085) (Sat.Literal.pos 158) (Sat.Literal.pos 174) (lex_4_158_prefix s) (positive_select s 158) (lex_4_158_image s)

theorem lex_4_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.pos 3085)] :=
  (lex_4_158_gate s).prop _ (List.Mem.head _)

theorem lex_4_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.neg 158), (Sat.Literal.pos 174)] :=
  (lex_4_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.pos 158), (Sat.Literal.neg 174)] :=
  (lex_4_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.neg 158), (Sat.Literal.neg 174), (Sat.Literal.pos 3086)] :=
  (lex_4_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3085), (Sat.Literal.pos 158), (Sat.Literal.pos 174), (Sat.Literal.pos 3086)] :=
  (lex_4_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3086) = lexBefore s permutation4 157 := by
  exact (positive_lex_of_descriptor s 3086 permutation4 158 (by rfl)).trans ((lex_skipped s permutation4 157 158 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation4 157) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation4 157 by rw [image4_eq]; rfl))

theorem lex_4_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3087) (Sat.Literal.pos 3086) (Sat.Literal.pos 157) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation4 157 (assignment s)
    (Sat.Literal.pos 3087) (Sat.Literal.pos 3086) (Sat.Literal.pos 157) (Sat.Literal.pos 173) (positive_of_descriptor s 3087 (.lex permutation4 157) (by rfl)) (lex_4_157_prefix s) (positive_select s 157) (lex_4_157_image s)

theorem lex_4_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.pos 157), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation4 157 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3086) (Sat.Literal.pos 157) (Sat.Literal.pos 173) (lex_4_157_prefix s) (positive_select s 157) (lex_4_157_image s)

theorem lex_4_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.pos 3086)] :=
  (lex_4_157_gate s).prop _ (List.Mem.head _)

theorem lex_4_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.neg 157), (Sat.Literal.pos 173)] :=
  (lex_4_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.pos 157), (Sat.Literal.neg 173)] :=
  (lex_4_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.neg 157), (Sat.Literal.neg 173), (Sat.Literal.pos 3087)] :=
  (lex_4_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3086), (Sat.Literal.pos 157), (Sat.Literal.pos 173), (Sat.Literal.pos 3087)] :=
  (lex_4_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3087) = lexBefore s permutation4 156 := by
  exact (positive_lex_of_descriptor s 3087 permutation4 157 (by rfl)).trans ((lex_skipped s permutation4 156 157 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation4 156) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation4 156 by rw [image4_eq]; rfl))

theorem lex_4_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3088) (Sat.Literal.pos 3087) (Sat.Literal.pos 156) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation4 156 (assignment s)
    (Sat.Literal.pos 3088) (Sat.Literal.pos 3087) (Sat.Literal.pos 156) (Sat.Literal.pos 172) (positive_of_descriptor s 3088 (.lex permutation4 156) (by rfl)) (lex_4_156_prefix s) (positive_select s 156) (lex_4_156_image s)

theorem lex_4_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.pos 156), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation4 156 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3087) (Sat.Literal.pos 156) (Sat.Literal.pos 172) (lex_4_156_prefix s) (positive_select s 156) (lex_4_156_image s)

theorem lex_4_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.pos 3087)] :=
  (lex_4_156_gate s).prop _ (List.Mem.head _)

theorem lex_4_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.neg 156), (Sat.Literal.pos 172)] :=
  (lex_4_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.pos 156), (Sat.Literal.neg 172)] :=
  (lex_4_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.neg 156), (Sat.Literal.neg 172), (Sat.Literal.pos 3088)] :=
  (lex_4_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3087), (Sat.Literal.pos 156), (Sat.Literal.pos 172), (Sat.Literal.pos 3088)] :=
  (lex_4_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3088) = lexBefore s permutation4 155 := by
  exact (positive_lex_of_descriptor s 3088 permutation4 156 (by rfl)).trans ((lex_skipped s permutation4 155 156 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation4 155) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation4 155 by rw [image4_eq]; rfl))

theorem lex_4_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3089) (Sat.Literal.pos 3088) (Sat.Literal.pos 155) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation4 155 (assignment s)
    (Sat.Literal.pos 3089) (Sat.Literal.pos 3088) (Sat.Literal.pos 155) (Sat.Literal.pos 171) (positive_of_descriptor s 3089 (.lex permutation4 155) (by rfl)) (lex_4_155_prefix s) (positive_select s 155) (lex_4_155_image s)

theorem lex_4_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.pos 155), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation4 155 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3088) (Sat.Literal.pos 155) (Sat.Literal.pos 171) (lex_4_155_prefix s) (positive_select s 155) (lex_4_155_image s)

theorem lex_4_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.pos 3088)] :=
  (lex_4_155_gate s).prop _ (List.Mem.head _)

theorem lex_4_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.neg 155), (Sat.Literal.pos 171)] :=
  (lex_4_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.pos 155), (Sat.Literal.neg 171)] :=
  (lex_4_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.neg 155), (Sat.Literal.neg 171), (Sat.Literal.pos 3089)] :=
  (lex_4_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3088), (Sat.Literal.pos 155), (Sat.Literal.pos 171), (Sat.Literal.pos 3089)] :=
  (lex_4_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3089) = lexBefore s permutation4 154 := by
  exact (positive_lex_of_descriptor s 3089 permutation4 155 (by rfl)).trans ((lex_skipped s permutation4 154 155 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation4 154) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation4 154 by rw [image4_eq]; rfl))

theorem lex_4_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3090) (Sat.Literal.pos 3089) (Sat.Literal.pos 154) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation4 154 (assignment s)
    (Sat.Literal.pos 3090) (Sat.Literal.pos 3089) (Sat.Literal.pos 154) (Sat.Literal.pos 170) (positive_of_descriptor s 3090 (.lex permutation4 154) (by rfl)) (lex_4_154_prefix s) (positive_select s 154) (lex_4_154_image s)

theorem lex_4_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.pos 154), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation4 154 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3089) (Sat.Literal.pos 154) (Sat.Literal.pos 170) (lex_4_154_prefix s) (positive_select s 154) (lex_4_154_image s)

theorem lex_4_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.pos 3089)] :=
  (lex_4_154_gate s).prop _ (List.Mem.head _)

theorem lex_4_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.neg 154), (Sat.Literal.pos 170)] :=
  (lex_4_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.pos 154), (Sat.Literal.neg 170)] :=
  (lex_4_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.neg 154), (Sat.Literal.neg 170), (Sat.Literal.pos 3090)] :=
  (lex_4_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3089), (Sat.Literal.pos 154), (Sat.Literal.pos 170), (Sat.Literal.pos 3090)] :=
  (lex_4_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3090) = lexBefore s permutation4 153 := by
  exact (positive_lex_of_descriptor s 3090 permutation4 154 (by rfl)).trans ((lex_skipped s permutation4 153 154 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation4 153) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation4 153 by rw [image4_eq]; rfl))

theorem lex_4_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3091) (Sat.Literal.pos 3090) (Sat.Literal.pos 153) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation4 153 (assignment s)
    (Sat.Literal.pos 3091) (Sat.Literal.pos 3090) (Sat.Literal.pos 153) (Sat.Literal.pos 169) (positive_of_descriptor s 3091 (.lex permutation4 153) (by rfl)) (lex_4_153_prefix s) (positive_select s 153) (lex_4_153_image s)

theorem lex_4_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.pos 153), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation4 153 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3090) (Sat.Literal.pos 153) (Sat.Literal.pos 169) (lex_4_153_prefix s) (positive_select s 153) (lex_4_153_image s)

theorem lex_4_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.pos 3090)] :=
  (lex_4_153_gate s).prop _ (List.Mem.head _)

theorem lex_4_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.neg 153), (Sat.Literal.pos 169)] :=
  (lex_4_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.pos 153), (Sat.Literal.neg 169)] :=
  (lex_4_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.neg 153), (Sat.Literal.neg 169), (Sat.Literal.pos 3091)] :=
  (lex_4_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3090), (Sat.Literal.pos 153), (Sat.Literal.pos 169), (Sat.Literal.pos 3091)] :=
  (lex_4_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3091) = lexBefore s permutation4 152 := by
  exact (positive_lex_of_descriptor s 3091 permutation4 153 (by rfl)).trans ((lex_skipped s permutation4 152 153 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation4 152) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation4 152 by rw [image4_eq]; rfl))

theorem lex_4_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3092) (Sat.Literal.pos 3091) (Sat.Literal.pos 152) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation4 152 (assignment s)
    (Sat.Literal.pos 3092) (Sat.Literal.pos 3091) (Sat.Literal.pos 152) (Sat.Literal.pos 168) (positive_of_descriptor s 3092 (.lex permutation4 152) (by rfl)) (lex_4_152_prefix s) (positive_select s 152) (lex_4_152_image s)

theorem lex_4_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.pos 152), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation4 152 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3091) (Sat.Literal.pos 152) (Sat.Literal.pos 168) (lex_4_152_prefix s) (positive_select s 152) (lex_4_152_image s)

theorem lex_4_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.pos 3091)] :=
  (lex_4_152_gate s).prop _ (List.Mem.head _)

theorem lex_4_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.neg 152), (Sat.Literal.pos 168)] :=
  (lex_4_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.pos 152), (Sat.Literal.neg 168)] :=
  (lex_4_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.neg 152), (Sat.Literal.neg 168), (Sat.Literal.pos 3092)] :=
  (lex_4_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3091), (Sat.Literal.pos 152), (Sat.Literal.pos 168), (Sat.Literal.pos 3092)] :=
  (lex_4_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3092) = lexBefore s permutation4 151 := by
  exact (positive_lex_of_descriptor s 3092 permutation4 152 (by rfl)).trans ((lex_skipped s permutation4 151 152 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation4 151) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation4 151 by rw [image4_eq]; rfl))

theorem lex_4_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3093) (Sat.Literal.pos 3092) (Sat.Literal.pos 151) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation4 151 (assignment s)
    (Sat.Literal.pos 3093) (Sat.Literal.pos 3092) (Sat.Literal.pos 151) (Sat.Literal.pos 167) (positive_of_descriptor s 3093 (.lex permutation4 151) (by rfl)) (lex_4_151_prefix s) (positive_select s 151) (lex_4_151_image s)

theorem lex_4_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.pos 151), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation4 151 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3092) (Sat.Literal.pos 151) (Sat.Literal.pos 167) (lex_4_151_prefix s) (positive_select s 151) (lex_4_151_image s)

theorem lex_4_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.pos 3092)] :=
  (lex_4_151_gate s).prop _ (List.Mem.head _)

theorem lex_4_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.neg 151), (Sat.Literal.pos 167)] :=
  (lex_4_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.pos 151), (Sat.Literal.neg 167)] :=
  (lex_4_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.neg 151), (Sat.Literal.neg 167), (Sat.Literal.pos 3093)] :=
  (lex_4_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3092), (Sat.Literal.pos 151), (Sat.Literal.pos 167), (Sat.Literal.pos 3093)] :=
  (lex_4_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3093) = lexBefore s permutation4 150 := by
  exact (positive_lex_of_descriptor s 3093 permutation4 151 (by rfl)).trans ((lex_skipped s permutation4 150 151 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation4 150) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation4 150 by rw [image4_eq]; rfl))

theorem lex_4_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3094) (Sat.Literal.pos 3093) (Sat.Literal.pos 150) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation4 150 (assignment s)
    (Sat.Literal.pos 3094) (Sat.Literal.pos 3093) (Sat.Literal.pos 150) (Sat.Literal.pos 166) (positive_of_descriptor s 3094 (.lex permutation4 150) (by rfl)) (lex_4_150_prefix s) (positive_select s 150) (lex_4_150_image s)

theorem lex_4_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.pos 150), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation4 150 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3093) (Sat.Literal.pos 150) (Sat.Literal.pos 166) (lex_4_150_prefix s) (positive_select s 150) (lex_4_150_image s)

theorem lex_4_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.pos 3093)] :=
  (lex_4_150_gate s).prop _ (List.Mem.head _)

theorem lex_4_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.neg 150), (Sat.Literal.pos 166)] :=
  (lex_4_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.pos 150), (Sat.Literal.neg 166)] :=
  (lex_4_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.neg 150), (Sat.Literal.neg 166), (Sat.Literal.pos 3094)] :=
  (lex_4_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3093), (Sat.Literal.pos 150), (Sat.Literal.pos 166), (Sat.Literal.pos 3094)] :=
  (lex_4_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3094) = lexBefore s permutation4 149 := by
  exact (positive_lex_of_descriptor s 3094 permutation4 150 (by rfl)).trans ((lex_skipped s permutation4 149 150 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation4 149) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation4 149 by rw [image4_eq]; rfl))

theorem lex_4_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3095) (Sat.Literal.pos 3094) (Sat.Literal.pos 149) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation4 149 (assignment s)
    (Sat.Literal.pos 3095) (Sat.Literal.pos 3094) (Sat.Literal.pos 149) (Sat.Literal.pos 165) (positive_of_descriptor s 3095 (.lex permutation4 149) (by rfl)) (lex_4_149_prefix s) (positive_select s 149) (lex_4_149_image s)

theorem lex_4_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.pos 149), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation4 149 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3094) (Sat.Literal.pos 149) (Sat.Literal.pos 165) (lex_4_149_prefix s) (positive_select s 149) (lex_4_149_image s)

theorem lex_4_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.pos 3094)] :=
  (lex_4_149_gate s).prop _ (List.Mem.head _)

theorem lex_4_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.neg 149), (Sat.Literal.pos 165)] :=
  (lex_4_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.pos 149), (Sat.Literal.neg 165)] :=
  (lex_4_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.neg 149), (Sat.Literal.neg 165), (Sat.Literal.pos 3095)] :=
  (lex_4_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3094), (Sat.Literal.pos 149), (Sat.Literal.pos 165), (Sat.Literal.pos 3095)] :=
  (lex_4_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3095) = lexBefore s permutation4 148 := by
  exact (positive_lex_of_descriptor s 3095 permutation4 149 (by rfl)).trans ((lex_skipped s permutation4 148 149 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation4 148) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation4 148 by rw [image4_eq]; rfl))

theorem lex_4_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3096) (Sat.Literal.pos 3095) (Sat.Literal.pos 148) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation4 148 (assignment s)
    (Sat.Literal.pos 3096) (Sat.Literal.pos 3095) (Sat.Literal.pos 148) (Sat.Literal.pos 164) (positive_of_descriptor s 3096 (.lex permutation4 148) (by rfl)) (lex_4_148_prefix s) (positive_select s 148) (lex_4_148_image s)

theorem lex_4_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.pos 148), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation4 148 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3095) (Sat.Literal.pos 148) (Sat.Literal.pos 164) (lex_4_148_prefix s) (positive_select s 148) (lex_4_148_image s)

theorem lex_4_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.pos 3095)] :=
  (lex_4_148_gate s).prop _ (List.Mem.head _)

theorem lex_4_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.neg 148), (Sat.Literal.pos 164)] :=
  (lex_4_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.pos 148), (Sat.Literal.neg 164)] :=
  (lex_4_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.neg 148), (Sat.Literal.neg 164), (Sat.Literal.pos 3096)] :=
  (lex_4_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3095), (Sat.Literal.pos 148), (Sat.Literal.pos 164), (Sat.Literal.pos 3096)] :=
  (lex_4_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3096) = lexBefore s permutation4 147 := by
  exact (positive_lex_of_descriptor s 3096 permutation4 148 (by rfl)).trans ((lex_skipped s permutation4 147 148 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation4 147) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation4 147 by rw [image4_eq]; rfl))

theorem lex_4_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3097) (Sat.Literal.pos 3096) (Sat.Literal.pos 147) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation4 147 (assignment s)
    (Sat.Literal.pos 3097) (Sat.Literal.pos 3096) (Sat.Literal.pos 147) (Sat.Literal.pos 163) (positive_of_descriptor s 3097 (.lex permutation4 147) (by rfl)) (lex_4_147_prefix s) (positive_select s 147) (lex_4_147_image s)

theorem lex_4_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.pos 147), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation4 147 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3096) (Sat.Literal.pos 147) (Sat.Literal.pos 163) (lex_4_147_prefix s) (positive_select s 147) (lex_4_147_image s)

theorem lex_4_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.pos 3096)] :=
  (lex_4_147_gate s).prop _ (List.Mem.head _)

theorem lex_4_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.neg 147), (Sat.Literal.pos 163)] :=
  (lex_4_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.pos 147), (Sat.Literal.neg 163)] :=
  (lex_4_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.neg 147), (Sat.Literal.neg 163), (Sat.Literal.pos 3097)] :=
  (lex_4_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3096), (Sat.Literal.pos 147), (Sat.Literal.pos 163), (Sat.Literal.pos 3097)] :=
  (lex_4_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3097) = lexBefore s permutation4 146 := by
  exact (positive_lex_of_descriptor s 3097 permutation4 147 (by rfl)).trans ((lex_skipped s permutation4 146 147 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation4 146) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation4 146 by rw [image4_eq]; rfl))

theorem lex_4_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3098) (Sat.Literal.pos 3097) (Sat.Literal.pos 146) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation4 146 (assignment s)
    (Sat.Literal.pos 3098) (Sat.Literal.pos 3097) (Sat.Literal.pos 146) (Sat.Literal.pos 162) (positive_of_descriptor s 3098 (.lex permutation4 146) (by rfl)) (lex_4_146_prefix s) (positive_select s 146) (lex_4_146_image s)

theorem lex_4_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.pos 146), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation4 146 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3097) (Sat.Literal.pos 146) (Sat.Literal.pos 162) (lex_4_146_prefix s) (positive_select s 146) (lex_4_146_image s)

theorem lex_4_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.pos 3097)] :=
  (lex_4_146_gate s).prop _ (List.Mem.head _)

theorem lex_4_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.neg 146), (Sat.Literal.pos 162)] :=
  (lex_4_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.pos 146), (Sat.Literal.neg 162)] :=
  (lex_4_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.neg 146), (Sat.Literal.neg 162), (Sat.Literal.pos 3098)] :=
  (lex_4_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3097), (Sat.Literal.pos 146), (Sat.Literal.pos 162), (Sat.Literal.pos 3098)] :=
  (lex_4_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3098) = lexBefore s permutation4 145 := by
  exact (positive_lex_of_descriptor s 3098 permutation4 146 (by rfl)).trans ((lex_skipped s permutation4 145 146 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation4 145) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation4 145 by rw [image4_eq]; rfl))

theorem lex_4_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3099) (Sat.Literal.pos 3098) (Sat.Literal.pos 145) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation4 145 (assignment s)
    (Sat.Literal.pos 3099) (Sat.Literal.pos 3098) (Sat.Literal.pos 145) (Sat.Literal.pos 161) (positive_of_descriptor s 3099 (.lex permutation4 145) (by rfl)) (lex_4_145_prefix s) (positive_select s 145) (lex_4_145_image s)

theorem lex_4_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.pos 145), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation4 145 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3098) (Sat.Literal.pos 145) (Sat.Literal.pos 161) (lex_4_145_prefix s) (positive_select s 145) (lex_4_145_image s)

theorem lex_4_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.pos 3098)] :=
  (lex_4_145_gate s).prop _ (List.Mem.head _)

theorem lex_4_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.neg 145), (Sat.Literal.pos 161)] :=
  (lex_4_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.pos 145), (Sat.Literal.neg 161)] :=
  (lex_4_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.neg 145), (Sat.Literal.neg 161), (Sat.Literal.pos 3099)] :=
  (lex_4_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3098), (Sat.Literal.pos 145), (Sat.Literal.pos 161), (Sat.Literal.pos 3099)] :=
  (lex_4_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3099) = lexBefore s permutation4 144 := by
  exact (positive_lex_of_descriptor s 3099 permutation4 145 (by rfl)).trans ((lex_skipped s permutation4 144 145 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation4 144) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation4 144 by rw [image4_eq]; rfl))

theorem lex_4_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3100) (Sat.Literal.pos 3099) (Sat.Literal.pos 144) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation4 144 (assignment s)
    (Sat.Literal.pos 3100) (Sat.Literal.pos 3099) (Sat.Literal.pos 144) (Sat.Literal.pos 160) (positive_of_descriptor s 3100 (.lex permutation4 144) (by rfl)) (lex_4_144_prefix s) (positive_select s 144) (lex_4_144_image s)

theorem lex_4_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.pos 144), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation4 144 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3099) (Sat.Literal.pos 144) (Sat.Literal.pos 160) (lex_4_144_prefix s) (positive_select s 144) (lex_4_144_image s)

theorem lex_4_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.pos 3099)] :=
  (lex_4_144_gate s).prop _ (List.Mem.head _)

theorem lex_4_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.neg 144), (Sat.Literal.pos 160)] :=
  (lex_4_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.pos 144), (Sat.Literal.neg 160)] :=
  (lex_4_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.neg 144), (Sat.Literal.neg 160), (Sat.Literal.pos 3100)] :=
  (lex_4_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3099), (Sat.Literal.pos 144), (Sat.Literal.pos 160), (Sat.Literal.pos 3100)] :=
  (lex_4_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3100) = lexBefore s permutation4 111 := by
  exact (positive_lex_of_descriptor s 3100 permutation4 144 (by rfl)).trans ((lex_skipped s permutation4 111 144 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 112 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation4 111) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation4 111 by rw [image4_eq]; rfl))

theorem lex_4_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3101) (Sat.Literal.pos 3100) (Sat.Literal.pos 111) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation4 111 (assignment s)
    (Sat.Literal.pos 3101) (Sat.Literal.pos 3100) (Sat.Literal.pos 111) (Sat.Literal.pos 95) (positive_of_descriptor s 3101 (.lex permutation4 111) (by rfl)) (lex_4_111_prefix s) (positive_select s 111) (lex_4_111_image s)

theorem lex_4_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.pos 111), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation4 111 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3100) (Sat.Literal.pos 111) (Sat.Literal.pos 95) (lex_4_111_prefix s) (positive_select s 111) (lex_4_111_image s)

theorem lex_4_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.pos 3100)] :=
  (lex_4_111_gate s).prop _ (List.Mem.head _)

theorem lex_4_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.neg 111), (Sat.Literal.pos 95)] :=
  (lex_4_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.pos 111), (Sat.Literal.neg 95)] :=
  (lex_4_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.neg 111), (Sat.Literal.neg 95), (Sat.Literal.pos 3101)] :=
  (lex_4_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3100), (Sat.Literal.pos 111), (Sat.Literal.pos 95), (Sat.Literal.pos 3101)] :=
  (lex_4_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3101) = lexBefore s permutation4 110 := by
  exact (positive_lex_of_descriptor s 3101 permutation4 111 (by rfl)).trans ((lex_skipped s permutation4 110 111 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation4 110) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation4 110 by rw [image4_eq]; rfl))

theorem lex_4_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3102) (Sat.Literal.pos 3101) (Sat.Literal.pos 110) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation4 110 (assignment s)
    (Sat.Literal.pos 3102) (Sat.Literal.pos 3101) (Sat.Literal.pos 110) (Sat.Literal.pos 94) (positive_of_descriptor s 3102 (.lex permutation4 110) (by rfl)) (lex_4_110_prefix s) (positive_select s 110) (lex_4_110_image s)

theorem lex_4_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.pos 110), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation4 110 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3101) (Sat.Literal.pos 110) (Sat.Literal.pos 94) (lex_4_110_prefix s) (positive_select s 110) (lex_4_110_image s)

theorem lex_4_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.pos 3101)] :=
  (lex_4_110_gate s).prop _ (List.Mem.head _)

theorem lex_4_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.neg 110), (Sat.Literal.pos 94)] :=
  (lex_4_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.pos 110), (Sat.Literal.neg 94)] :=
  (lex_4_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.neg 110), (Sat.Literal.neg 94), (Sat.Literal.pos 3102)] :=
  (lex_4_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3101), (Sat.Literal.pos 110), (Sat.Literal.pos 94), (Sat.Literal.pos 3102)] :=
  (lex_4_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3102) = lexBefore s permutation4 109 := by
  exact (positive_lex_of_descriptor s 3102 permutation4 110 (by rfl)).trans ((lex_skipped s permutation4 109 110 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation4 109) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation4 109 by rw [image4_eq]; rfl))

theorem lex_4_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3103) (Sat.Literal.pos 3102) (Sat.Literal.pos 109) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation4 109 (assignment s)
    (Sat.Literal.pos 3103) (Sat.Literal.pos 3102) (Sat.Literal.pos 109) (Sat.Literal.pos 93) (positive_of_descriptor s 3103 (.lex permutation4 109) (by rfl)) (lex_4_109_prefix s) (positive_select s 109) (lex_4_109_image s)

theorem lex_4_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.pos 109), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation4 109 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3102) (Sat.Literal.pos 109) (Sat.Literal.pos 93) (lex_4_109_prefix s) (positive_select s 109) (lex_4_109_image s)

theorem lex_4_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.pos 3102)] :=
  (lex_4_109_gate s).prop _ (List.Mem.head _)

theorem lex_4_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.neg 109), (Sat.Literal.pos 93)] :=
  (lex_4_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.pos 109), (Sat.Literal.neg 93)] :=
  (lex_4_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.neg 109), (Sat.Literal.neg 93), (Sat.Literal.pos 3103)] :=
  (lex_4_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3102), (Sat.Literal.pos 109), (Sat.Literal.pos 93), (Sat.Literal.pos 3103)] :=
  (lex_4_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3103) = lexBefore s permutation4 108 := by
  exact (positive_lex_of_descriptor s 3103 permutation4 109 (by rfl)).trans ((lex_skipped s permutation4 108 109 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation4 108) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation4 108 by rw [image4_eq]; rfl))

theorem lex_4_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3104) (Sat.Literal.pos 3103) (Sat.Literal.pos 108) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation4 108 (assignment s)
    (Sat.Literal.pos 3104) (Sat.Literal.pos 3103) (Sat.Literal.pos 108) (Sat.Literal.pos 92) (positive_of_descriptor s 3104 (.lex permutation4 108) (by rfl)) (lex_4_108_prefix s) (positive_select s 108) (lex_4_108_image s)

theorem lex_4_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.pos 108), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation4 108 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3103) (Sat.Literal.pos 108) (Sat.Literal.pos 92) (lex_4_108_prefix s) (positive_select s 108) (lex_4_108_image s)

theorem lex_4_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.pos 3103)] :=
  (lex_4_108_gate s).prop _ (List.Mem.head _)

theorem lex_4_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.neg 108), (Sat.Literal.pos 92)] :=
  (lex_4_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.pos 108), (Sat.Literal.neg 92)] :=
  (lex_4_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.neg 108), (Sat.Literal.neg 92), (Sat.Literal.pos 3104)] :=
  (lex_4_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3103), (Sat.Literal.pos 108), (Sat.Literal.pos 92), (Sat.Literal.pos 3104)] :=
  (lex_4_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3104) = lexBefore s permutation4 107 := by
  exact (positive_lex_of_descriptor s 3104 permutation4 108 (by rfl)).trans ((lex_skipped s permutation4 107 108 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation4 107) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation4 107 by rw [image4_eq]; rfl))

theorem lex_4_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3105) (Sat.Literal.pos 3104) (Sat.Literal.pos 107) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation4 107 (assignment s)
    (Sat.Literal.pos 3105) (Sat.Literal.pos 3104) (Sat.Literal.pos 107) (Sat.Literal.pos 91) (positive_of_descriptor s 3105 (.lex permutation4 107) (by rfl)) (lex_4_107_prefix s) (positive_select s 107) (lex_4_107_image s)

theorem lex_4_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.pos 107), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation4 107 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3104) (Sat.Literal.pos 107) (Sat.Literal.pos 91) (lex_4_107_prefix s) (positive_select s 107) (lex_4_107_image s)

theorem lex_4_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.pos 3104)] :=
  (lex_4_107_gate s).prop _ (List.Mem.head _)

theorem lex_4_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.neg 107), (Sat.Literal.pos 91)] :=
  (lex_4_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.pos 107), (Sat.Literal.neg 91)] :=
  (lex_4_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.neg 107), (Sat.Literal.neg 91), (Sat.Literal.pos 3105)] :=
  (lex_4_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3104), (Sat.Literal.pos 107), (Sat.Literal.pos 91), (Sat.Literal.pos 3105)] :=
  (lex_4_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3105) = lexBefore s permutation4 106 := by
  exact (positive_lex_of_descriptor s 3105 permutation4 107 (by rfl)).trans ((lex_skipped s permutation4 106 107 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation4 106) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation4 106 by rw [image4_eq]; rfl))

theorem lex_4_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3106) (Sat.Literal.pos 3105) (Sat.Literal.pos 106) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation4 106 (assignment s)
    (Sat.Literal.pos 3106) (Sat.Literal.pos 3105) (Sat.Literal.pos 106) (Sat.Literal.pos 90) (positive_of_descriptor s 3106 (.lex permutation4 106) (by rfl)) (lex_4_106_prefix s) (positive_select s 106) (lex_4_106_image s)

theorem lex_4_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.pos 106), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation4 106 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3105) (Sat.Literal.pos 106) (Sat.Literal.pos 90) (lex_4_106_prefix s) (positive_select s 106) (lex_4_106_image s)

theorem lex_4_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.pos 3105)] :=
  (lex_4_106_gate s).prop _ (List.Mem.head _)

theorem lex_4_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.neg 106), (Sat.Literal.pos 90)] :=
  (lex_4_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.pos 106), (Sat.Literal.neg 90)] :=
  (lex_4_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.neg 106), (Sat.Literal.neg 90), (Sat.Literal.pos 3106)] :=
  (lex_4_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3105), (Sat.Literal.pos 106), (Sat.Literal.pos 90), (Sat.Literal.pos 3106)] :=
  (lex_4_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3106) = lexBefore s permutation4 105 := by
  exact (positive_lex_of_descriptor s 3106 permutation4 106 (by rfl)).trans ((lex_skipped s permutation4 105 106 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation4 105) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation4 105 by rw [image4_eq]; rfl))

theorem lex_4_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3107) (Sat.Literal.pos 3106) (Sat.Literal.pos 105) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation4 105 (assignment s)
    (Sat.Literal.pos 3107) (Sat.Literal.pos 3106) (Sat.Literal.pos 105) (Sat.Literal.pos 89) (positive_of_descriptor s 3107 (.lex permutation4 105) (by rfl)) (lex_4_105_prefix s) (positive_select s 105) (lex_4_105_image s)

theorem lex_4_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.pos 105), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation4 105 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3106) (Sat.Literal.pos 105) (Sat.Literal.pos 89) (lex_4_105_prefix s) (positive_select s 105) (lex_4_105_image s)

theorem lex_4_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.pos 3106)] :=
  (lex_4_105_gate s).prop _ (List.Mem.head _)

theorem lex_4_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.neg 105), (Sat.Literal.pos 89)] :=
  (lex_4_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.pos 105), (Sat.Literal.neg 89)] :=
  (lex_4_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.neg 105), (Sat.Literal.neg 89), (Sat.Literal.pos 3107)] :=
  (lex_4_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3106), (Sat.Literal.pos 105), (Sat.Literal.pos 89), (Sat.Literal.pos 3107)] :=
  (lex_4_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3107) = lexBefore s permutation4 104 := by
  exact (positive_lex_of_descriptor s 3107 permutation4 105 (by rfl)).trans ((lex_skipped s permutation4 104 105 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation4 104) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation4 104 by rw [image4_eq]; rfl))

theorem lex_4_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3108) (Sat.Literal.pos 3107) (Sat.Literal.pos 104) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation4 104 (assignment s)
    (Sat.Literal.pos 3108) (Sat.Literal.pos 3107) (Sat.Literal.pos 104) (Sat.Literal.pos 88) (positive_of_descriptor s 3108 (.lex permutation4 104) (by rfl)) (lex_4_104_prefix s) (positive_select s 104) (lex_4_104_image s)

theorem lex_4_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.pos 104), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation4 104 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3107) (Sat.Literal.pos 104) (Sat.Literal.pos 88) (lex_4_104_prefix s) (positive_select s 104) (lex_4_104_image s)

theorem lex_4_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.pos 3107)] :=
  (lex_4_104_gate s).prop _ (List.Mem.head _)

theorem lex_4_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.neg 104), (Sat.Literal.pos 88)] :=
  (lex_4_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.pos 104), (Sat.Literal.neg 88)] :=
  (lex_4_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.neg 104), (Sat.Literal.neg 88), (Sat.Literal.pos 3108)] :=
  (lex_4_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3107), (Sat.Literal.pos 104), (Sat.Literal.pos 88), (Sat.Literal.pos 3108)] :=
  (lex_4_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3108) = lexBefore s permutation4 103 := by
  exact (positive_lex_of_descriptor s 3108 permutation4 104 (by rfl)).trans ((lex_skipped s permutation4 103 104 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation4 103) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation4 103 by rw [image4_eq]; rfl))

theorem lex_4_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3109) (Sat.Literal.pos 3108) (Sat.Literal.pos 103) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation4 103 (assignment s)
    (Sat.Literal.pos 3109) (Sat.Literal.pos 3108) (Sat.Literal.pos 103) (Sat.Literal.pos 87) (positive_of_descriptor s 3109 (.lex permutation4 103) (by rfl)) (lex_4_103_prefix s) (positive_select s 103) (lex_4_103_image s)

theorem lex_4_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.pos 103), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation4 103 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3108) (Sat.Literal.pos 103) (Sat.Literal.pos 87) (lex_4_103_prefix s) (positive_select s 103) (lex_4_103_image s)

theorem lex_4_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.pos 3108)] :=
  (lex_4_103_gate s).prop _ (List.Mem.head _)

theorem lex_4_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.neg 103), (Sat.Literal.pos 87)] :=
  (lex_4_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.pos 103), (Sat.Literal.neg 87)] :=
  (lex_4_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.neg 103), (Sat.Literal.neg 87), (Sat.Literal.pos 3109)] :=
  (lex_4_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3108), (Sat.Literal.pos 103), (Sat.Literal.pos 87), (Sat.Literal.pos 3109)] :=
  (lex_4_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3109) = lexBefore s permutation4 102 := by
  exact (positive_lex_of_descriptor s 3109 permutation4 103 (by rfl)).trans ((lex_skipped s permutation4 102 103 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation4 102) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation4 102 by rw [image4_eq]; rfl))

theorem lex_4_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3110) (Sat.Literal.pos 3109) (Sat.Literal.pos 102) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation4 102 (assignment s)
    (Sat.Literal.pos 3110) (Sat.Literal.pos 3109) (Sat.Literal.pos 102) (Sat.Literal.pos 86) (positive_of_descriptor s 3110 (.lex permutation4 102) (by rfl)) (lex_4_102_prefix s) (positive_select s 102) (lex_4_102_image s)

theorem lex_4_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.pos 102), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation4 102 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3109) (Sat.Literal.pos 102) (Sat.Literal.pos 86) (lex_4_102_prefix s) (positive_select s 102) (lex_4_102_image s)

theorem lex_4_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.pos 3109)] :=
  (lex_4_102_gate s).prop _ (List.Mem.head _)

theorem lex_4_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.neg 102), (Sat.Literal.pos 86)] :=
  (lex_4_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.pos 102), (Sat.Literal.neg 86)] :=
  (lex_4_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.neg 102), (Sat.Literal.neg 86), (Sat.Literal.pos 3110)] :=
  (lex_4_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3109), (Sat.Literal.pos 102), (Sat.Literal.pos 86), (Sat.Literal.pos 3110)] :=
  (lex_4_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3110) = lexBefore s permutation4 101 := by
  exact (positive_lex_of_descriptor s 3110 permutation4 102 (by rfl)).trans ((lex_skipped s permutation4 101 102 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation4 101) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation4 101 by rw [image4_eq]; rfl))

theorem lex_4_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3111) (Sat.Literal.pos 3110) (Sat.Literal.pos 101) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation4 101 (assignment s)
    (Sat.Literal.pos 3111) (Sat.Literal.pos 3110) (Sat.Literal.pos 101) (Sat.Literal.pos 85) (positive_of_descriptor s 3111 (.lex permutation4 101) (by rfl)) (lex_4_101_prefix s) (positive_select s 101) (lex_4_101_image s)

theorem lex_4_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.pos 101), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation4 101 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3110) (Sat.Literal.pos 101) (Sat.Literal.pos 85) (lex_4_101_prefix s) (positive_select s 101) (lex_4_101_image s)

theorem lex_4_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.pos 3110)] :=
  (lex_4_101_gate s).prop _ (List.Mem.head _)

theorem lex_4_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.neg 101), (Sat.Literal.pos 85)] :=
  (lex_4_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.pos 101), (Sat.Literal.neg 85)] :=
  (lex_4_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.neg 101), (Sat.Literal.neg 85), (Sat.Literal.pos 3111)] :=
  (lex_4_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3110), (Sat.Literal.pos 101), (Sat.Literal.pos 85), (Sat.Literal.pos 3111)] :=
  (lex_4_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3111) = lexBefore s permutation4 100 := by
  exact (positive_lex_of_descriptor s 3111 permutation4 101 (by rfl)).trans ((lex_skipped s permutation4 100 101 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation4 100) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation4 100 by rw [image4_eq]; rfl))

theorem lex_4_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3112) (Sat.Literal.pos 3111) (Sat.Literal.pos 100) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation4 100 (assignment s)
    (Sat.Literal.pos 3112) (Sat.Literal.pos 3111) (Sat.Literal.pos 100) (Sat.Literal.pos 84) (positive_of_descriptor s 3112 (.lex permutation4 100) (by rfl)) (lex_4_100_prefix s) (positive_select s 100) (lex_4_100_image s)

theorem lex_4_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.pos 100), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation4 100 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3111) (Sat.Literal.pos 100) (Sat.Literal.pos 84) (lex_4_100_prefix s) (positive_select s 100) (lex_4_100_image s)

theorem lex_4_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.pos 3111)] :=
  (lex_4_100_gate s).prop _ (List.Mem.head _)

theorem lex_4_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.neg 100), (Sat.Literal.pos 84)] :=
  (lex_4_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.pos 100), (Sat.Literal.neg 84)] :=
  (lex_4_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.neg 100), (Sat.Literal.neg 84), (Sat.Literal.pos 3112)] :=
  (lex_4_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3111), (Sat.Literal.pos 100), (Sat.Literal.pos 84), (Sat.Literal.pos 3112)] :=
  (lex_4_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3112) = lexBefore s permutation4 99 := by
  exact (positive_lex_of_descriptor s 3112 permutation4 100 (by rfl)).trans ((lex_skipped s permutation4 99 100 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation4 99) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation4 99 by rw [image4_eq]; rfl))

theorem lex_4_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3113) (Sat.Literal.pos 3112) (Sat.Literal.pos 99) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation4 99 (assignment s)
    (Sat.Literal.pos 3113) (Sat.Literal.pos 3112) (Sat.Literal.pos 99) (Sat.Literal.pos 83) (positive_of_descriptor s 3113 (.lex permutation4 99) (by rfl)) (lex_4_99_prefix s) (positive_select s 99) (lex_4_99_image s)

theorem lex_4_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.pos 99), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation4 99 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3112) (Sat.Literal.pos 99) (Sat.Literal.pos 83) (lex_4_99_prefix s) (positive_select s 99) (lex_4_99_image s)

theorem lex_4_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.pos 3112)] :=
  (lex_4_99_gate s).prop _ (List.Mem.head _)

theorem lex_4_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.neg 99), (Sat.Literal.pos 83)] :=
  (lex_4_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.pos 99), (Sat.Literal.neg 83)] :=
  (lex_4_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.neg 99), (Sat.Literal.neg 83), (Sat.Literal.pos 3113)] :=
  (lex_4_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3112), (Sat.Literal.pos 99), (Sat.Literal.pos 83), (Sat.Literal.pos 3113)] :=
  (lex_4_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3113) = lexBefore s permutation4 98 := by
  exact (positive_lex_of_descriptor s 3113 permutation4 99 (by rfl)).trans ((lex_skipped s permutation4 98 99 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation4 98) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation4 98 by rw [image4_eq]; rfl))

theorem lex_4_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3114) (Sat.Literal.pos 3113) (Sat.Literal.pos 98) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation4 98 (assignment s)
    (Sat.Literal.pos 3114) (Sat.Literal.pos 3113) (Sat.Literal.pos 98) (Sat.Literal.pos 82) (positive_of_descriptor s 3114 (.lex permutation4 98) (by rfl)) (lex_4_98_prefix s) (positive_select s 98) (lex_4_98_image s)

theorem lex_4_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.pos 98), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation4 98 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3113) (Sat.Literal.pos 98) (Sat.Literal.pos 82) (lex_4_98_prefix s) (positive_select s 98) (lex_4_98_image s)

theorem lex_4_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.pos 3113)] :=
  (lex_4_98_gate s).prop _ (List.Mem.head _)

theorem lex_4_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.neg 98), (Sat.Literal.pos 82)] :=
  (lex_4_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.pos 98), (Sat.Literal.neg 82)] :=
  (lex_4_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.neg 98), (Sat.Literal.neg 82), (Sat.Literal.pos 3114)] :=
  (lex_4_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3113), (Sat.Literal.pos 98), (Sat.Literal.pos 82), (Sat.Literal.pos 3114)] :=
  (lex_4_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3114) = lexBefore s permutation4 97 := by
  exact (positive_lex_of_descriptor s 3114 permutation4 98 (by rfl)).trans ((lex_skipped s permutation4 97 98 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation4 97) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation4 97 by rw [image4_eq]; rfl))

theorem lex_4_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3115) (Sat.Literal.pos 3114) (Sat.Literal.pos 97) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation4 97 (assignment s)
    (Sat.Literal.pos 3115) (Sat.Literal.pos 3114) (Sat.Literal.pos 97) (Sat.Literal.pos 81) (positive_of_descriptor s 3115 (.lex permutation4 97) (by rfl)) (lex_4_97_prefix s) (positive_select s 97) (lex_4_97_image s)

theorem lex_4_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.pos 97), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation4 97 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3114) (Sat.Literal.pos 97) (Sat.Literal.pos 81) (lex_4_97_prefix s) (positive_select s 97) (lex_4_97_image s)

theorem lex_4_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.pos 3114)] :=
  (lex_4_97_gate s).prop _ (List.Mem.head _)

theorem lex_4_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.neg 97), (Sat.Literal.pos 81)] :=
  (lex_4_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.pos 97), (Sat.Literal.neg 81)] :=
  (lex_4_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.neg 97), (Sat.Literal.neg 81), (Sat.Literal.pos 3115)] :=
  (lex_4_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3114), (Sat.Literal.pos 97), (Sat.Literal.pos 81), (Sat.Literal.pos 3115)] :=
  (lex_4_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3115) = lexBefore s permutation4 96 := by
  exact (positive_lex_of_descriptor s 3115 permutation4 97 (by rfl)).trans ((lex_skipped s permutation4 96 97 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation4 96) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation4 96 by rw [image4_eq]; rfl))

theorem lex_4_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3116) (Sat.Literal.pos 3115) (Sat.Literal.pos 96) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation4 96 (assignment s)
    (Sat.Literal.pos 3116) (Sat.Literal.pos 3115) (Sat.Literal.pos 96) (Sat.Literal.pos 80) (positive_of_descriptor s 3116 (.lex permutation4 96) (by rfl)) (lex_4_96_prefix s) (positive_select s 96) (lex_4_96_image s)

theorem lex_4_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.pos 96), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation4 96 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3115) (Sat.Literal.pos 96) (Sat.Literal.pos 80) (lex_4_96_prefix s) (positive_select s 96) (lex_4_96_image s)

theorem lex_4_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.pos 3115)] :=
  (lex_4_96_gate s).prop _ (List.Mem.head _)

theorem lex_4_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.neg 96), (Sat.Literal.pos 80)] :=
  (lex_4_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.pos 96), (Sat.Literal.neg 80)] :=
  (lex_4_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.neg 96), (Sat.Literal.neg 80), (Sat.Literal.pos 3116)] :=
  (lex_4_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3115), (Sat.Literal.pos 96), (Sat.Literal.pos 80), (Sat.Literal.pos 3116)] :=
  (lex_4_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3116) = lexBefore s permutation4 95 := by
  exact (positive_lex_of_descriptor s 3116 permutation4 96 (by rfl)).trans ((lex_skipped s permutation4 95 96 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation4 95) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation4 95 by rw [image4_eq]; rfl))

theorem lex_4_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3117) (Sat.Literal.pos 3116) (Sat.Literal.pos 95) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation4 95 (assignment s)
    (Sat.Literal.pos 3117) (Sat.Literal.pos 3116) (Sat.Literal.pos 95) (Sat.Literal.pos 111) (positive_of_descriptor s 3117 (.lex permutation4 95) (by rfl)) (lex_4_95_prefix s) (positive_select s 95) (lex_4_95_image s)

theorem lex_4_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.pos 95), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation4 95 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3116) (Sat.Literal.pos 95) (Sat.Literal.pos 111) (lex_4_95_prefix s) (positive_select s 95) (lex_4_95_image s)

theorem lex_4_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.pos 3116)] :=
  (lex_4_95_gate s).prop _ (List.Mem.head _)

theorem lex_4_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.neg 95), (Sat.Literal.pos 111)] :=
  (lex_4_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.pos 95), (Sat.Literal.neg 111)] :=
  (lex_4_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.neg 95), (Sat.Literal.neg 111), (Sat.Literal.pos 3117)] :=
  (lex_4_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3116), (Sat.Literal.pos 95), (Sat.Literal.pos 111), (Sat.Literal.pos 3117)] :=
  (lex_4_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3117) = lexBefore s permutation4 94 := by
  exact (positive_lex_of_descriptor s 3117 permutation4 95 (by rfl)).trans ((lex_skipped s permutation4 94 95 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation4 94) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation4 94 by rw [image4_eq]; rfl))

theorem lex_4_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3118) (Sat.Literal.pos 3117) (Sat.Literal.pos 94) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation4 94 (assignment s)
    (Sat.Literal.pos 3118) (Sat.Literal.pos 3117) (Sat.Literal.pos 94) (Sat.Literal.pos 110) (positive_of_descriptor s 3118 (.lex permutation4 94) (by rfl)) (lex_4_94_prefix s) (positive_select s 94) (lex_4_94_image s)

theorem lex_4_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.pos 94), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation4 94 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3117) (Sat.Literal.pos 94) (Sat.Literal.pos 110) (lex_4_94_prefix s) (positive_select s 94) (lex_4_94_image s)

theorem lex_4_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.pos 3117)] :=
  (lex_4_94_gate s).prop _ (List.Mem.head _)

theorem lex_4_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.neg 94), (Sat.Literal.pos 110)] :=
  (lex_4_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.pos 94), (Sat.Literal.neg 110)] :=
  (lex_4_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.neg 94), (Sat.Literal.neg 110), (Sat.Literal.pos 3118)] :=
  (lex_4_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3117), (Sat.Literal.pos 94), (Sat.Literal.pos 110), (Sat.Literal.pos 3118)] :=
  (lex_4_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3118) = lexBefore s permutation4 93 := by
  exact (positive_lex_of_descriptor s 3118 permutation4 94 (by rfl)).trans ((lex_skipped s permutation4 93 94 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation4 93) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation4 93 by rw [image4_eq]; rfl))

theorem lex_4_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3119) (Sat.Literal.pos 3118) (Sat.Literal.pos 93) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation4 93 (assignment s)
    (Sat.Literal.pos 3119) (Sat.Literal.pos 3118) (Sat.Literal.pos 93) (Sat.Literal.pos 109) (positive_of_descriptor s 3119 (.lex permutation4 93) (by rfl)) (lex_4_93_prefix s) (positive_select s 93) (lex_4_93_image s)

theorem lex_4_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.pos 93), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation4 93 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3118) (Sat.Literal.pos 93) (Sat.Literal.pos 109) (lex_4_93_prefix s) (positive_select s 93) (lex_4_93_image s)

theorem lex_4_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.pos 3118)] :=
  (lex_4_93_gate s).prop _ (List.Mem.head _)

theorem lex_4_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.neg 93), (Sat.Literal.pos 109)] :=
  (lex_4_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.pos 93), (Sat.Literal.neg 109)] :=
  (lex_4_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.neg 93), (Sat.Literal.neg 109), (Sat.Literal.pos 3119)] :=
  (lex_4_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3118), (Sat.Literal.pos 93), (Sat.Literal.pos 109), (Sat.Literal.pos 3119)] :=
  (lex_4_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3119) = lexBefore s permutation4 92 := by
  exact (positive_lex_of_descriptor s 3119 permutation4 93 (by rfl)).trans ((lex_skipped s permutation4 92 93 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation4 92) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation4 92 by rw [image4_eq]; rfl))

theorem lex_4_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3120) (Sat.Literal.pos 3119) (Sat.Literal.pos 92) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation4 92 (assignment s)
    (Sat.Literal.pos 3120) (Sat.Literal.pos 3119) (Sat.Literal.pos 92) (Sat.Literal.pos 108) (positive_of_descriptor s 3120 (.lex permutation4 92) (by rfl)) (lex_4_92_prefix s) (positive_select s 92) (lex_4_92_image s)

theorem lex_4_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.pos 92), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation4 92 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3119) (Sat.Literal.pos 92) (Sat.Literal.pos 108) (lex_4_92_prefix s) (positive_select s 92) (lex_4_92_image s)

theorem lex_4_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.pos 3119)] :=
  (lex_4_92_gate s).prop _ (List.Mem.head _)

theorem lex_4_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.neg 92), (Sat.Literal.pos 108)] :=
  (lex_4_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.pos 92), (Sat.Literal.neg 108)] :=
  (lex_4_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.neg 92), (Sat.Literal.neg 108), (Sat.Literal.pos 3120)] :=
  (lex_4_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3119), (Sat.Literal.pos 92), (Sat.Literal.pos 108), (Sat.Literal.pos 3120)] :=
  (lex_4_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3120) = lexBefore s permutation4 91 := by
  exact (positive_lex_of_descriptor s 3120 permutation4 92 (by rfl)).trans ((lex_skipped s permutation4 91 92 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation4 91) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation4 91 by rw [image4_eq]; rfl))

theorem lex_4_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3121) (Sat.Literal.pos 3120) (Sat.Literal.pos 91) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation4 91 (assignment s)
    (Sat.Literal.pos 3121) (Sat.Literal.pos 3120) (Sat.Literal.pos 91) (Sat.Literal.pos 107) (positive_of_descriptor s 3121 (.lex permutation4 91) (by rfl)) (lex_4_91_prefix s) (positive_select s 91) (lex_4_91_image s)

theorem lex_4_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.pos 91), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation4 91 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3120) (Sat.Literal.pos 91) (Sat.Literal.pos 107) (lex_4_91_prefix s) (positive_select s 91) (lex_4_91_image s)

theorem lex_4_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.pos 3120)] :=
  (lex_4_91_gate s).prop _ (List.Mem.head _)

theorem lex_4_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.neg 91), (Sat.Literal.pos 107)] :=
  (lex_4_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.pos 91), (Sat.Literal.neg 107)] :=
  (lex_4_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.neg 91), (Sat.Literal.neg 107), (Sat.Literal.pos 3121)] :=
  (lex_4_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3120), (Sat.Literal.pos 91), (Sat.Literal.pos 107), (Sat.Literal.pos 3121)] :=
  (lex_4_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3121) = lexBefore s permutation4 90 := by
  exact (positive_lex_of_descriptor s 3121 permutation4 91 (by rfl)).trans ((lex_skipped s permutation4 90 91 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation4 90) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation4 90 by rw [image4_eq]; rfl))

theorem lex_4_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3122) (Sat.Literal.pos 3121) (Sat.Literal.pos 90) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation4 90 (assignment s)
    (Sat.Literal.pos 3122) (Sat.Literal.pos 3121) (Sat.Literal.pos 90) (Sat.Literal.pos 106) (positive_of_descriptor s 3122 (.lex permutation4 90) (by rfl)) (lex_4_90_prefix s) (positive_select s 90) (lex_4_90_image s)

theorem lex_4_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.pos 90), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation4 90 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3121) (Sat.Literal.pos 90) (Sat.Literal.pos 106) (lex_4_90_prefix s) (positive_select s 90) (lex_4_90_image s)

theorem lex_4_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.pos 3121)] :=
  (lex_4_90_gate s).prop _ (List.Mem.head _)

theorem lex_4_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.neg 90), (Sat.Literal.pos 106)] :=
  (lex_4_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.pos 90), (Sat.Literal.neg 106)] :=
  (lex_4_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.neg 90), (Sat.Literal.neg 106), (Sat.Literal.pos 3122)] :=
  (lex_4_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3121), (Sat.Literal.pos 90), (Sat.Literal.pos 106), (Sat.Literal.pos 3122)] :=
  (lex_4_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3122) = lexBefore s permutation4 89 := by
  exact (positive_lex_of_descriptor s 3122 permutation4 90 (by rfl)).trans ((lex_skipped s permutation4 89 90 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation4 89) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation4 89 by rw [image4_eq]; rfl))

theorem lex_4_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3123) (Sat.Literal.pos 3122) (Sat.Literal.pos 89) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation4 89 (assignment s)
    (Sat.Literal.pos 3123) (Sat.Literal.pos 3122) (Sat.Literal.pos 89) (Sat.Literal.pos 105) (positive_of_descriptor s 3123 (.lex permutation4 89) (by rfl)) (lex_4_89_prefix s) (positive_select s 89) (lex_4_89_image s)

theorem lex_4_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.pos 89), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation4 89 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3122) (Sat.Literal.pos 89) (Sat.Literal.pos 105) (lex_4_89_prefix s) (positive_select s 89) (lex_4_89_image s)

theorem lex_4_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.pos 3122)] :=
  (lex_4_89_gate s).prop _ (List.Mem.head _)

theorem lex_4_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.neg 89), (Sat.Literal.pos 105)] :=
  (lex_4_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.pos 89), (Sat.Literal.neg 105)] :=
  (lex_4_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.neg 89), (Sat.Literal.neg 105), (Sat.Literal.pos 3123)] :=
  (lex_4_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3122), (Sat.Literal.pos 89), (Sat.Literal.pos 105), (Sat.Literal.pos 3123)] :=
  (lex_4_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3123) = lexBefore s permutation4 88 := by
  exact (positive_lex_of_descriptor s 3123 permutation4 89 (by rfl)).trans ((lex_skipped s permutation4 88 89 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation4 88) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation4 88 by rw [image4_eq]; rfl))

theorem lex_4_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3124) (Sat.Literal.pos 3123) (Sat.Literal.pos 88) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation4 88 (assignment s)
    (Sat.Literal.pos 3124) (Sat.Literal.pos 3123) (Sat.Literal.pos 88) (Sat.Literal.pos 104) (positive_of_descriptor s 3124 (.lex permutation4 88) (by rfl)) (lex_4_88_prefix s) (positive_select s 88) (lex_4_88_image s)

theorem lex_4_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.pos 88), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation4 88 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3123) (Sat.Literal.pos 88) (Sat.Literal.pos 104) (lex_4_88_prefix s) (positive_select s 88) (lex_4_88_image s)

theorem lex_4_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.pos 3123)] :=
  (lex_4_88_gate s).prop _ (List.Mem.head _)

theorem lex_4_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.neg 88), (Sat.Literal.pos 104)] :=
  (lex_4_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.pos 88), (Sat.Literal.neg 104)] :=
  (lex_4_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.neg 88), (Sat.Literal.neg 104), (Sat.Literal.pos 3124)] :=
  (lex_4_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3123), (Sat.Literal.pos 88), (Sat.Literal.pos 104), (Sat.Literal.pos 3124)] :=
  (lex_4_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_3_19_gate

end Crown.CertificateData
