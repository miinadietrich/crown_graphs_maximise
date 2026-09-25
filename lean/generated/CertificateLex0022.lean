import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_12_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4724) = lexBefore s permutation12 204 := by
  exact (positive_lex_of_descriptor s 4724 permutation12 205 (by rfl)).trans ((lex_skipped s permutation12 204 205 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation12 204) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation12 204 by rw [image12_eq]; rfl))

theorem lex_12_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4725) (Sat.Literal.pos 4724) (Sat.Literal.pos 204) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation12 204 (assignment s)
    (Sat.Literal.pos 4725) (Sat.Literal.pos 4724) (Sat.Literal.pos 204) (Sat.Literal.pos 51) (positive_of_descriptor s 4725 (.lex permutation12 204) (by rfl)) (lex_12_204_prefix s) (positive_select s 204) (lex_12_204_image s)

theorem lex_12_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.pos 204), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation12 204 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4724) (Sat.Literal.pos 204) (Sat.Literal.pos 51) (lex_12_204_prefix s) (positive_select s 204) (lex_12_204_image s)

theorem lex_12_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.pos 4724)] :=
  (lex_12_204_gate s).prop _ (List.Mem.head _)

theorem lex_12_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.neg 204), (Sat.Literal.pos 51)] :=
  (lex_12_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.pos 204), (Sat.Literal.neg 51)] :=
  (lex_12_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.neg 204), (Sat.Literal.neg 51), (Sat.Literal.pos 4725)] :=
  (lex_12_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.pos 204), (Sat.Literal.pos 51), (Sat.Literal.pos 4725)] :=
  (lex_12_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4725) = lexBefore s permutation12 203 := by
  exact (positive_lex_of_descriptor s 4725 permutation12 204 (by rfl)).trans ((lex_skipped s permutation12 203 204 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation12 203) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation12 203 by rw [image12_eq]; rfl))

theorem lex_12_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4726) (Sat.Literal.pos 4725) (Sat.Literal.pos 203) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation12 203 (assignment s)
    (Sat.Literal.pos 4726) (Sat.Literal.pos 4725) (Sat.Literal.pos 203) (Sat.Literal.pos 242) (positive_of_descriptor s 4726 (.lex permutation12 203) (by rfl)) (lex_12_203_prefix s) (positive_select s 203) (lex_12_203_image s)

theorem lex_12_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.pos 203), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation12 203 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4725) (Sat.Literal.pos 203) (Sat.Literal.pos 242) (lex_12_203_prefix s) (positive_select s 203) (lex_12_203_image s)

theorem lex_12_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.pos 4725)] :=
  (lex_12_203_gate s).prop _ (List.Mem.head _)

theorem lex_12_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.neg 203), (Sat.Literal.pos 242)] :=
  (lex_12_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.pos 203), (Sat.Literal.neg 242)] :=
  (lex_12_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.neg 203), (Sat.Literal.neg 242), (Sat.Literal.pos 4726)] :=
  (lex_12_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4725), (Sat.Literal.pos 203), (Sat.Literal.pos 242), (Sat.Literal.pos 4726)] :=
  (lex_12_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4726) = lexBefore s permutation12 202 := by
  exact (positive_lex_of_descriptor s 4726 permutation12 203 (by rfl)).trans ((lex_skipped s permutation12 202 203 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation12 202) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation12 202 by rw [image12_eq]; rfl))

theorem lex_12_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4727) (Sat.Literal.pos 4726) (Sat.Literal.pos 202) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation12 202 (assignment s)
    (Sat.Literal.pos 4727) (Sat.Literal.pos 4726) (Sat.Literal.pos 202) (Sat.Literal.pos 178) (positive_of_descriptor s 4727 (.lex permutation12 202) (by rfl)) (lex_12_202_prefix s) (positive_select s 202) (lex_12_202_image s)

theorem lex_12_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.pos 202), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation12 202 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4726) (Sat.Literal.pos 202) (Sat.Literal.pos 178) (lex_12_202_prefix s) (positive_select s 202) (lex_12_202_image s)

theorem lex_12_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.pos 4726)] :=
  (lex_12_202_gate s).prop _ (List.Mem.head _)

theorem lex_12_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.neg 202), (Sat.Literal.pos 178)] :=
  (lex_12_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.pos 202), (Sat.Literal.neg 178)] :=
  (lex_12_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.neg 202), (Sat.Literal.neg 178), (Sat.Literal.pos 4727)] :=
  (lex_12_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4726), (Sat.Literal.pos 202), (Sat.Literal.pos 178), (Sat.Literal.pos 4727)] :=
  (lex_12_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4727) = lexBefore s permutation12 201 := by
  exact (positive_lex_of_descriptor s 4727 permutation12 202 (by rfl)).trans ((lex_skipped s permutation12 201 202 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation12 201) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation12 201 by rw [image12_eq]; rfl))

theorem lex_12_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4728) (Sat.Literal.pos 4727) (Sat.Literal.pos 201) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation12 201 (assignment s)
    (Sat.Literal.pos 4728) (Sat.Literal.pos 4727) (Sat.Literal.pos 201) (Sat.Literal.pos 114) (positive_of_descriptor s 4728 (.lex permutation12 201) (by rfl)) (lex_12_201_prefix s) (positive_select s 201) (lex_12_201_image s)

theorem lex_12_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.pos 201), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation12 201 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4727) (Sat.Literal.pos 201) (Sat.Literal.pos 114) (lex_12_201_prefix s) (positive_select s 201) (lex_12_201_image s)

theorem lex_12_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.pos 4727)] :=
  (lex_12_201_gate s).prop _ (List.Mem.head _)

theorem lex_12_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.neg 201), (Sat.Literal.pos 114)] :=
  (lex_12_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.pos 201), (Sat.Literal.neg 114)] :=
  (lex_12_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.neg 201), (Sat.Literal.neg 114), (Sat.Literal.pos 4728)] :=
  (lex_12_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4727), (Sat.Literal.pos 201), (Sat.Literal.pos 114), (Sat.Literal.pos 4728)] :=
  (lex_12_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4728) = lexBefore s permutation12 200 := by
  exact (positive_lex_of_descriptor s 4728 permutation12 201 (by rfl)).trans ((lex_skipped s permutation12 200 201 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation12 200) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation12 200 by rw [image12_eq]; rfl))

theorem lex_12_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4729) (Sat.Literal.pos 4728) (Sat.Literal.pos 200) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation12 200 (assignment s)
    (Sat.Literal.pos 4729) (Sat.Literal.pos 4728) (Sat.Literal.pos 200) (Sat.Literal.pos 50) (positive_of_descriptor s 4729 (.lex permutation12 200) (by rfl)) (lex_12_200_prefix s) (positive_select s 200) (lex_12_200_image s)

theorem lex_12_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.pos 200), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation12 200 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4728) (Sat.Literal.pos 200) (Sat.Literal.pos 50) (lex_12_200_prefix s) (positive_select s 200) (lex_12_200_image s)

theorem lex_12_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.pos 4728)] :=
  (lex_12_200_gate s).prop _ (List.Mem.head _)

theorem lex_12_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.neg 200), (Sat.Literal.pos 50)] :=
  (lex_12_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.pos 200), (Sat.Literal.neg 50)] :=
  (lex_12_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.neg 200), (Sat.Literal.neg 50), (Sat.Literal.pos 4729)] :=
  (lex_12_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4728), (Sat.Literal.pos 200), (Sat.Literal.pos 50), (Sat.Literal.pos 4729)] :=
  (lex_12_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4729) = lexBefore s permutation12 199 := by
  exact (positive_lex_of_descriptor s 4729 permutation12 200 (by rfl)).trans ((lex_skipped s permutation12 199 200 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation12 199) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation12 199 by rw [image12_eq]; rfl))

theorem lex_12_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4730) (Sat.Literal.pos 4729) (Sat.Literal.pos 199) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation12 199 (assignment s)
    (Sat.Literal.pos 4730) (Sat.Literal.pos 4729) (Sat.Literal.pos 199) (Sat.Literal.pos 241) (positive_of_descriptor s 4730 (.lex permutation12 199) (by rfl)) (lex_12_199_prefix s) (positive_select s 199) (lex_12_199_image s)

theorem lex_12_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.pos 199), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation12 199 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4729) (Sat.Literal.pos 199) (Sat.Literal.pos 241) (lex_12_199_prefix s) (positive_select s 199) (lex_12_199_image s)

theorem lex_12_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.pos 4729)] :=
  (lex_12_199_gate s).prop _ (List.Mem.head _)

theorem lex_12_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.neg 199), (Sat.Literal.pos 241)] :=
  (lex_12_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.pos 199), (Sat.Literal.neg 241)] :=
  (lex_12_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.neg 199), (Sat.Literal.neg 241), (Sat.Literal.pos 4730)] :=
  (lex_12_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4729), (Sat.Literal.pos 199), (Sat.Literal.pos 241), (Sat.Literal.pos 4730)] :=
  (lex_12_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4730) = lexBefore s permutation12 198 := by
  exact (positive_lex_of_descriptor s 4730 permutation12 199 (by rfl)).trans ((lex_skipped s permutation12 198 199 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation12 198) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation12 198 by rw [image12_eq]; rfl))

theorem lex_12_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4731) (Sat.Literal.pos 4730) (Sat.Literal.pos 198) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation12 198 (assignment s)
    (Sat.Literal.pos 4731) (Sat.Literal.pos 4730) (Sat.Literal.pos 198) (Sat.Literal.pos 177) (positive_of_descriptor s 4731 (.lex permutation12 198) (by rfl)) (lex_12_198_prefix s) (positive_select s 198) (lex_12_198_image s)

theorem lex_12_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.pos 198), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation12 198 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4730) (Sat.Literal.pos 198) (Sat.Literal.pos 177) (lex_12_198_prefix s) (positive_select s 198) (lex_12_198_image s)

theorem lex_12_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.pos 4730)] :=
  (lex_12_198_gate s).prop _ (List.Mem.head _)

theorem lex_12_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.neg 198), (Sat.Literal.pos 177)] :=
  (lex_12_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.pos 198), (Sat.Literal.neg 177)] :=
  (lex_12_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.neg 198), (Sat.Literal.neg 177), (Sat.Literal.pos 4731)] :=
  (lex_12_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4730), (Sat.Literal.pos 198), (Sat.Literal.pos 177), (Sat.Literal.pos 4731)] :=
  (lex_12_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4731) = lexBefore s permutation12 197 := by
  exact (positive_lex_of_descriptor s 4731 permutation12 198 (by rfl)).trans ((lex_skipped s permutation12 197 198 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation12 197) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation12 197 by rw [image12_eq]; rfl))

theorem lex_12_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4732) (Sat.Literal.pos 4731) (Sat.Literal.pos 197) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation12 197 (assignment s)
    (Sat.Literal.pos 4732) (Sat.Literal.pos 4731) (Sat.Literal.pos 197) (Sat.Literal.pos 113) (positive_of_descriptor s 4732 (.lex permutation12 197) (by rfl)) (lex_12_197_prefix s) (positive_select s 197) (lex_12_197_image s)

theorem lex_12_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.pos 197), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation12 197 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4731) (Sat.Literal.pos 197) (Sat.Literal.pos 113) (lex_12_197_prefix s) (positive_select s 197) (lex_12_197_image s)

theorem lex_12_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.pos 4731)] :=
  (lex_12_197_gate s).prop _ (List.Mem.head _)

theorem lex_12_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.neg 197), (Sat.Literal.pos 113)] :=
  (lex_12_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.pos 197), (Sat.Literal.neg 113)] :=
  (lex_12_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.neg 197), (Sat.Literal.neg 113), (Sat.Literal.pos 4732)] :=
  (lex_12_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4731), (Sat.Literal.pos 197), (Sat.Literal.pos 113), (Sat.Literal.pos 4732)] :=
  (lex_12_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4732) = lexBefore s permutation12 196 := by
  exact (positive_lex_of_descriptor s 4732 permutation12 197 (by rfl)).trans ((lex_skipped s permutation12 196 197 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation12 196) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation12 196 by rw [image12_eq]; rfl))

theorem lex_12_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4733) (Sat.Literal.pos 4732) (Sat.Literal.pos 196) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation12 196 (assignment s)
    (Sat.Literal.pos 4733) (Sat.Literal.pos 4732) (Sat.Literal.pos 196) (Sat.Literal.pos 49) (positive_of_descriptor s 4733 (.lex permutation12 196) (by rfl)) (lex_12_196_prefix s) (positive_select s 196) (lex_12_196_image s)

theorem lex_12_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.pos 196), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation12 196 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4732) (Sat.Literal.pos 196) (Sat.Literal.pos 49) (lex_12_196_prefix s) (positive_select s 196) (lex_12_196_image s)

theorem lex_12_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.pos 4732)] :=
  (lex_12_196_gate s).prop _ (List.Mem.head _)

theorem lex_12_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.neg 196), (Sat.Literal.pos 49)] :=
  (lex_12_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.pos 196), (Sat.Literal.neg 49)] :=
  (lex_12_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.neg 196), (Sat.Literal.neg 49), (Sat.Literal.pos 4733)] :=
  (lex_12_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4732), (Sat.Literal.pos 196), (Sat.Literal.pos 49), (Sat.Literal.pos 4733)] :=
  (lex_12_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4733) = lexBefore s permutation12 195 := by
  exact (positive_lex_of_descriptor s 4733 permutation12 196 (by rfl)).trans ((lex_skipped s permutation12 195 196 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation12 195) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation12 195 by rw [image12_eq]; rfl))

theorem lex_12_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4734) (Sat.Literal.pos 4733) (Sat.Literal.pos 195) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation12 195 (assignment s)
    (Sat.Literal.pos 4734) (Sat.Literal.pos 4733) (Sat.Literal.pos 195) (Sat.Literal.pos 240) (positive_of_descriptor s 4734 (.lex permutation12 195) (by rfl)) (lex_12_195_prefix s) (positive_select s 195) (lex_12_195_image s)

theorem lex_12_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.pos 195), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation12 195 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4733) (Sat.Literal.pos 195) (Sat.Literal.pos 240) (lex_12_195_prefix s) (positive_select s 195) (lex_12_195_image s)

theorem lex_12_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.pos 4733)] :=
  (lex_12_195_gate s).prop _ (List.Mem.head _)

theorem lex_12_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.neg 195), (Sat.Literal.pos 240)] :=
  (lex_12_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.pos 195), (Sat.Literal.neg 240)] :=
  (lex_12_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.neg 195), (Sat.Literal.neg 240), (Sat.Literal.pos 4734)] :=
  (lex_12_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4733), (Sat.Literal.pos 195), (Sat.Literal.pos 240), (Sat.Literal.pos 4734)] :=
  (lex_12_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4734) = lexBefore s permutation12 194 := by
  exact (positive_lex_of_descriptor s 4734 permutation12 195 (by rfl)).trans ((lex_skipped s permutation12 194 195 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation12 194) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation12 194 by rw [image12_eq]; rfl))

theorem lex_12_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4735) (Sat.Literal.pos 4734) (Sat.Literal.pos 194) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation12 194 (assignment s)
    (Sat.Literal.pos 4735) (Sat.Literal.pos 4734) (Sat.Literal.pos 194) (Sat.Literal.pos 176) (positive_of_descriptor s 4735 (.lex permutation12 194) (by rfl)) (lex_12_194_prefix s) (positive_select s 194) (lex_12_194_image s)

theorem lex_12_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.pos 194), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation12 194 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4734) (Sat.Literal.pos 194) (Sat.Literal.pos 176) (lex_12_194_prefix s) (positive_select s 194) (lex_12_194_image s)

theorem lex_12_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.pos 4734)] :=
  (lex_12_194_gate s).prop _ (List.Mem.head _)

theorem lex_12_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.neg 194), (Sat.Literal.pos 176)] :=
  (lex_12_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.pos 194), (Sat.Literal.neg 176)] :=
  (lex_12_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.neg 194), (Sat.Literal.neg 176), (Sat.Literal.pos 4735)] :=
  (lex_12_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4734), (Sat.Literal.pos 194), (Sat.Literal.pos 176), (Sat.Literal.pos 4735)] :=
  (lex_12_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4735) = lexBefore s permutation12 193 := by
  exact (positive_lex_of_descriptor s 4735 permutation12 194 (by rfl)).trans ((lex_skipped s permutation12 193 194 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation12 193) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation12 193 by rw [image12_eq]; rfl))

theorem lex_12_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4736) (Sat.Literal.pos 4735) (Sat.Literal.pos 193) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation12 193 (assignment s)
    (Sat.Literal.pos 4736) (Sat.Literal.pos 4735) (Sat.Literal.pos 193) (Sat.Literal.pos 112) (positive_of_descriptor s 4736 (.lex permutation12 193) (by rfl)) (lex_12_193_prefix s) (positive_select s 193) (lex_12_193_image s)

theorem lex_12_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.pos 193), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation12 193 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4735) (Sat.Literal.pos 193) (Sat.Literal.pos 112) (lex_12_193_prefix s) (positive_select s 193) (lex_12_193_image s)

theorem lex_12_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.pos 4735)] :=
  (lex_12_193_gate s).prop _ (List.Mem.head _)

theorem lex_12_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.neg 193), (Sat.Literal.pos 112)] :=
  (lex_12_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.pos 193), (Sat.Literal.neg 112)] :=
  (lex_12_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.neg 193), (Sat.Literal.neg 112), (Sat.Literal.pos 4736)] :=
  (lex_12_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4735), (Sat.Literal.pos 193), (Sat.Literal.pos 112), (Sat.Literal.pos 4736)] :=
  (lex_12_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4736) = lexBefore s permutation12 192 := by
  exact (positive_lex_of_descriptor s 4736 permutation12 193 (by rfl)).trans ((lex_skipped s permutation12 192 193 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation12 192) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation12 192 by rw [image12_eq]; rfl))

theorem lex_12_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4737) (Sat.Literal.pos 4736) (Sat.Literal.pos 192) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation12 192 (assignment s)
    (Sat.Literal.pos 4737) (Sat.Literal.pos 4736) (Sat.Literal.pos 192) (Sat.Literal.pos 48) (positive_of_descriptor s 4737 (.lex permutation12 192) (by rfl)) (lex_12_192_prefix s) (positive_select s 192) (lex_12_192_image s)

theorem lex_12_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.pos 192), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation12 192 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4736) (Sat.Literal.pos 192) (Sat.Literal.pos 48) (lex_12_192_prefix s) (positive_select s 192) (lex_12_192_image s)

theorem lex_12_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.pos 4736)] :=
  (lex_12_192_gate s).prop _ (List.Mem.head _)

theorem lex_12_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.neg 192), (Sat.Literal.pos 48)] :=
  (lex_12_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.pos 192), (Sat.Literal.neg 48)] :=
  (lex_12_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.neg 192), (Sat.Literal.neg 48), (Sat.Literal.pos 4737)] :=
  (lex_12_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4736), (Sat.Literal.pos 192), (Sat.Literal.pos 48), (Sat.Literal.pos 4737)] :=
  (lex_12_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4737) = lexBefore s permutation12 191 := by
  exact (positive_lex_of_descriptor s 4737 permutation12 192 (by rfl)).trans ((lex_skipped s permutation12 191 192 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation12 191) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation12 191 by rw [image12_eq]; rfl))

theorem lex_12_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4738) (Sat.Literal.pos 4737) (Sat.Literal.pos 191) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation12 191 (assignment s)
    (Sat.Literal.pos 4738) (Sat.Literal.pos 4737) (Sat.Literal.pos 191) (Sat.Literal.pos 239) (positive_of_descriptor s 4738 (.lex permutation12 191) (by rfl)) (lex_12_191_prefix s) (positive_select s 191) (lex_12_191_image s)

theorem lex_12_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.pos 191), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation12 191 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4737) (Sat.Literal.pos 191) (Sat.Literal.pos 239) (lex_12_191_prefix s) (positive_select s 191) (lex_12_191_image s)

theorem lex_12_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.pos 4737)] :=
  (lex_12_191_gate s).prop _ (List.Mem.head _)

theorem lex_12_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.neg 191), (Sat.Literal.pos 239)] :=
  (lex_12_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.pos 191), (Sat.Literal.neg 239)] :=
  (lex_12_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.neg 191), (Sat.Literal.neg 239), (Sat.Literal.pos 4738)] :=
  (lex_12_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4737), (Sat.Literal.pos 191), (Sat.Literal.pos 239), (Sat.Literal.pos 4738)] :=
  (lex_12_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4738) = lexBefore s permutation12 190 := by
  exact (positive_lex_of_descriptor s 4738 permutation12 191 (by rfl)).trans ((lex_skipped s permutation12 190 191 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation12 190) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation12 190 by rw [image12_eq]; rfl))

theorem lex_12_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4739) (Sat.Literal.pos 4738) (Sat.Literal.pos 190) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation12 190 (assignment s)
    (Sat.Literal.pos 4739) (Sat.Literal.pos 4738) (Sat.Literal.pos 190) (Sat.Literal.pos 175) (positive_of_descriptor s 4739 (.lex permutation12 190) (by rfl)) (lex_12_190_prefix s) (positive_select s 190) (lex_12_190_image s)

theorem lex_12_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.pos 190), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation12 190 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4738) (Sat.Literal.pos 190) (Sat.Literal.pos 175) (lex_12_190_prefix s) (positive_select s 190) (lex_12_190_image s)

theorem lex_12_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.pos 4738)] :=
  (lex_12_190_gate s).prop _ (List.Mem.head _)

theorem lex_12_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.neg 190), (Sat.Literal.pos 175)] :=
  (lex_12_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.pos 190), (Sat.Literal.neg 175)] :=
  (lex_12_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.neg 190), (Sat.Literal.neg 175), (Sat.Literal.pos 4739)] :=
  (lex_12_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4738), (Sat.Literal.pos 190), (Sat.Literal.pos 175), (Sat.Literal.pos 4739)] :=
  (lex_12_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4739) = lexBefore s permutation12 189 := by
  exact (positive_lex_of_descriptor s 4739 permutation12 190 (by rfl)).trans ((lex_skipped s permutation12 189 190 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation12 189) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation12 189 by rw [image12_eq]; rfl))

theorem lex_12_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4740) (Sat.Literal.pos 4739) (Sat.Literal.pos 189) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation12 189 (assignment s)
    (Sat.Literal.pos 4740) (Sat.Literal.pos 4739) (Sat.Literal.pos 189) (Sat.Literal.pos 111) (positive_of_descriptor s 4740 (.lex permutation12 189) (by rfl)) (lex_12_189_prefix s) (positive_select s 189) (lex_12_189_image s)

theorem lex_12_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.pos 189), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation12 189 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4739) (Sat.Literal.pos 189) (Sat.Literal.pos 111) (lex_12_189_prefix s) (positive_select s 189) (lex_12_189_image s)

theorem lex_12_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.pos 4739)] :=
  (lex_12_189_gate s).prop _ (List.Mem.head _)

theorem lex_12_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.neg 189), (Sat.Literal.pos 111)] :=
  (lex_12_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.pos 189), (Sat.Literal.neg 111)] :=
  (lex_12_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.neg 189), (Sat.Literal.neg 111), (Sat.Literal.pos 4740)] :=
  (lex_12_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4739), (Sat.Literal.pos 189), (Sat.Literal.pos 111), (Sat.Literal.pos 4740)] :=
  (lex_12_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4740) = lexBefore s permutation12 188 := by
  exact (positive_lex_of_descriptor s 4740 permutation12 189 (by rfl)).trans ((lex_skipped s permutation12 188 189 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation12 188) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation12 188 by rw [image12_eq]; rfl))

theorem lex_12_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4741) (Sat.Literal.pos 4740) (Sat.Literal.pos 188) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation12 188 (assignment s)
    (Sat.Literal.pos 4741) (Sat.Literal.pos 4740) (Sat.Literal.pos 188) (Sat.Literal.pos 47) (positive_of_descriptor s 4741 (.lex permutation12 188) (by rfl)) (lex_12_188_prefix s) (positive_select s 188) (lex_12_188_image s)

theorem lex_12_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.pos 188), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation12 188 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4740) (Sat.Literal.pos 188) (Sat.Literal.pos 47) (lex_12_188_prefix s) (positive_select s 188) (lex_12_188_image s)

theorem lex_12_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.pos 4740)] :=
  (lex_12_188_gate s).prop _ (List.Mem.head _)

theorem lex_12_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.neg 188), (Sat.Literal.pos 47)] :=
  (lex_12_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.pos 188), (Sat.Literal.neg 47)] :=
  (lex_12_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.neg 188), (Sat.Literal.neg 47), (Sat.Literal.pos 4741)] :=
  (lex_12_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4740), (Sat.Literal.pos 188), (Sat.Literal.pos 47), (Sat.Literal.pos 4741)] :=
  (lex_12_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4741) = lexBefore s permutation12 187 := by
  exact (positive_lex_of_descriptor s 4741 permutation12 188 (by rfl)).trans ((lex_skipped s permutation12 187 188 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation12 187) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation12 187 by rw [image12_eq]; rfl))

theorem lex_12_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4742) (Sat.Literal.pos 4741) (Sat.Literal.pos 187) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation12 187 (assignment s)
    (Sat.Literal.pos 4742) (Sat.Literal.pos 4741) (Sat.Literal.pos 187) (Sat.Literal.pos 238) (positive_of_descriptor s 4742 (.lex permutation12 187) (by rfl)) (lex_12_187_prefix s) (positive_select s 187) (lex_12_187_image s)

theorem lex_12_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.pos 187), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation12 187 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4741) (Sat.Literal.pos 187) (Sat.Literal.pos 238) (lex_12_187_prefix s) (positive_select s 187) (lex_12_187_image s)

theorem lex_12_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.pos 4741)] :=
  (lex_12_187_gate s).prop _ (List.Mem.head _)

theorem lex_12_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.neg 187), (Sat.Literal.pos 238)] :=
  (lex_12_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.pos 187), (Sat.Literal.neg 238)] :=
  (lex_12_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.neg 187), (Sat.Literal.neg 238), (Sat.Literal.pos 4742)] :=
  (lex_12_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4741), (Sat.Literal.pos 187), (Sat.Literal.pos 238), (Sat.Literal.pos 4742)] :=
  (lex_12_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4742) = lexBefore s permutation12 186 := by
  exact (positive_lex_of_descriptor s 4742 permutation12 187 (by rfl)).trans ((lex_skipped s permutation12 186 187 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation12 186) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation12 186 by rw [image12_eq]; rfl))

theorem lex_12_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4743) (Sat.Literal.pos 4742) (Sat.Literal.pos 186) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation12 186 (assignment s)
    (Sat.Literal.pos 4743) (Sat.Literal.pos 4742) (Sat.Literal.pos 186) (Sat.Literal.pos 174) (positive_of_descriptor s 4743 (.lex permutation12 186) (by rfl)) (lex_12_186_prefix s) (positive_select s 186) (lex_12_186_image s)

theorem lex_12_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.pos 186), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation12 186 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4742) (Sat.Literal.pos 186) (Sat.Literal.pos 174) (lex_12_186_prefix s) (positive_select s 186) (lex_12_186_image s)

theorem lex_12_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.pos 4742)] :=
  (lex_12_186_gate s).prop _ (List.Mem.head _)

theorem lex_12_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.neg 186), (Sat.Literal.pos 174)] :=
  (lex_12_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.pos 186), (Sat.Literal.neg 174)] :=
  (lex_12_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.neg 186), (Sat.Literal.neg 174), (Sat.Literal.pos 4743)] :=
  (lex_12_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4742), (Sat.Literal.pos 186), (Sat.Literal.pos 174), (Sat.Literal.pos 4743)] :=
  (lex_12_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4743) = lexBefore s permutation12 185 := by
  exact (positive_lex_of_descriptor s 4743 permutation12 186 (by rfl)).trans ((lex_skipped s permutation12 185 186 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation12 185) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation12 185 by rw [image12_eq]; rfl))

theorem lex_12_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4744) (Sat.Literal.pos 4743) (Sat.Literal.pos 185) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation12 185 (assignment s)
    (Sat.Literal.pos 4744) (Sat.Literal.pos 4743) (Sat.Literal.pos 185) (Sat.Literal.pos 110) (positive_of_descriptor s 4744 (.lex permutation12 185) (by rfl)) (lex_12_185_prefix s) (positive_select s 185) (lex_12_185_image s)

theorem lex_12_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.pos 185), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation12 185 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4743) (Sat.Literal.pos 185) (Sat.Literal.pos 110) (lex_12_185_prefix s) (positive_select s 185) (lex_12_185_image s)

theorem lex_12_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.pos 4743)] :=
  (lex_12_185_gate s).prop _ (List.Mem.head _)

theorem lex_12_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.neg 185), (Sat.Literal.pos 110)] :=
  (lex_12_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.pos 185), (Sat.Literal.neg 110)] :=
  (lex_12_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.neg 185), (Sat.Literal.neg 110), (Sat.Literal.pos 4744)] :=
  (lex_12_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4743), (Sat.Literal.pos 185), (Sat.Literal.pos 110), (Sat.Literal.pos 4744)] :=
  (lex_12_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4744) = lexBefore s permutation12 184 := by
  exact (positive_lex_of_descriptor s 4744 permutation12 185 (by rfl)).trans ((lex_skipped s permutation12 184 185 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation12 184) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation12 184 by rw [image12_eq]; rfl))

theorem lex_12_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4745) (Sat.Literal.pos 4744) (Sat.Literal.pos 184) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation12 184 (assignment s)
    (Sat.Literal.pos 4745) (Sat.Literal.pos 4744) (Sat.Literal.pos 184) (Sat.Literal.pos 46) (positive_of_descriptor s 4745 (.lex permutation12 184) (by rfl)) (lex_12_184_prefix s) (positive_select s 184) (lex_12_184_image s)

theorem lex_12_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.pos 184), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation12 184 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4744) (Sat.Literal.pos 184) (Sat.Literal.pos 46) (lex_12_184_prefix s) (positive_select s 184) (lex_12_184_image s)

theorem lex_12_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.pos 4744)] :=
  (lex_12_184_gate s).prop _ (List.Mem.head _)

theorem lex_12_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.neg 184), (Sat.Literal.pos 46)] :=
  (lex_12_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.pos 184), (Sat.Literal.neg 46)] :=
  (lex_12_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.neg 184), (Sat.Literal.neg 46), (Sat.Literal.pos 4745)] :=
  (lex_12_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4744), (Sat.Literal.pos 184), (Sat.Literal.pos 46), (Sat.Literal.pos 4745)] :=
  (lex_12_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4745) = lexBefore s permutation12 183 := by
  exact (positive_lex_of_descriptor s 4745 permutation12 184 (by rfl)).trans ((lex_skipped s permutation12 183 184 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation12 183) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation12 183 by rw [image12_eq]; rfl))

theorem lex_12_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4746) (Sat.Literal.pos 4745) (Sat.Literal.pos 183) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation12 183 (assignment s)
    (Sat.Literal.pos 4746) (Sat.Literal.pos 4745) (Sat.Literal.pos 183) (Sat.Literal.pos 237) (positive_of_descriptor s 4746 (.lex permutation12 183) (by rfl)) (lex_12_183_prefix s) (positive_select s 183) (lex_12_183_image s)

theorem lex_12_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.pos 183), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation12 183 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4745) (Sat.Literal.pos 183) (Sat.Literal.pos 237) (lex_12_183_prefix s) (positive_select s 183) (lex_12_183_image s)

theorem lex_12_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.pos 4745)] :=
  (lex_12_183_gate s).prop _ (List.Mem.head _)

theorem lex_12_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.neg 183), (Sat.Literal.pos 237)] :=
  (lex_12_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.pos 183), (Sat.Literal.neg 237)] :=
  (lex_12_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.neg 183), (Sat.Literal.neg 237), (Sat.Literal.pos 4746)] :=
  (lex_12_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4745), (Sat.Literal.pos 183), (Sat.Literal.pos 237), (Sat.Literal.pos 4746)] :=
  (lex_12_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4746) = lexBefore s permutation12 182 := by
  exact (positive_lex_of_descriptor s 4746 permutation12 183 (by rfl)).trans ((lex_skipped s permutation12 182 183 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation12 182) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation12 182 by rw [image12_eq]; rfl))

theorem lex_12_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4747) (Sat.Literal.pos 4746) (Sat.Literal.pos 182) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation12 182 (assignment s)
    (Sat.Literal.pos 4747) (Sat.Literal.pos 4746) (Sat.Literal.pos 182) (Sat.Literal.pos 173) (positive_of_descriptor s 4747 (.lex permutation12 182) (by rfl)) (lex_12_182_prefix s) (positive_select s 182) (lex_12_182_image s)

theorem lex_12_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.pos 182), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation12 182 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4746) (Sat.Literal.pos 182) (Sat.Literal.pos 173) (lex_12_182_prefix s) (positive_select s 182) (lex_12_182_image s)

theorem lex_12_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.pos 4746)] :=
  (lex_12_182_gate s).prop _ (List.Mem.head _)

theorem lex_12_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.neg 182), (Sat.Literal.pos 173)] :=
  (lex_12_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.pos 182), (Sat.Literal.neg 173)] :=
  (lex_12_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.neg 182), (Sat.Literal.neg 173), (Sat.Literal.pos 4747)] :=
  (lex_12_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4746), (Sat.Literal.pos 182), (Sat.Literal.pos 173), (Sat.Literal.pos 4747)] :=
  (lex_12_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4747) = lexBefore s permutation12 181 := by
  exact (positive_lex_of_descriptor s 4747 permutation12 182 (by rfl)).trans ((lex_skipped s permutation12 181 182 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation12 181) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation12 181 by rw [image12_eq]; rfl))

theorem lex_12_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4748) (Sat.Literal.pos 4747) (Sat.Literal.pos 181) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation12 181 (assignment s)
    (Sat.Literal.pos 4748) (Sat.Literal.pos 4747) (Sat.Literal.pos 181) (Sat.Literal.pos 109) (positive_of_descriptor s 4748 (.lex permutation12 181) (by rfl)) (lex_12_181_prefix s) (positive_select s 181) (lex_12_181_image s)

theorem lex_12_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.pos 181), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation12 181 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4747) (Sat.Literal.pos 181) (Sat.Literal.pos 109) (lex_12_181_prefix s) (positive_select s 181) (lex_12_181_image s)

theorem lex_12_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.pos 4747)] :=
  (lex_12_181_gate s).prop _ (List.Mem.head _)

theorem lex_12_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.neg 181), (Sat.Literal.pos 109)] :=
  (lex_12_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.pos 181), (Sat.Literal.neg 109)] :=
  (lex_12_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.neg 181), (Sat.Literal.neg 109), (Sat.Literal.pos 4748)] :=
  (lex_12_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4747), (Sat.Literal.pos 181), (Sat.Literal.pos 109), (Sat.Literal.pos 4748)] :=
  (lex_12_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4748) = lexBefore s permutation12 180 := by
  exact (positive_lex_of_descriptor s 4748 permutation12 181 (by rfl)).trans ((lex_skipped s permutation12 180 181 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation12 180) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation12 180 by rw [image12_eq]; rfl))

theorem lex_12_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4749) (Sat.Literal.pos 4748) (Sat.Literal.pos 180) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation12 180 (assignment s)
    (Sat.Literal.pos 4749) (Sat.Literal.pos 4748) (Sat.Literal.pos 180) (Sat.Literal.pos 45) (positive_of_descriptor s 4749 (.lex permutation12 180) (by rfl)) (lex_12_180_prefix s) (positive_select s 180) (lex_12_180_image s)

theorem lex_12_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.pos 180), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation12 180 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4748) (Sat.Literal.pos 180) (Sat.Literal.pos 45) (lex_12_180_prefix s) (positive_select s 180) (lex_12_180_image s)

theorem lex_12_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.pos 4748)] :=
  (lex_12_180_gate s).prop _ (List.Mem.head _)

theorem lex_12_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.neg 180), (Sat.Literal.pos 45)] :=
  (lex_12_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.pos 180), (Sat.Literal.neg 45)] :=
  (lex_12_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.neg 180), (Sat.Literal.neg 45), (Sat.Literal.pos 4749)] :=
  (lex_12_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4748), (Sat.Literal.pos 180), (Sat.Literal.pos 45), (Sat.Literal.pos 4749)] :=
  (lex_12_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4749) = lexBefore s permutation12 179 := by
  exact (positive_lex_of_descriptor s 4749 permutation12 180 (by rfl)).trans ((lex_skipped s permutation12 179 180 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation12 179) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation12 179 by rw [image12_eq]; rfl))

theorem lex_12_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4750) (Sat.Literal.pos 4749) (Sat.Literal.pos 179) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation12 179 (assignment s)
    (Sat.Literal.pos 4750) (Sat.Literal.pos 4749) (Sat.Literal.pos 179) (Sat.Literal.pos 236) (positive_of_descriptor s 4750 (.lex permutation12 179) (by rfl)) (lex_12_179_prefix s) (positive_select s 179) (lex_12_179_image s)

theorem lex_12_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.pos 179), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation12 179 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4749) (Sat.Literal.pos 179) (Sat.Literal.pos 236) (lex_12_179_prefix s) (positive_select s 179) (lex_12_179_image s)

theorem lex_12_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.pos 4749)] :=
  (lex_12_179_gate s).prop _ (List.Mem.head _)

theorem lex_12_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.neg 179), (Sat.Literal.pos 236)] :=
  (lex_12_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.pos 179), (Sat.Literal.neg 236)] :=
  (lex_12_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.neg 179), (Sat.Literal.neg 236), (Sat.Literal.pos 4750)] :=
  (lex_12_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4749), (Sat.Literal.pos 179), (Sat.Literal.pos 236), (Sat.Literal.pos 4750)] :=
  (lex_12_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4750) = lexBefore s permutation12 178 := by
  exact (positive_lex_of_descriptor s 4750 permutation12 179 (by rfl)).trans ((lex_skipped s permutation12 178 179 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation12 178) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation12 178 by rw [image12_eq]; rfl))

theorem lex_12_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4751) (Sat.Literal.pos 4750) (Sat.Literal.pos 178) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation12 178 (assignment s)
    (Sat.Literal.pos 4751) (Sat.Literal.pos 4750) (Sat.Literal.pos 178) (Sat.Literal.pos 172) (positive_of_descriptor s 4751 (.lex permutation12 178) (by rfl)) (lex_12_178_prefix s) (positive_select s 178) (lex_12_178_image s)

theorem lex_12_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.pos 178), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation12 178 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4750) (Sat.Literal.pos 178) (Sat.Literal.pos 172) (lex_12_178_prefix s) (positive_select s 178) (lex_12_178_image s)

theorem lex_12_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.pos 4750)] :=
  (lex_12_178_gate s).prop _ (List.Mem.head _)

theorem lex_12_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.neg 178), (Sat.Literal.pos 172)] :=
  (lex_12_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.pos 178), (Sat.Literal.neg 172)] :=
  (lex_12_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.neg 178), (Sat.Literal.neg 172), (Sat.Literal.pos 4751)] :=
  (lex_12_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4750), (Sat.Literal.pos 178), (Sat.Literal.pos 172), (Sat.Literal.pos 4751)] :=
  (lex_12_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4751) = lexBefore s permutation12 177 := by
  exact (positive_lex_of_descriptor s 4751 permutation12 178 (by rfl)).trans ((lex_skipped s permutation12 177 178 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation12 177) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation12 177 by rw [image12_eq]; rfl))

theorem lex_12_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4752) (Sat.Literal.pos 4751) (Sat.Literal.pos 177) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation12 177 (assignment s)
    (Sat.Literal.pos 4752) (Sat.Literal.pos 4751) (Sat.Literal.pos 177) (Sat.Literal.pos 108) (positive_of_descriptor s 4752 (.lex permutation12 177) (by rfl)) (lex_12_177_prefix s) (positive_select s 177) (lex_12_177_image s)

theorem lex_12_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.pos 177), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation12 177 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4751) (Sat.Literal.pos 177) (Sat.Literal.pos 108) (lex_12_177_prefix s) (positive_select s 177) (lex_12_177_image s)

theorem lex_12_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.pos 4751)] :=
  (lex_12_177_gate s).prop _ (List.Mem.head _)

theorem lex_12_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.neg 177), (Sat.Literal.pos 108)] :=
  (lex_12_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.pos 177), (Sat.Literal.neg 108)] :=
  (lex_12_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.neg 177), (Sat.Literal.neg 108), (Sat.Literal.pos 4752)] :=
  (lex_12_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4751), (Sat.Literal.pos 177), (Sat.Literal.pos 108), (Sat.Literal.pos 4752)] :=
  (lex_12_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4752) = lexBefore s permutation12 176 := by
  exact (positive_lex_of_descriptor s 4752 permutation12 177 (by rfl)).trans ((lex_skipped s permutation12 176 177 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation12 176) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation12 176 by rw [image12_eq]; rfl))

theorem lex_12_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4753) (Sat.Literal.pos 4752) (Sat.Literal.pos 176) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation12 176 (assignment s)
    (Sat.Literal.pos 4753) (Sat.Literal.pos 4752) (Sat.Literal.pos 176) (Sat.Literal.pos 44) (positive_of_descriptor s 4753 (.lex permutation12 176) (by rfl)) (lex_12_176_prefix s) (positive_select s 176) (lex_12_176_image s)

theorem lex_12_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.pos 176), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation12 176 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4752) (Sat.Literal.pos 176) (Sat.Literal.pos 44) (lex_12_176_prefix s) (positive_select s 176) (lex_12_176_image s)

theorem lex_12_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.pos 4752)] :=
  (lex_12_176_gate s).prop _ (List.Mem.head _)

theorem lex_12_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.neg 176), (Sat.Literal.pos 44)] :=
  (lex_12_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.pos 176), (Sat.Literal.neg 44)] :=
  (lex_12_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.neg 176), (Sat.Literal.neg 44), (Sat.Literal.pos 4753)] :=
  (lex_12_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4752), (Sat.Literal.pos 176), (Sat.Literal.pos 44), (Sat.Literal.pos 4753)] :=
  (lex_12_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4753) = lexBefore s permutation12 175 := by
  exact (positive_lex_of_descriptor s 4753 permutation12 176 (by rfl)).trans ((lex_skipped s permutation12 175 176 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation12 175) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation12 175 by rw [image12_eq]; rfl))

theorem lex_12_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4754) (Sat.Literal.pos 4753) (Sat.Literal.pos 175) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation12 175 (assignment s)
    (Sat.Literal.pos 4754) (Sat.Literal.pos 4753) (Sat.Literal.pos 175) (Sat.Literal.pos 235) (positive_of_descriptor s 4754 (.lex permutation12 175) (by rfl)) (lex_12_175_prefix s) (positive_select s 175) (lex_12_175_image s)

theorem lex_12_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.pos 175), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation12 175 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4753) (Sat.Literal.pos 175) (Sat.Literal.pos 235) (lex_12_175_prefix s) (positive_select s 175) (lex_12_175_image s)

theorem lex_12_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.pos 4753)] :=
  (lex_12_175_gate s).prop _ (List.Mem.head _)

theorem lex_12_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.neg 175), (Sat.Literal.pos 235)] :=
  (lex_12_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.pos 175), (Sat.Literal.neg 235)] :=
  (lex_12_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.neg 175), (Sat.Literal.neg 235), (Sat.Literal.pos 4754)] :=
  (lex_12_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4753), (Sat.Literal.pos 175), (Sat.Literal.pos 235), (Sat.Literal.pos 4754)] :=
  (lex_12_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4754) = lexBefore s permutation12 174 := by
  exact (positive_lex_of_descriptor s 4754 permutation12 175 (by rfl)).trans ((lex_skipped s permutation12 174 175 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation12 174) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation12 174 by rw [image12_eq]; rfl))

theorem lex_12_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4755) (Sat.Literal.pos 4754) (Sat.Literal.pos 174) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation12 174 (assignment s)
    (Sat.Literal.pos 4755) (Sat.Literal.pos 4754) (Sat.Literal.pos 174) (Sat.Literal.pos 171) (positive_of_descriptor s 4755 (.lex permutation12 174) (by rfl)) (lex_12_174_prefix s) (positive_select s 174) (lex_12_174_image s)

theorem lex_12_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.pos 174), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation12 174 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4754) (Sat.Literal.pos 174) (Sat.Literal.pos 171) (lex_12_174_prefix s) (positive_select s 174) (lex_12_174_image s)

theorem lex_12_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.pos 4754)] :=
  (lex_12_174_gate s).prop _ (List.Mem.head _)

theorem lex_12_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.neg 174), (Sat.Literal.pos 171)] :=
  (lex_12_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.pos 174), (Sat.Literal.neg 171)] :=
  (lex_12_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.neg 174), (Sat.Literal.neg 171), (Sat.Literal.pos 4755)] :=
  (lex_12_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4754), (Sat.Literal.pos 174), (Sat.Literal.pos 171), (Sat.Literal.pos 4755)] :=
  (lex_12_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4755) = lexBefore s permutation12 173 := by
  exact (positive_lex_of_descriptor s 4755 permutation12 174 (by rfl)).trans ((lex_skipped s permutation12 173 174 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation12 173) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation12 173 by rw [image12_eq]; rfl))

theorem lex_12_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4756) (Sat.Literal.pos 4755) (Sat.Literal.pos 173) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation12 173 (assignment s)
    (Sat.Literal.pos 4756) (Sat.Literal.pos 4755) (Sat.Literal.pos 173) (Sat.Literal.pos 107) (positive_of_descriptor s 4756 (.lex permutation12 173) (by rfl)) (lex_12_173_prefix s) (positive_select s 173) (lex_12_173_image s)

theorem lex_12_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.pos 173), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation12 173 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4755) (Sat.Literal.pos 173) (Sat.Literal.pos 107) (lex_12_173_prefix s) (positive_select s 173) (lex_12_173_image s)

theorem lex_12_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.pos 4755)] :=
  (lex_12_173_gate s).prop _ (List.Mem.head _)

theorem lex_12_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.neg 173), (Sat.Literal.pos 107)] :=
  (lex_12_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.pos 173), (Sat.Literal.neg 107)] :=
  (lex_12_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.neg 173), (Sat.Literal.neg 107), (Sat.Literal.pos 4756)] :=
  (lex_12_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4755), (Sat.Literal.pos 173), (Sat.Literal.pos 107), (Sat.Literal.pos 4756)] :=
  (lex_12_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4756) = lexBefore s permutation12 172 := by
  exact (positive_lex_of_descriptor s 4756 permutation12 173 (by rfl)).trans ((lex_skipped s permutation12 172 173 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation12 172) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation12 172 by rw [image12_eq]; rfl))

theorem lex_12_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4757) (Sat.Literal.pos 4756) (Sat.Literal.pos 172) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation12 172 (assignment s)
    (Sat.Literal.pos 4757) (Sat.Literal.pos 4756) (Sat.Literal.pos 172) (Sat.Literal.pos 43) (positive_of_descriptor s 4757 (.lex permutation12 172) (by rfl)) (lex_12_172_prefix s) (positive_select s 172) (lex_12_172_image s)

theorem lex_12_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.pos 172), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation12 172 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4756) (Sat.Literal.pos 172) (Sat.Literal.pos 43) (lex_12_172_prefix s) (positive_select s 172) (lex_12_172_image s)

theorem lex_12_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.pos 4756)] :=
  (lex_12_172_gate s).prop _ (List.Mem.head _)

theorem lex_12_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.neg 172), (Sat.Literal.pos 43)] :=
  (lex_12_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.pos 172), (Sat.Literal.neg 43)] :=
  (lex_12_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.neg 172), (Sat.Literal.neg 43), (Sat.Literal.pos 4757)] :=
  (lex_12_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4756), (Sat.Literal.pos 172), (Sat.Literal.pos 43), (Sat.Literal.pos 4757)] :=
  (lex_12_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4757) = lexBefore s permutation12 171 := by
  exact (positive_lex_of_descriptor s 4757 permutation12 172 (by rfl)).trans ((lex_skipped s permutation12 171 172 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation12 171) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation12 171 by rw [image12_eq]; rfl))

theorem lex_12_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4758) (Sat.Literal.pos 4757) (Sat.Literal.pos 171) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation12 171 (assignment s)
    (Sat.Literal.pos 4758) (Sat.Literal.pos 4757) (Sat.Literal.pos 171) (Sat.Literal.pos 234) (positive_of_descriptor s 4758 (.lex permutation12 171) (by rfl)) (lex_12_171_prefix s) (positive_select s 171) (lex_12_171_image s)

theorem lex_12_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.pos 171), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation12 171 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4757) (Sat.Literal.pos 171) (Sat.Literal.pos 234) (lex_12_171_prefix s) (positive_select s 171) (lex_12_171_image s)

theorem lex_12_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.pos 4757)] :=
  (lex_12_171_gate s).prop _ (List.Mem.head _)

theorem lex_12_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.neg 171), (Sat.Literal.pos 234)] :=
  (lex_12_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.pos 171), (Sat.Literal.neg 234)] :=
  (lex_12_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.neg 171), (Sat.Literal.neg 234), (Sat.Literal.pos 4758)] :=
  (lex_12_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4757), (Sat.Literal.pos 171), (Sat.Literal.pos 234), (Sat.Literal.pos 4758)] :=
  (lex_12_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4758) = lexBefore s permutation12 169 := by
  exact (positive_lex_of_descriptor s 4758 permutation12 171 (by rfl)).trans ((lex_skipped s permutation12 169 171 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 170 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation12 169) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation12 169 by rw [image12_eq]; rfl))

theorem lex_12_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4759) (Sat.Literal.pos 4758) (Sat.Literal.pos 169) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation12 169 (assignment s)
    (Sat.Literal.pos 4759) (Sat.Literal.pos 4758) (Sat.Literal.pos 169) (Sat.Literal.pos 106) (positive_of_descriptor s 4759 (.lex permutation12 169) (by rfl)) (lex_12_169_prefix s) (positive_select s 169) (lex_12_169_image s)

theorem lex_12_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.pos 169), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation12 169 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4758) (Sat.Literal.pos 169) (Sat.Literal.pos 106) (lex_12_169_prefix s) (positive_select s 169) (lex_12_169_image s)

theorem lex_12_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.pos 4758)] :=
  (lex_12_169_gate s).prop _ (List.Mem.head _)

theorem lex_12_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.neg 169), (Sat.Literal.pos 106)] :=
  (lex_12_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.pos 169), (Sat.Literal.neg 106)] :=
  (lex_12_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.neg 169), (Sat.Literal.neg 106), (Sat.Literal.pos 4759)] :=
  (lex_12_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4758), (Sat.Literal.pos 169), (Sat.Literal.pos 106), (Sat.Literal.pos 4759)] :=
  (lex_12_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4759) = lexBefore s permutation12 168 := by
  exact (positive_lex_of_descriptor s 4759 permutation12 169 (by rfl)).trans ((lex_skipped s permutation12 168 169 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation12 168) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation12 168 by rw [image12_eq]; rfl))

theorem lex_12_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4760) (Sat.Literal.pos 4759) (Sat.Literal.pos 168) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation12 168 (assignment s)
    (Sat.Literal.pos 4760) (Sat.Literal.pos 4759) (Sat.Literal.pos 168) (Sat.Literal.pos 42) (positive_of_descriptor s 4760 (.lex permutation12 168) (by rfl)) (lex_12_168_prefix s) (positive_select s 168) (lex_12_168_image s)

theorem lex_12_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.pos 168), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation12 168 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4759) (Sat.Literal.pos 168) (Sat.Literal.pos 42) (lex_12_168_prefix s) (positive_select s 168) (lex_12_168_image s)

theorem lex_12_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.pos 4759)] :=
  (lex_12_168_gate s).prop _ (List.Mem.head _)

theorem lex_12_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.neg 168), (Sat.Literal.pos 42)] :=
  (lex_12_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.pos 168), (Sat.Literal.neg 42)] :=
  (lex_12_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.neg 168), (Sat.Literal.neg 42), (Sat.Literal.pos 4760)] :=
  (lex_12_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4759), (Sat.Literal.pos 168), (Sat.Literal.pos 42), (Sat.Literal.pos 4760)] :=
  (lex_12_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4760) = lexBefore s permutation12 167 := by
  exact (positive_lex_of_descriptor s 4760 permutation12 168 (by rfl)).trans ((lex_skipped s permutation12 167 168 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation12 167) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation12 167 by rw [image12_eq]; rfl))

theorem lex_12_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4761) (Sat.Literal.pos 4760) (Sat.Literal.pos 167) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation12 167 (assignment s)
    (Sat.Literal.pos 4761) (Sat.Literal.pos 4760) (Sat.Literal.pos 167) (Sat.Literal.pos 233) (positive_of_descriptor s 4761 (.lex permutation12 167) (by rfl)) (lex_12_167_prefix s) (positive_select s 167) (lex_12_167_image s)

theorem lex_12_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.pos 167), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation12 167 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4760) (Sat.Literal.pos 167) (Sat.Literal.pos 233) (lex_12_167_prefix s) (positive_select s 167) (lex_12_167_image s)

theorem lex_12_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.pos 4760)] :=
  (lex_12_167_gate s).prop _ (List.Mem.head _)

theorem lex_12_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.neg 167), (Sat.Literal.pos 233)] :=
  (lex_12_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.pos 167), (Sat.Literal.neg 233)] :=
  (lex_12_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.neg 167), (Sat.Literal.neg 233), (Sat.Literal.pos 4761)] :=
  (lex_12_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4760), (Sat.Literal.pos 167), (Sat.Literal.pos 233), (Sat.Literal.pos 4761)] :=
  (lex_12_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4761) = lexBefore s permutation12 166 := by
  exact (positive_lex_of_descriptor s 4761 permutation12 167 (by rfl)).trans ((lex_skipped s permutation12 166 167 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation12 166) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation12 166 by rw [image12_eq]; rfl))

theorem lex_12_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4762) (Sat.Literal.pos 4761) (Sat.Literal.pos 166) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation12 166 (assignment s)
    (Sat.Literal.pos 4762) (Sat.Literal.pos 4761) (Sat.Literal.pos 166) (Sat.Literal.pos 169) (positive_of_descriptor s 4762 (.lex permutation12 166) (by rfl)) (lex_12_166_prefix s) (positive_select s 166) (lex_12_166_image s)

theorem lex_12_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.pos 166), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation12 166 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4761) (Sat.Literal.pos 166) (Sat.Literal.pos 169) (lex_12_166_prefix s) (positive_select s 166) (lex_12_166_image s)

theorem lex_12_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.pos 4761)] :=
  (lex_12_166_gate s).prop _ (List.Mem.head _)

theorem lex_12_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.neg 166), (Sat.Literal.pos 169)] :=
  (lex_12_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.pos 166), (Sat.Literal.neg 169)] :=
  (lex_12_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.neg 166), (Sat.Literal.neg 169), (Sat.Literal.pos 4762)] :=
  (lex_12_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4761), (Sat.Literal.pos 166), (Sat.Literal.pos 169), (Sat.Literal.pos 4762)] :=
  (lex_12_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4762) = lexBefore s permutation12 165 := by
  exact (positive_lex_of_descriptor s 4762 permutation12 166 (by rfl)).trans ((lex_skipped s permutation12 165 166 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation12 165) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation12 165 by rw [image12_eq]; rfl))

theorem lex_12_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4763) (Sat.Literal.pos 4762) (Sat.Literal.pos 165) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation12 165 (assignment s)
    (Sat.Literal.pos 4763) (Sat.Literal.pos 4762) (Sat.Literal.pos 165) (Sat.Literal.pos 105) (positive_of_descriptor s 4763 (.lex permutation12 165) (by rfl)) (lex_12_165_prefix s) (positive_select s 165) (lex_12_165_image s)

theorem lex_12_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.pos 165), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation12 165 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4762) (Sat.Literal.pos 165) (Sat.Literal.pos 105) (lex_12_165_prefix s) (positive_select s 165) (lex_12_165_image s)

theorem lex_12_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.pos 4762)] :=
  (lex_12_165_gate s).prop _ (List.Mem.head _)

theorem lex_12_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.neg 165), (Sat.Literal.pos 105)] :=
  (lex_12_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.pos 165), (Sat.Literal.neg 105)] :=
  (lex_12_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.neg 165), (Sat.Literal.neg 105), (Sat.Literal.pos 4763)] :=
  (lex_12_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4762), (Sat.Literal.pos 165), (Sat.Literal.pos 105), (Sat.Literal.pos 4763)] :=
  (lex_12_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4763) = lexBefore s permutation12 164 := by
  exact (positive_lex_of_descriptor s 4763 permutation12 165 (by rfl)).trans ((lex_skipped s permutation12 164 165 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation12 164) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation12 164 by rw [image12_eq]; rfl))

theorem lex_12_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4764) (Sat.Literal.pos 4763) (Sat.Literal.pos 164) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation12 164 (assignment s)
    (Sat.Literal.pos 4764) (Sat.Literal.pos 4763) (Sat.Literal.pos 164) (Sat.Literal.pos 41) (positive_of_descriptor s 4764 (.lex permutation12 164) (by rfl)) (lex_12_164_prefix s) (positive_select s 164) (lex_12_164_image s)

theorem lex_12_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.pos 164), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation12 164 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4763) (Sat.Literal.pos 164) (Sat.Literal.pos 41) (lex_12_164_prefix s) (positive_select s 164) (lex_12_164_image s)

theorem lex_12_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.pos 4763)] :=
  (lex_12_164_gate s).prop _ (List.Mem.head _)

theorem lex_12_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.neg 164), (Sat.Literal.pos 41)] :=
  (lex_12_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.pos 164), (Sat.Literal.neg 41)] :=
  (lex_12_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.neg 164), (Sat.Literal.neg 41), (Sat.Literal.pos 4764)] :=
  (lex_12_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4763), (Sat.Literal.pos 164), (Sat.Literal.pos 41), (Sat.Literal.pos 4764)] :=
  (lex_12_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4764) = lexBefore s permutation12 163 := by
  exact (positive_lex_of_descriptor s 4764 permutation12 164 (by rfl)).trans ((lex_skipped s permutation12 163 164 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation12 163) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation12 163 by rw [image12_eq]; rfl))

theorem lex_12_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4765) (Sat.Literal.pos 4764) (Sat.Literal.pos 163) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation12 163 (assignment s)
    (Sat.Literal.pos 4765) (Sat.Literal.pos 4764) (Sat.Literal.pos 163) (Sat.Literal.pos 232) (positive_of_descriptor s 4765 (.lex permutation12 163) (by rfl)) (lex_12_163_prefix s) (positive_select s 163) (lex_12_163_image s)

theorem lex_12_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.pos 163), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation12 163 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4764) (Sat.Literal.pos 163) (Sat.Literal.pos 232) (lex_12_163_prefix s) (positive_select s 163) (lex_12_163_image s)

theorem lex_12_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.pos 4764)] :=
  (lex_12_163_gate s).prop _ (List.Mem.head _)

theorem lex_12_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.neg 163), (Sat.Literal.pos 232)] :=
  (lex_12_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.pos 163), (Sat.Literal.neg 232)] :=
  (lex_12_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.neg 163), (Sat.Literal.neg 232), (Sat.Literal.pos 4765)] :=
  (lex_12_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4764), (Sat.Literal.pos 163), (Sat.Literal.pos 232), (Sat.Literal.pos 4765)] :=
  (lex_12_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4765) = lexBefore s permutation12 162 := by
  exact (positive_lex_of_descriptor s 4765 permutation12 163 (by rfl)).trans ((lex_skipped s permutation12 162 163 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation12 162) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation12 162 by rw [image12_eq]; rfl))

theorem lex_12_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4766) (Sat.Literal.pos 4765) (Sat.Literal.pos 162) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation12 162 (assignment s)
    (Sat.Literal.pos 4766) (Sat.Literal.pos 4765) (Sat.Literal.pos 162) (Sat.Literal.pos 168) (positive_of_descriptor s 4766 (.lex permutation12 162) (by rfl)) (lex_12_162_prefix s) (positive_select s 162) (lex_12_162_image s)

theorem lex_12_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.pos 162), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation12 162 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4765) (Sat.Literal.pos 162) (Sat.Literal.pos 168) (lex_12_162_prefix s) (positive_select s 162) (lex_12_162_image s)

theorem lex_12_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.pos 4765)] :=
  (lex_12_162_gate s).prop _ (List.Mem.head _)

theorem lex_12_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.neg 162), (Sat.Literal.pos 168)] :=
  (lex_12_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.pos 162), (Sat.Literal.neg 168)] :=
  (lex_12_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.neg 162), (Sat.Literal.neg 168), (Sat.Literal.pos 4766)] :=
  (lex_12_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4765), (Sat.Literal.pos 162), (Sat.Literal.pos 168), (Sat.Literal.pos 4766)] :=
  (lex_12_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4766) = lexBefore s permutation12 161 := by
  exact (positive_lex_of_descriptor s 4766 permutation12 162 (by rfl)).trans ((lex_skipped s permutation12 161 162 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation12 161) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation12 161 by rw [image12_eq]; rfl))

theorem lex_12_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4767) (Sat.Literal.pos 4766) (Sat.Literal.pos 161) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation12 161 (assignment s)
    (Sat.Literal.pos 4767) (Sat.Literal.pos 4766) (Sat.Literal.pos 161) (Sat.Literal.pos 104) (positive_of_descriptor s 4767 (.lex permutation12 161) (by rfl)) (lex_12_161_prefix s) (positive_select s 161) (lex_12_161_image s)

theorem lex_12_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.pos 161), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation12 161 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4766) (Sat.Literal.pos 161) (Sat.Literal.pos 104) (lex_12_161_prefix s) (positive_select s 161) (lex_12_161_image s)

theorem lex_12_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.pos 4766)] :=
  (lex_12_161_gate s).prop _ (List.Mem.head _)

theorem lex_12_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.neg 161), (Sat.Literal.pos 104)] :=
  (lex_12_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.pos 161), (Sat.Literal.neg 104)] :=
  (lex_12_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.neg 161), (Sat.Literal.neg 104), (Sat.Literal.pos 4767)] :=
  (lex_12_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4766), (Sat.Literal.pos 161), (Sat.Literal.pos 104), (Sat.Literal.pos 4767)] :=
  (lex_12_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4767) = lexBefore s permutation12 160 := by
  exact (positive_lex_of_descriptor s 4767 permutation12 161 (by rfl)).trans ((lex_skipped s permutation12 160 161 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation12 160) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation12 160 by rw [image12_eq]; rfl))

theorem lex_12_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4768) (Sat.Literal.pos 4767) (Sat.Literal.pos 160) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation12 160 (assignment s)
    (Sat.Literal.pos 4768) (Sat.Literal.pos 4767) (Sat.Literal.pos 160) (Sat.Literal.pos 40) (positive_of_descriptor s 4768 (.lex permutation12 160) (by rfl)) (lex_12_160_prefix s) (positive_select s 160) (lex_12_160_image s)

theorem lex_12_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.pos 160), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation12 160 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4767) (Sat.Literal.pos 160) (Sat.Literal.pos 40) (lex_12_160_prefix s) (positive_select s 160) (lex_12_160_image s)

theorem lex_12_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.pos 4767)] :=
  (lex_12_160_gate s).prop _ (List.Mem.head _)

theorem lex_12_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.neg 160), (Sat.Literal.pos 40)] :=
  (lex_12_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.pos 160), (Sat.Literal.neg 40)] :=
  (lex_12_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.neg 160), (Sat.Literal.neg 40), (Sat.Literal.pos 4768)] :=
  (lex_12_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4767), (Sat.Literal.pos 160), (Sat.Literal.pos 40), (Sat.Literal.pos 4768)] :=
  (lex_12_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4768) = lexBefore s permutation12 159 := by
  exact (positive_lex_of_descriptor s 4768 permutation12 160 (by rfl)).trans ((lex_skipped s permutation12 159 160 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation12 159) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation12 159 by rw [image12_eq]; rfl))

theorem lex_12_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4769) (Sat.Literal.pos 4768) (Sat.Literal.pos 159) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation12 159 (assignment s)
    (Sat.Literal.pos 4769) (Sat.Literal.pos 4768) (Sat.Literal.pos 159) (Sat.Literal.pos 231) (positive_of_descriptor s 4769 (.lex permutation12 159) (by rfl)) (lex_12_159_prefix s) (positive_select s 159) (lex_12_159_image s)

theorem lex_12_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.pos 159), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation12 159 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4768) (Sat.Literal.pos 159) (Sat.Literal.pos 231) (lex_12_159_prefix s) (positive_select s 159) (lex_12_159_image s)

theorem lex_12_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.pos 4768)] :=
  (lex_12_159_gate s).prop _ (List.Mem.head _)

theorem lex_12_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.neg 159), (Sat.Literal.pos 231)] :=
  (lex_12_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.pos 159), (Sat.Literal.neg 231)] :=
  (lex_12_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.neg 159), (Sat.Literal.neg 231), (Sat.Literal.pos 4769)] :=
  (lex_12_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4768), (Sat.Literal.pos 159), (Sat.Literal.pos 231), (Sat.Literal.pos 4769)] :=
  (lex_12_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4769) = lexBefore s permutation12 158 := by
  exact (positive_lex_of_descriptor s 4769 permutation12 159 (by rfl)).trans ((lex_skipped s permutation12 158 159 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation12 158) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation12 158 by rw [image12_eq]; rfl))

theorem lex_12_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4770) (Sat.Literal.pos 4769) (Sat.Literal.pos 158) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation12 158 (assignment s)
    (Sat.Literal.pos 4770) (Sat.Literal.pos 4769) (Sat.Literal.pos 158) (Sat.Literal.pos 167) (positive_of_descriptor s 4770 (.lex permutation12 158) (by rfl)) (lex_12_158_prefix s) (positive_select s 158) (lex_12_158_image s)

theorem lex_12_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.pos 158), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation12 158 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4769) (Sat.Literal.pos 158) (Sat.Literal.pos 167) (lex_12_158_prefix s) (positive_select s 158) (lex_12_158_image s)

theorem lex_12_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.pos 4769)] :=
  (lex_12_158_gate s).prop _ (List.Mem.head _)

theorem lex_12_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.neg 158), (Sat.Literal.pos 167)] :=
  (lex_12_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.pos 158), (Sat.Literal.neg 167)] :=
  (lex_12_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.neg 158), (Sat.Literal.neg 167), (Sat.Literal.pos 4770)] :=
  (lex_12_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4769), (Sat.Literal.pos 158), (Sat.Literal.pos 167), (Sat.Literal.pos 4770)] :=
  (lex_12_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4770) = lexBefore s permutation12 157 := by
  exact (positive_lex_of_descriptor s 4770 permutation12 158 (by rfl)).trans ((lex_skipped s permutation12 157 158 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation12 157) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation12 157 by rw [image12_eq]; rfl))

theorem lex_12_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4771) (Sat.Literal.pos 4770) (Sat.Literal.pos 157) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation12 157 (assignment s)
    (Sat.Literal.pos 4771) (Sat.Literal.pos 4770) (Sat.Literal.pos 157) (Sat.Literal.pos 103) (positive_of_descriptor s 4771 (.lex permutation12 157) (by rfl)) (lex_12_157_prefix s) (positive_select s 157) (lex_12_157_image s)

theorem lex_12_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.pos 157), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation12 157 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4770) (Sat.Literal.pos 157) (Sat.Literal.pos 103) (lex_12_157_prefix s) (positive_select s 157) (lex_12_157_image s)

theorem lex_12_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.pos 4770)] :=
  (lex_12_157_gate s).prop _ (List.Mem.head _)

theorem lex_12_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.neg 157), (Sat.Literal.pos 103)] :=
  (lex_12_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.pos 157), (Sat.Literal.neg 103)] :=
  (lex_12_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.neg 157), (Sat.Literal.neg 103), (Sat.Literal.pos 4771)] :=
  (lex_12_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4770), (Sat.Literal.pos 157), (Sat.Literal.pos 103), (Sat.Literal.pos 4771)] :=
  (lex_12_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4771) = lexBefore s permutation12 156 := by
  exact (positive_lex_of_descriptor s 4771 permutation12 157 (by rfl)).trans ((lex_skipped s permutation12 156 157 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation12 156) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation12 156 by rw [image12_eq]; rfl))

theorem lex_12_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4772) (Sat.Literal.pos 4771) (Sat.Literal.pos 156) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation12 156 (assignment s)
    (Sat.Literal.pos 4772) (Sat.Literal.pos 4771) (Sat.Literal.pos 156) (Sat.Literal.pos 39) (positive_of_descriptor s 4772 (.lex permutation12 156) (by rfl)) (lex_12_156_prefix s) (positive_select s 156) (lex_12_156_image s)

theorem lex_12_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.pos 156), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation12 156 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4771) (Sat.Literal.pos 156) (Sat.Literal.pos 39) (lex_12_156_prefix s) (positive_select s 156) (lex_12_156_image s)

theorem lex_12_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.pos 4771)] :=
  (lex_12_156_gate s).prop _ (List.Mem.head _)

theorem lex_12_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.neg 156), (Sat.Literal.pos 39)] :=
  (lex_12_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.pos 156), (Sat.Literal.neg 39)] :=
  (lex_12_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.neg 156), (Sat.Literal.neg 39), (Sat.Literal.pos 4772)] :=
  (lex_12_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4771), (Sat.Literal.pos 156), (Sat.Literal.pos 39), (Sat.Literal.pos 4772)] :=
  (lex_12_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4772) = lexBefore s permutation12 155 := by
  exact (positive_lex_of_descriptor s 4772 permutation12 156 (by rfl)).trans ((lex_skipped s permutation12 155 156 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation12 155) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation12 155 by rw [image12_eq]; rfl))

theorem lex_12_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4773) (Sat.Literal.pos 4772) (Sat.Literal.pos 155) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation12 155 (assignment s)
    (Sat.Literal.pos 4773) (Sat.Literal.pos 4772) (Sat.Literal.pos 155) (Sat.Literal.pos 230) (positive_of_descriptor s 4773 (.lex permutation12 155) (by rfl)) (lex_12_155_prefix s) (positive_select s 155) (lex_12_155_image s)

theorem lex_12_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.pos 155), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation12 155 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4772) (Sat.Literal.pos 155) (Sat.Literal.pos 230) (lex_12_155_prefix s) (positive_select s 155) (lex_12_155_image s)

theorem lex_12_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.pos 4772)] :=
  (lex_12_155_gate s).prop _ (List.Mem.head _)

theorem lex_12_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.neg 155), (Sat.Literal.pos 230)] :=
  (lex_12_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.pos 155), (Sat.Literal.neg 230)] :=
  (lex_12_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.neg 155), (Sat.Literal.neg 230), (Sat.Literal.pos 4773)] :=
  (lex_12_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4772), (Sat.Literal.pos 155), (Sat.Literal.pos 230), (Sat.Literal.pos 4773)] :=
  (lex_12_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4773) = lexBefore s permutation12 154 := by
  exact (positive_lex_of_descriptor s 4773 permutation12 155 (by rfl)).trans ((lex_skipped s permutation12 154 155 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation12 154) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation12 154 by rw [image12_eq]; rfl))

theorem lex_12_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4774) (Sat.Literal.pos 4773) (Sat.Literal.pos 154) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation12 154 (assignment s)
    (Sat.Literal.pos 4774) (Sat.Literal.pos 4773) (Sat.Literal.pos 154) (Sat.Literal.pos 166) (positive_of_descriptor s 4774 (.lex permutation12 154) (by rfl)) (lex_12_154_prefix s) (positive_select s 154) (lex_12_154_image s)

theorem lex_12_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.pos 154), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation12 154 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4773) (Sat.Literal.pos 154) (Sat.Literal.pos 166) (lex_12_154_prefix s) (positive_select s 154) (lex_12_154_image s)

theorem lex_12_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.pos 4773)] :=
  (lex_12_154_gate s).prop _ (List.Mem.head _)

theorem lex_12_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.neg 154), (Sat.Literal.pos 166)] :=
  (lex_12_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.pos 154), (Sat.Literal.neg 166)] :=
  (lex_12_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.neg 154), (Sat.Literal.neg 166), (Sat.Literal.pos 4774)] :=
  (lex_12_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4773), (Sat.Literal.pos 154), (Sat.Literal.pos 166), (Sat.Literal.pos 4774)] :=
  (lex_12_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4774) = lexBefore s permutation12 153 := by
  exact (positive_lex_of_descriptor s 4774 permutation12 154 (by rfl)).trans ((lex_skipped s permutation12 153 154 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation12 153) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation12 153 by rw [image12_eq]; rfl))

theorem lex_12_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4775) (Sat.Literal.pos 4774) (Sat.Literal.pos 153) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation12 153 (assignment s)
    (Sat.Literal.pos 4775) (Sat.Literal.pos 4774) (Sat.Literal.pos 153) (Sat.Literal.pos 102) (positive_of_descriptor s 4775 (.lex permutation12 153) (by rfl)) (lex_12_153_prefix s) (positive_select s 153) (lex_12_153_image s)

theorem lex_12_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.pos 153), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation12 153 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4774) (Sat.Literal.pos 153) (Sat.Literal.pos 102) (lex_12_153_prefix s) (positive_select s 153) (lex_12_153_image s)

theorem lex_12_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.pos 4774)] :=
  (lex_12_153_gate s).prop _ (List.Mem.head _)

theorem lex_12_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.neg 153), (Sat.Literal.pos 102)] :=
  (lex_12_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.pos 153), (Sat.Literal.neg 102)] :=
  (lex_12_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.neg 153), (Sat.Literal.neg 102), (Sat.Literal.pos 4775)] :=
  (lex_12_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4774), (Sat.Literal.pos 153), (Sat.Literal.pos 102), (Sat.Literal.pos 4775)] :=
  (lex_12_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4775) = lexBefore s permutation12 152 := by
  exact (positive_lex_of_descriptor s 4775 permutation12 153 (by rfl)).trans ((lex_skipped s permutation12 152 153 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation12 152) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation12 152 by rw [image12_eq]; rfl))

theorem lex_12_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4776) (Sat.Literal.pos 4775) (Sat.Literal.pos 152) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation12 152 (assignment s)
    (Sat.Literal.pos 4776) (Sat.Literal.pos 4775) (Sat.Literal.pos 152) (Sat.Literal.pos 38) (positive_of_descriptor s 4776 (.lex permutation12 152) (by rfl)) (lex_12_152_prefix s) (positive_select s 152) (lex_12_152_image s)

theorem lex_12_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.pos 152), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation12 152 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4775) (Sat.Literal.pos 152) (Sat.Literal.pos 38) (lex_12_152_prefix s) (positive_select s 152) (lex_12_152_image s)

theorem lex_12_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.pos 4775)] :=
  (lex_12_152_gate s).prop _ (List.Mem.head _)

theorem lex_12_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.neg 152), (Sat.Literal.pos 38)] :=
  (lex_12_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.pos 152), (Sat.Literal.neg 38)] :=
  (lex_12_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.neg 152), (Sat.Literal.neg 38), (Sat.Literal.pos 4776)] :=
  (lex_12_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4775), (Sat.Literal.pos 152), (Sat.Literal.pos 38), (Sat.Literal.pos 4776)] :=
  (lex_12_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4776) = lexBefore s permutation12 151 := by
  exact (positive_lex_of_descriptor s 4776 permutation12 152 (by rfl)).trans ((lex_skipped s permutation12 151 152 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation12 151) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation12 151 by rw [image12_eq]; rfl))

theorem lex_12_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4777) (Sat.Literal.pos 4776) (Sat.Literal.pos 151) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation12 151 (assignment s)
    (Sat.Literal.pos 4777) (Sat.Literal.pos 4776) (Sat.Literal.pos 151) (Sat.Literal.pos 229) (positive_of_descriptor s 4777 (.lex permutation12 151) (by rfl)) (lex_12_151_prefix s) (positive_select s 151) (lex_12_151_image s)

theorem lex_12_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.pos 151), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation12 151 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4776) (Sat.Literal.pos 151) (Sat.Literal.pos 229) (lex_12_151_prefix s) (positive_select s 151) (lex_12_151_image s)

theorem lex_12_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.pos 4776)] :=
  (lex_12_151_gate s).prop _ (List.Mem.head _)

theorem lex_12_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.neg 151), (Sat.Literal.pos 229)] :=
  (lex_12_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.pos 151), (Sat.Literal.neg 229)] :=
  (lex_12_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.neg 151), (Sat.Literal.neg 229), (Sat.Literal.pos 4777)] :=
  (lex_12_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4776), (Sat.Literal.pos 151), (Sat.Literal.pos 229), (Sat.Literal.pos 4777)] :=
  (lex_12_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4777) = lexBefore s permutation12 150 := by
  exact (positive_lex_of_descriptor s 4777 permutation12 151 (by rfl)).trans ((lex_skipped s permutation12 150 151 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation12 150) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation12 150 by rw [image12_eq]; rfl))

theorem lex_12_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4778) (Sat.Literal.pos 4777) (Sat.Literal.pos 150) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation12 150 (assignment s)
    (Sat.Literal.pos 4778) (Sat.Literal.pos 4777) (Sat.Literal.pos 150) (Sat.Literal.pos 165) (positive_of_descriptor s 4778 (.lex permutation12 150) (by rfl)) (lex_12_150_prefix s) (positive_select s 150) (lex_12_150_image s)

theorem lex_12_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.pos 150), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation12 150 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4777) (Sat.Literal.pos 150) (Sat.Literal.pos 165) (lex_12_150_prefix s) (positive_select s 150) (lex_12_150_image s)

theorem lex_12_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.pos 4777)] :=
  (lex_12_150_gate s).prop _ (List.Mem.head _)

theorem lex_12_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.neg 150), (Sat.Literal.pos 165)] :=
  (lex_12_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.pos 150), (Sat.Literal.neg 165)] :=
  (lex_12_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.neg 150), (Sat.Literal.neg 165), (Sat.Literal.pos 4778)] :=
  (lex_12_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4777), (Sat.Literal.pos 150), (Sat.Literal.pos 165), (Sat.Literal.pos 4778)] :=
  (lex_12_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4778) = lexBefore s permutation12 149 := by
  exact (positive_lex_of_descriptor s 4778 permutation12 150 (by rfl)).trans ((lex_skipped s permutation12 149 150 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation12 149) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation12 149 by rw [image12_eq]; rfl))

theorem lex_12_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4779) (Sat.Literal.pos 4778) (Sat.Literal.pos 149) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation12 149 (assignment s)
    (Sat.Literal.pos 4779) (Sat.Literal.pos 4778) (Sat.Literal.pos 149) (Sat.Literal.pos 101) (positive_of_descriptor s 4779 (.lex permutation12 149) (by rfl)) (lex_12_149_prefix s) (positive_select s 149) (lex_12_149_image s)

theorem lex_12_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.pos 149), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation12 149 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4778) (Sat.Literal.pos 149) (Sat.Literal.pos 101) (lex_12_149_prefix s) (positive_select s 149) (lex_12_149_image s)

theorem lex_12_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.pos 4778)] :=
  (lex_12_149_gate s).prop _ (List.Mem.head _)

theorem lex_12_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.neg 149), (Sat.Literal.pos 101)] :=
  (lex_12_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.pos 149), (Sat.Literal.neg 101)] :=
  (lex_12_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.neg 149), (Sat.Literal.neg 101), (Sat.Literal.pos 4779)] :=
  (lex_12_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4778), (Sat.Literal.pos 149), (Sat.Literal.pos 101), (Sat.Literal.pos 4779)] :=
  (lex_12_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4779) = lexBefore s permutation12 148 := by
  exact (positive_lex_of_descriptor s 4779 permutation12 149 (by rfl)).trans ((lex_skipped s permutation12 148 149 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation12 148) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation12 148 by rw [image12_eq]; rfl))

theorem lex_12_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4780) (Sat.Literal.pos 4779) (Sat.Literal.pos 148) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation12 148 (assignment s)
    (Sat.Literal.pos 4780) (Sat.Literal.pos 4779) (Sat.Literal.pos 148) (Sat.Literal.pos 37) (positive_of_descriptor s 4780 (.lex permutation12 148) (by rfl)) (lex_12_148_prefix s) (positive_select s 148) (lex_12_148_image s)

theorem lex_12_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.pos 148), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation12 148 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4779) (Sat.Literal.pos 148) (Sat.Literal.pos 37) (lex_12_148_prefix s) (positive_select s 148) (lex_12_148_image s)

theorem lex_12_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.pos 4779)] :=
  (lex_12_148_gate s).prop _ (List.Mem.head _)

theorem lex_12_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.neg 148), (Sat.Literal.pos 37)] :=
  (lex_12_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.pos 148), (Sat.Literal.neg 37)] :=
  (lex_12_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.neg 148), (Sat.Literal.neg 37), (Sat.Literal.pos 4780)] :=
  (lex_12_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4779), (Sat.Literal.pos 148), (Sat.Literal.pos 37), (Sat.Literal.pos 4780)] :=
  (lex_12_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4780) = lexBefore s permutation12 147 := by
  exact (positive_lex_of_descriptor s 4780 permutation12 148 (by rfl)).trans ((lex_skipped s permutation12 147 148 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation12 147) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation12 147 by rw [image12_eq]; rfl))

theorem lex_12_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4781) (Sat.Literal.pos 4780) (Sat.Literal.pos 147) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation12 147 (assignment s)
    (Sat.Literal.pos 4781) (Sat.Literal.pos 4780) (Sat.Literal.pos 147) (Sat.Literal.pos 228) (positive_of_descriptor s 4781 (.lex permutation12 147) (by rfl)) (lex_12_147_prefix s) (positive_select s 147) (lex_12_147_image s)

theorem lex_12_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.pos 147), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation12 147 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4780) (Sat.Literal.pos 147) (Sat.Literal.pos 228) (lex_12_147_prefix s) (positive_select s 147) (lex_12_147_image s)

theorem lex_12_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.pos 4780)] :=
  (lex_12_147_gate s).prop _ (List.Mem.head _)

theorem lex_12_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.neg 147), (Sat.Literal.pos 228)] :=
  (lex_12_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.pos 147), (Sat.Literal.neg 228)] :=
  (lex_12_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.neg 147), (Sat.Literal.neg 228), (Sat.Literal.pos 4781)] :=
  (lex_12_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4780), (Sat.Literal.pos 147), (Sat.Literal.pos 228), (Sat.Literal.pos 4781)] :=
  (lex_12_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4781) = lexBefore s permutation12 146 := by
  exact (positive_lex_of_descriptor s 4781 permutation12 147 (by rfl)).trans ((lex_skipped s permutation12 146 147 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation12 146) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation12 146 by rw [image12_eq]; rfl))

theorem lex_12_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4782) (Sat.Literal.pos 4781) (Sat.Literal.pos 146) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation12 146 (assignment s)
    (Sat.Literal.pos 4782) (Sat.Literal.pos 4781) (Sat.Literal.pos 146) (Sat.Literal.pos 164) (positive_of_descriptor s 4782 (.lex permutation12 146) (by rfl)) (lex_12_146_prefix s) (positive_select s 146) (lex_12_146_image s)

theorem lex_12_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.pos 146), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation12 146 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4781) (Sat.Literal.pos 146) (Sat.Literal.pos 164) (lex_12_146_prefix s) (positive_select s 146) (lex_12_146_image s)

theorem lex_12_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.pos 4781)] :=
  (lex_12_146_gate s).prop _ (List.Mem.head _)

theorem lex_12_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.neg 146), (Sat.Literal.pos 164)] :=
  (lex_12_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.pos 146), (Sat.Literal.neg 164)] :=
  (lex_12_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.neg 146), (Sat.Literal.neg 164), (Sat.Literal.pos 4782)] :=
  (lex_12_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4781), (Sat.Literal.pos 146), (Sat.Literal.pos 164), (Sat.Literal.pos 4782)] :=
  (lex_12_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4782) = lexBefore s permutation12 145 := by
  exact (positive_lex_of_descriptor s 4782 permutation12 146 (by rfl)).trans ((lex_skipped s permutation12 145 146 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation12 145) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation12 145 by rw [image12_eq]; rfl))

theorem lex_12_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4783) (Sat.Literal.pos 4782) (Sat.Literal.pos 145) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation12 145 (assignment s)
    (Sat.Literal.pos 4783) (Sat.Literal.pos 4782) (Sat.Literal.pos 145) (Sat.Literal.pos 100) (positive_of_descriptor s 4783 (.lex permutation12 145) (by rfl)) (lex_12_145_prefix s) (positive_select s 145) (lex_12_145_image s)

theorem lex_12_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.pos 145), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation12 145 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4782) (Sat.Literal.pos 145) (Sat.Literal.pos 100) (lex_12_145_prefix s) (positive_select s 145) (lex_12_145_image s)

theorem lex_12_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.pos 4782)] :=
  (lex_12_145_gate s).prop _ (List.Mem.head _)

theorem lex_12_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.neg 145), (Sat.Literal.pos 100)] :=
  (lex_12_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.pos 145), (Sat.Literal.neg 100)] :=
  (lex_12_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.neg 145), (Sat.Literal.neg 100), (Sat.Literal.pos 4783)] :=
  (lex_12_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4782), (Sat.Literal.pos 145), (Sat.Literal.pos 100), (Sat.Literal.pos 4783)] :=
  (lex_12_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4783) = lexBefore s permutation12 144 := by
  exact (positive_lex_of_descriptor s 4783 permutation12 145 (by rfl)).trans ((lex_skipped s permutation12 144 145 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation12 144) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation12 144 by rw [image12_eq]; rfl))

theorem lex_12_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4784) (Sat.Literal.pos 4783) (Sat.Literal.pos 144) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation12 144 (assignment s)
    (Sat.Literal.pos 4784) (Sat.Literal.pos 4783) (Sat.Literal.pos 144) (Sat.Literal.pos 36) (positive_of_descriptor s 4784 (.lex permutation12 144) (by rfl)) (lex_12_144_prefix s) (positive_select s 144) (lex_12_144_image s)

theorem lex_12_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.pos 144), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation12 144 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4783) (Sat.Literal.pos 144) (Sat.Literal.pos 36) (lex_12_144_prefix s) (positive_select s 144) (lex_12_144_image s)

theorem lex_12_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.pos 4783)] :=
  (lex_12_144_gate s).prop _ (List.Mem.head _)

theorem lex_12_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.neg 144), (Sat.Literal.pos 36)] :=
  (lex_12_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.pos 144), (Sat.Literal.neg 36)] :=
  (lex_12_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.neg 144), (Sat.Literal.neg 36), (Sat.Literal.pos 4784)] :=
  (lex_12_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4783), (Sat.Literal.pos 144), (Sat.Literal.pos 36), (Sat.Literal.pos 4784)] :=
  (lex_12_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4784) = lexBefore s permutation12 143 := by
  exact (positive_lex_of_descriptor s 4784 permutation12 144 (by rfl)).trans ((lex_skipped s permutation12 143 144 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation12 143) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation12 143 by rw [image12_eq]; rfl))

theorem lex_12_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4785) (Sat.Literal.pos 4784) (Sat.Literal.pos 143) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation12 143 (assignment s)
    (Sat.Literal.pos 4785) (Sat.Literal.pos 4784) (Sat.Literal.pos 143) (Sat.Literal.pos 227) (positive_of_descriptor s 4785 (.lex permutation12 143) (by rfl)) (lex_12_143_prefix s) (positive_select s 143) (lex_12_143_image s)

theorem lex_12_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.pos 143), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation12 143 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4784) (Sat.Literal.pos 143) (Sat.Literal.pos 227) (lex_12_143_prefix s) (positive_select s 143) (lex_12_143_image s)

theorem lex_12_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.pos 4784)] :=
  (lex_12_143_gate s).prop _ (List.Mem.head _)

theorem lex_12_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.neg 143), (Sat.Literal.pos 227)] :=
  (lex_12_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.pos 143), (Sat.Literal.neg 227)] :=
  (lex_12_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.neg 143), (Sat.Literal.neg 227), (Sat.Literal.pos 4785)] :=
  (lex_12_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4784), (Sat.Literal.pos 143), (Sat.Literal.pos 227), (Sat.Literal.pos 4785)] :=
  (lex_12_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4785) = lexBefore s permutation12 142 := by
  exact (positive_lex_of_descriptor s 4785 permutation12 143 (by rfl)).trans ((lex_skipped s permutation12 142 143 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation12 142) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation12 142 by rw [image12_eq]; rfl))

theorem lex_12_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4786) (Sat.Literal.pos 4785) (Sat.Literal.pos 142) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation12 142 (assignment s)
    (Sat.Literal.pos 4786) (Sat.Literal.pos 4785) (Sat.Literal.pos 142) (Sat.Literal.pos 163) (positive_of_descriptor s 4786 (.lex permutation12 142) (by rfl)) (lex_12_142_prefix s) (positive_select s 142) (lex_12_142_image s)

theorem lex_12_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.pos 142), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation12 142 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4785) (Sat.Literal.pos 142) (Sat.Literal.pos 163) (lex_12_142_prefix s) (positive_select s 142) (lex_12_142_image s)

theorem lex_12_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.pos 4785)] :=
  (lex_12_142_gate s).prop _ (List.Mem.head _)

theorem lex_12_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.neg 142), (Sat.Literal.pos 163)] :=
  (lex_12_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.pos 142), (Sat.Literal.neg 163)] :=
  (lex_12_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.neg 142), (Sat.Literal.neg 163), (Sat.Literal.pos 4786)] :=
  (lex_12_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4785), (Sat.Literal.pos 142), (Sat.Literal.pos 163), (Sat.Literal.pos 4786)] :=
  (lex_12_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4786) = lexBefore s permutation12 141 := by
  exact (positive_lex_of_descriptor s 4786 permutation12 142 (by rfl)).trans ((lex_skipped s permutation12 141 142 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation12 141) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation12 141 by rw [image12_eq]; rfl))

theorem lex_12_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4787) (Sat.Literal.pos 4786) (Sat.Literal.pos 141) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation12 141 (assignment s)
    (Sat.Literal.pos 4787) (Sat.Literal.pos 4786) (Sat.Literal.pos 141) (Sat.Literal.pos 99) (positive_of_descriptor s 4787 (.lex permutation12 141) (by rfl)) (lex_12_141_prefix s) (positive_select s 141) (lex_12_141_image s)

theorem lex_12_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.pos 141), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation12 141 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4786) (Sat.Literal.pos 141) (Sat.Literal.pos 99) (lex_12_141_prefix s) (positive_select s 141) (lex_12_141_image s)

theorem lex_12_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.pos 4786)] :=
  (lex_12_141_gate s).prop _ (List.Mem.head _)

theorem lex_12_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.neg 141), (Sat.Literal.pos 99)] :=
  (lex_12_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.pos 141), (Sat.Literal.neg 99)] :=
  (lex_12_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.neg 141), (Sat.Literal.neg 99), (Sat.Literal.pos 4787)] :=
  (lex_12_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4786), (Sat.Literal.pos 141), (Sat.Literal.pos 99), (Sat.Literal.pos 4787)] :=
  (lex_12_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4787) = lexBefore s permutation12 140 := by
  exact (positive_lex_of_descriptor s 4787 permutation12 141 (by rfl)).trans ((lex_skipped s permutation12 140 141 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation12 140) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation12 140 by rw [image12_eq]; rfl))

theorem lex_12_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4788) (Sat.Literal.pos 4787) (Sat.Literal.pos 140) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation12 140 (assignment s)
    (Sat.Literal.pos 4788) (Sat.Literal.pos 4787) (Sat.Literal.pos 140) (Sat.Literal.pos 35) (positive_of_descriptor s 4788 (.lex permutation12 140) (by rfl)) (lex_12_140_prefix s) (positive_select s 140) (lex_12_140_image s)

theorem lex_12_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.pos 140), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation12 140 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4787) (Sat.Literal.pos 140) (Sat.Literal.pos 35) (lex_12_140_prefix s) (positive_select s 140) (lex_12_140_image s)

theorem lex_12_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.pos 4787)] :=
  (lex_12_140_gate s).prop _ (List.Mem.head _)

theorem lex_12_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.neg 140), (Sat.Literal.pos 35)] :=
  (lex_12_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.pos 140), (Sat.Literal.neg 35)] :=
  (lex_12_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.neg 140), (Sat.Literal.neg 35), (Sat.Literal.pos 4788)] :=
  (lex_12_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4787), (Sat.Literal.pos 140), (Sat.Literal.pos 35), (Sat.Literal.pos 4788)] :=
  (lex_12_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4788) = lexBefore s permutation12 139 := by
  exact (positive_lex_of_descriptor s 4788 permutation12 140 (by rfl)).trans ((lex_skipped s permutation12 139 140 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation12 139) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation12 139 by rw [image12_eq]; rfl))

theorem lex_12_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4789) (Sat.Literal.pos 4788) (Sat.Literal.pos 139) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation12 139 (assignment s)
    (Sat.Literal.pos 4789) (Sat.Literal.pos 4788) (Sat.Literal.pos 139) (Sat.Literal.pos 226) (positive_of_descriptor s 4789 (.lex permutation12 139) (by rfl)) (lex_12_139_prefix s) (positive_select s 139) (lex_12_139_image s)

theorem lex_12_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.pos 139), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation12 139 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4788) (Sat.Literal.pos 139) (Sat.Literal.pos 226) (lex_12_139_prefix s) (positive_select s 139) (lex_12_139_image s)

theorem lex_12_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.pos 4788)] :=
  (lex_12_139_gate s).prop _ (List.Mem.head _)

theorem lex_12_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.neg 139), (Sat.Literal.pos 226)] :=
  (lex_12_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.pos 139), (Sat.Literal.neg 226)] :=
  (lex_12_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.neg 139), (Sat.Literal.neg 226), (Sat.Literal.pos 4789)] :=
  (lex_12_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4788), (Sat.Literal.pos 139), (Sat.Literal.pos 226), (Sat.Literal.pos 4789)] :=
  (lex_12_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4789) = lexBefore s permutation12 138 := by
  exact (positive_lex_of_descriptor s 4789 permutation12 139 (by rfl)).trans ((lex_skipped s permutation12 138 139 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation12 138) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation12 138 by rw [image12_eq]; rfl))

theorem lex_12_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4790) (Sat.Literal.pos 4789) (Sat.Literal.pos 138) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation12 138 (assignment s)
    (Sat.Literal.pos 4790) (Sat.Literal.pos 4789) (Sat.Literal.pos 138) (Sat.Literal.pos 162) (positive_of_descriptor s 4790 (.lex permutation12 138) (by rfl)) (lex_12_138_prefix s) (positive_select s 138) (lex_12_138_image s)

theorem lex_12_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.pos 138), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation12 138 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4789) (Sat.Literal.pos 138) (Sat.Literal.pos 162) (lex_12_138_prefix s) (positive_select s 138) (lex_12_138_image s)

theorem lex_12_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.pos 4789)] :=
  (lex_12_138_gate s).prop _ (List.Mem.head _)

theorem lex_12_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.neg 138), (Sat.Literal.pos 162)] :=
  (lex_12_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.pos 138), (Sat.Literal.neg 162)] :=
  (lex_12_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.neg 138), (Sat.Literal.neg 162), (Sat.Literal.pos 4790)] :=
  (lex_12_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4789), (Sat.Literal.pos 138), (Sat.Literal.pos 162), (Sat.Literal.pos 4790)] :=
  (lex_12_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4790) = lexBefore s permutation12 137 := by
  exact (positive_lex_of_descriptor s 4790 permutation12 138 (by rfl)).trans ((lex_skipped s permutation12 137 138 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation12 137) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation12 137 by rw [image12_eq]; rfl))

theorem lex_12_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4791) (Sat.Literal.pos 4790) (Sat.Literal.pos 137) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation12 137 (assignment s)
    (Sat.Literal.pos 4791) (Sat.Literal.pos 4790) (Sat.Literal.pos 137) (Sat.Literal.pos 98) (positive_of_descriptor s 4791 (.lex permutation12 137) (by rfl)) (lex_12_137_prefix s) (positive_select s 137) (lex_12_137_image s)

theorem lex_12_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.pos 137), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation12 137 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4790) (Sat.Literal.pos 137) (Sat.Literal.pos 98) (lex_12_137_prefix s) (positive_select s 137) (lex_12_137_image s)

theorem lex_12_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.pos 4790)] :=
  (lex_12_137_gate s).prop _ (List.Mem.head _)

theorem lex_12_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.neg 137), (Sat.Literal.pos 98)] :=
  (lex_12_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.pos 137), (Sat.Literal.neg 98)] :=
  (lex_12_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.neg 137), (Sat.Literal.neg 98), (Sat.Literal.pos 4791)] :=
  (lex_12_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4790), (Sat.Literal.pos 137), (Sat.Literal.pos 98), (Sat.Literal.pos 4791)] :=
  (lex_12_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4791) = lexBefore s permutation12 136 := by
  exact (positive_lex_of_descriptor s 4791 permutation12 137 (by rfl)).trans ((lex_skipped s permutation12 136 137 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation12 136) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation12 136 by rw [image12_eq]; rfl))

theorem lex_12_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4792) (Sat.Literal.pos 4791) (Sat.Literal.pos 136) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation12 136 (assignment s)
    (Sat.Literal.pos 4792) (Sat.Literal.pos 4791) (Sat.Literal.pos 136) (Sat.Literal.pos 34) (positive_of_descriptor s 4792 (.lex permutation12 136) (by rfl)) (lex_12_136_prefix s) (positive_select s 136) (lex_12_136_image s)

theorem lex_12_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.pos 136), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation12 136 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4791) (Sat.Literal.pos 136) (Sat.Literal.pos 34) (lex_12_136_prefix s) (positive_select s 136) (lex_12_136_image s)

theorem lex_12_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.pos 4791)] :=
  (lex_12_136_gate s).prop _ (List.Mem.head _)

theorem lex_12_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.neg 136), (Sat.Literal.pos 34)] :=
  (lex_12_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.pos 136), (Sat.Literal.neg 34)] :=
  (lex_12_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.neg 136), (Sat.Literal.neg 34), (Sat.Literal.pos 4792)] :=
  (lex_12_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4791), (Sat.Literal.pos 136), (Sat.Literal.pos 34), (Sat.Literal.pos 4792)] :=
  (lex_12_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4792) = lexBefore s permutation12 135 := by
  exact (positive_lex_of_descriptor s 4792 permutation12 136 (by rfl)).trans ((lex_skipped s permutation12 135 136 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation12 135) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation12 135 by rw [image12_eq]; rfl))

theorem lex_12_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4793) (Sat.Literal.pos 4792) (Sat.Literal.pos 135) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation12 135 (assignment s)
    (Sat.Literal.pos 4793) (Sat.Literal.pos 4792) (Sat.Literal.pos 135) (Sat.Literal.pos 225) (positive_of_descriptor s 4793 (.lex permutation12 135) (by rfl)) (lex_12_135_prefix s) (positive_select s 135) (lex_12_135_image s)

theorem lex_12_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.pos 135), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation12 135 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4792) (Sat.Literal.pos 135) (Sat.Literal.pos 225) (lex_12_135_prefix s) (positive_select s 135) (lex_12_135_image s)

theorem lex_12_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.pos 4792)] :=
  (lex_12_135_gate s).prop _ (List.Mem.head _)

theorem lex_12_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.neg 135), (Sat.Literal.pos 225)] :=
  (lex_12_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.pos 135), (Sat.Literal.neg 225)] :=
  (lex_12_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.neg 135), (Sat.Literal.neg 225), (Sat.Literal.pos 4793)] :=
  (lex_12_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4792), (Sat.Literal.pos 135), (Sat.Literal.pos 225), (Sat.Literal.pos 4793)] :=
  (lex_12_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4793) = lexBefore s permutation12 134 := by
  exact (positive_lex_of_descriptor s 4793 permutation12 135 (by rfl)).trans ((lex_skipped s permutation12 134 135 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation12 134) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation12 134 by rw [image12_eq]; rfl))

theorem lex_12_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4794) (Sat.Literal.pos 4793) (Sat.Literal.pos 134) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation12 134 (assignment s)
    (Sat.Literal.pos 4794) (Sat.Literal.pos 4793) (Sat.Literal.pos 134) (Sat.Literal.pos 161) (positive_of_descriptor s 4794 (.lex permutation12 134) (by rfl)) (lex_12_134_prefix s) (positive_select s 134) (lex_12_134_image s)

theorem lex_12_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.pos 134), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation12 134 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4793) (Sat.Literal.pos 134) (Sat.Literal.pos 161) (lex_12_134_prefix s) (positive_select s 134) (lex_12_134_image s)

theorem lex_12_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.pos 4793)] :=
  (lex_12_134_gate s).prop _ (List.Mem.head _)

theorem lex_12_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.neg 134), (Sat.Literal.pos 161)] :=
  (lex_12_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.pos 134), (Sat.Literal.neg 161)] :=
  (lex_12_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.neg 134), (Sat.Literal.neg 161), (Sat.Literal.pos 4794)] :=
  (lex_12_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4793), (Sat.Literal.pos 134), (Sat.Literal.pos 161), (Sat.Literal.pos 4794)] :=
  (lex_12_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4794) = lexBefore s permutation12 133 := by
  exact (positive_lex_of_descriptor s 4794 permutation12 134 (by rfl)).trans ((lex_skipped s permutation12 133 134 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation12 133) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation12 133 by rw [image12_eq]; rfl))

theorem lex_12_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4795) (Sat.Literal.pos 4794) (Sat.Literal.pos 133) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation12 133 (assignment s)
    (Sat.Literal.pos 4795) (Sat.Literal.pos 4794) (Sat.Literal.pos 133) (Sat.Literal.pos 97) (positive_of_descriptor s 4795 (.lex permutation12 133) (by rfl)) (lex_12_133_prefix s) (positive_select s 133) (lex_12_133_image s)

theorem lex_12_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.pos 133), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation12 133 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4794) (Sat.Literal.pos 133) (Sat.Literal.pos 97) (lex_12_133_prefix s) (positive_select s 133) (lex_12_133_image s)

theorem lex_12_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.pos 4794)] :=
  (lex_12_133_gate s).prop _ (List.Mem.head _)

theorem lex_12_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.neg 133), (Sat.Literal.pos 97)] :=
  (lex_12_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.pos 133), (Sat.Literal.neg 97)] :=
  (lex_12_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.neg 133), (Sat.Literal.neg 97), (Sat.Literal.pos 4795)] :=
  (lex_12_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4794), (Sat.Literal.pos 133), (Sat.Literal.pos 97), (Sat.Literal.pos 4795)] :=
  (lex_12_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4795) = lexBefore s permutation12 132 := by
  exact (positive_lex_of_descriptor s 4795 permutation12 133 (by rfl)).trans ((lex_skipped s permutation12 132 133 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation12 132) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation12 132 by rw [image12_eq]; rfl))

theorem lex_12_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4796) (Sat.Literal.pos 4795) (Sat.Literal.pos 132) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation12 132 (assignment s)
    (Sat.Literal.pos 4796) (Sat.Literal.pos 4795) (Sat.Literal.pos 132) (Sat.Literal.pos 33) (positive_of_descriptor s 4796 (.lex permutation12 132) (by rfl)) (lex_12_132_prefix s) (positive_select s 132) (lex_12_132_image s)

theorem lex_12_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.pos 132), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation12 132 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4795) (Sat.Literal.pos 132) (Sat.Literal.pos 33) (lex_12_132_prefix s) (positive_select s 132) (lex_12_132_image s)

theorem lex_12_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.pos 4795)] :=
  (lex_12_132_gate s).prop _ (List.Mem.head _)

theorem lex_12_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.neg 132), (Sat.Literal.pos 33)] :=
  (lex_12_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.pos 132), (Sat.Literal.neg 33)] :=
  (lex_12_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.neg 132), (Sat.Literal.neg 33), (Sat.Literal.pos 4796)] :=
  (lex_12_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4795), (Sat.Literal.pos 132), (Sat.Literal.pos 33), (Sat.Literal.pos 4796)] :=
  (lex_12_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4796) = lexBefore s permutation12 131 := by
  exact (positive_lex_of_descriptor s 4796 permutation12 132 (by rfl)).trans ((lex_skipped s permutation12 131 132 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation12 131) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation12 131 by rw [image12_eq]; rfl))

theorem lex_12_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4797) (Sat.Literal.pos 4796) (Sat.Literal.pos 131) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation12 131 (assignment s)
    (Sat.Literal.pos 4797) (Sat.Literal.pos 4796) (Sat.Literal.pos 131) (Sat.Literal.pos 224) (positive_of_descriptor s 4797 (.lex permutation12 131) (by rfl)) (lex_12_131_prefix s) (positive_select s 131) (lex_12_131_image s)

theorem lex_12_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.pos 131), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation12 131 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4796) (Sat.Literal.pos 131) (Sat.Literal.pos 224) (lex_12_131_prefix s) (positive_select s 131) (lex_12_131_image s)

theorem lex_12_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.pos 4796)] :=
  (lex_12_131_gate s).prop _ (List.Mem.head _)

theorem lex_12_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.neg 131), (Sat.Literal.pos 224)] :=
  (lex_12_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.pos 131), (Sat.Literal.neg 224)] :=
  (lex_12_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.neg 131), (Sat.Literal.neg 224), (Sat.Literal.pos 4797)] :=
  (lex_12_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4796), (Sat.Literal.pos 131), (Sat.Literal.pos 224), (Sat.Literal.pos 4797)] :=
  (lex_12_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4797) = lexBefore s permutation12 130 := by
  exact (positive_lex_of_descriptor s 4797 permutation12 131 (by rfl)).trans ((lex_skipped s permutation12 130 131 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation12 130) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation12 130 by rw [image12_eq]; rfl))

theorem lex_12_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4798) (Sat.Literal.pos 4797) (Sat.Literal.pos 130) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation12 130 (assignment s)
    (Sat.Literal.pos 4798) (Sat.Literal.pos 4797) (Sat.Literal.pos 130) (Sat.Literal.pos 160) (positive_of_descriptor s 4798 (.lex permutation12 130) (by rfl)) (lex_12_130_prefix s) (positive_select s 130) (lex_12_130_image s)

theorem lex_12_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.pos 130), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation12 130 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4797) (Sat.Literal.pos 130) (Sat.Literal.pos 160) (lex_12_130_prefix s) (positive_select s 130) (lex_12_130_image s)

theorem lex_12_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.pos 4797)] :=
  (lex_12_130_gate s).prop _ (List.Mem.head _)

theorem lex_12_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.neg 130), (Sat.Literal.pos 160)] :=
  (lex_12_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.pos 130), (Sat.Literal.neg 160)] :=
  (lex_12_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.neg 130), (Sat.Literal.neg 160), (Sat.Literal.pos 4798)] :=
  (lex_12_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4797), (Sat.Literal.pos 130), (Sat.Literal.pos 160), (Sat.Literal.pos 4798)] :=
  (lex_12_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4798) = lexBefore s permutation12 129 := by
  exact (positive_lex_of_descriptor s 4798 permutation12 130 (by rfl)).trans ((lex_skipped s permutation12 129 130 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation12 129) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation12 129 by rw [image12_eq]; rfl))

theorem lex_12_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4799) (Sat.Literal.pos 4798) (Sat.Literal.pos 129) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation12 129 (assignment s)
    (Sat.Literal.pos 4799) (Sat.Literal.pos 4798) (Sat.Literal.pos 129) (Sat.Literal.pos 96) (positive_of_descriptor s 4799 (.lex permutation12 129) (by rfl)) (lex_12_129_prefix s) (positive_select s 129) (lex_12_129_image s)

theorem lex_12_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.pos 129), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation12 129 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4798) (Sat.Literal.pos 129) (Sat.Literal.pos 96) (lex_12_129_prefix s) (positive_select s 129) (lex_12_129_image s)

theorem lex_12_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.pos 4798)] :=
  (lex_12_129_gate s).prop _ (List.Mem.head _)

theorem lex_12_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.neg 129), (Sat.Literal.pos 96)] :=
  (lex_12_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.pos 129), (Sat.Literal.neg 96)] :=
  (lex_12_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.neg 129), (Sat.Literal.neg 96), (Sat.Literal.pos 4799)] :=
  (lex_12_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4798), (Sat.Literal.pos 129), (Sat.Literal.pos 96), (Sat.Literal.pos 4799)] :=
  (lex_12_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4799) = lexBefore s permutation12 128 := by
  exact (positive_lex_of_descriptor s 4799 permutation12 129 (by rfl)).trans ((lex_skipped s permutation12 128 129 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation12 128) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation12 128 by rw [image12_eq]; rfl))

theorem lex_12_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4800) (Sat.Literal.pos 4799) (Sat.Literal.pos 128) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation12 128 (assignment s)
    (Sat.Literal.pos 4800) (Sat.Literal.pos 4799) (Sat.Literal.pos 128) (Sat.Literal.pos 32) (positive_of_descriptor s 4800 (.lex permutation12 128) (by rfl)) (lex_12_128_prefix s) (positive_select s 128) (lex_12_128_image s)

theorem lex_12_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.pos 128), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation12 128 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4799) (Sat.Literal.pos 128) (Sat.Literal.pos 32) (lex_12_128_prefix s) (positive_select s 128) (lex_12_128_image s)

theorem lex_12_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.pos 4799)] :=
  (lex_12_128_gate s).prop _ (List.Mem.head _)

theorem lex_12_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.neg 128), (Sat.Literal.pos 32)] :=
  (lex_12_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.pos 128), (Sat.Literal.neg 32)] :=
  (lex_12_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.neg 128), (Sat.Literal.neg 32), (Sat.Literal.pos 4800)] :=
  (lex_12_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4799), (Sat.Literal.pos 128), (Sat.Literal.pos 32), (Sat.Literal.pos 4800)] :=
  (lex_12_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4800) = lexBefore s permutation12 127 := by
  exact (positive_lex_of_descriptor s 4800 permutation12 128 (by rfl)).trans ((lex_skipped s permutation12 127 128 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation12 127) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation12 127 by rw [image12_eq]; rfl))

theorem lex_12_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4801) (Sat.Literal.pos 4800) (Sat.Literal.pos 127) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation12 127 (assignment s)
    (Sat.Literal.pos 4801) (Sat.Literal.pos 4800) (Sat.Literal.pos 127) (Sat.Literal.pos 223) (positive_of_descriptor s 4801 (.lex permutation12 127) (by rfl)) (lex_12_127_prefix s) (positive_select s 127) (lex_12_127_image s)

theorem lex_12_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.pos 127), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation12 127 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4800) (Sat.Literal.pos 127) (Sat.Literal.pos 223) (lex_12_127_prefix s) (positive_select s 127) (lex_12_127_image s)

theorem lex_12_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.pos 4800)] :=
  (lex_12_127_gate s).prop _ (List.Mem.head _)

theorem lex_12_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.neg 127), (Sat.Literal.pos 223)] :=
  (lex_12_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.pos 127), (Sat.Literal.neg 223)] :=
  (lex_12_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.neg 127), (Sat.Literal.neg 223), (Sat.Literal.pos 4801)] :=
  (lex_12_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4800), (Sat.Literal.pos 127), (Sat.Literal.pos 223), (Sat.Literal.pos 4801)] :=
  (lex_12_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4801) = lexBefore s permutation12 126 := by
  exact (positive_lex_of_descriptor s 4801 permutation12 127 (by rfl)).trans ((lex_skipped s permutation12 126 127 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation12 126) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation12 126 by rw [image12_eq]; rfl))

theorem lex_12_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4802) (Sat.Literal.pos 4801) (Sat.Literal.pos 126) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation12 126 (assignment s)
    (Sat.Literal.pos 4802) (Sat.Literal.pos 4801) (Sat.Literal.pos 126) (Sat.Literal.pos 159) (positive_of_descriptor s 4802 (.lex permutation12 126) (by rfl)) (lex_12_126_prefix s) (positive_select s 126) (lex_12_126_image s)

theorem lex_12_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.pos 126), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation12 126 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4801) (Sat.Literal.pos 126) (Sat.Literal.pos 159) (lex_12_126_prefix s) (positive_select s 126) (lex_12_126_image s)

theorem lex_12_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.pos 4801)] :=
  (lex_12_126_gate s).prop _ (List.Mem.head _)

theorem lex_12_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.neg 126), (Sat.Literal.pos 159)] :=
  (lex_12_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.pos 126), (Sat.Literal.neg 159)] :=
  (lex_12_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.neg 126), (Sat.Literal.neg 159), (Sat.Literal.pos 4802)] :=
  (lex_12_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4801), (Sat.Literal.pos 126), (Sat.Literal.pos 159), (Sat.Literal.pos 4802)] :=
  (lex_12_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4802) = lexBefore s permutation12 125 := by
  exact (positive_lex_of_descriptor s 4802 permutation12 126 (by rfl)).trans ((lex_skipped s permutation12 125 126 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation12 125) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation12 125 by rw [image12_eq]; rfl))

theorem lex_12_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4803) (Sat.Literal.pos 4802) (Sat.Literal.pos 125) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation12 125 (assignment s)
    (Sat.Literal.pos 4803) (Sat.Literal.pos 4802) (Sat.Literal.pos 125) (Sat.Literal.pos 95) (positive_of_descriptor s 4803 (.lex permutation12 125) (by rfl)) (lex_12_125_prefix s) (positive_select s 125) (lex_12_125_image s)

theorem lex_12_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.pos 125), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation12 125 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4802) (Sat.Literal.pos 125) (Sat.Literal.pos 95) (lex_12_125_prefix s) (positive_select s 125) (lex_12_125_image s)

theorem lex_12_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.pos 4802)] :=
  (lex_12_125_gate s).prop _ (List.Mem.head _)

theorem lex_12_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.neg 125), (Sat.Literal.pos 95)] :=
  (lex_12_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.pos 125), (Sat.Literal.neg 95)] :=
  (lex_12_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.neg 125), (Sat.Literal.neg 95), (Sat.Literal.pos 4803)] :=
  (lex_12_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4802), (Sat.Literal.pos 125), (Sat.Literal.pos 95), (Sat.Literal.pos 4803)] :=
  (lex_12_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4803) = lexBefore s permutation12 124 := by
  exact (positive_lex_of_descriptor s 4803 permutation12 125 (by rfl)).trans ((lex_skipped s permutation12 124 125 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation12 124) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation12 124 by rw [image12_eq]; rfl))

theorem lex_12_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4804) (Sat.Literal.pos 4803) (Sat.Literal.pos 124) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation12 124 (assignment s)
    (Sat.Literal.pos 4804) (Sat.Literal.pos 4803) (Sat.Literal.pos 124) (Sat.Literal.pos 31) (positive_of_descriptor s 4804 (.lex permutation12 124) (by rfl)) (lex_12_124_prefix s) (positive_select s 124) (lex_12_124_image s)

theorem lex_12_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.pos 124), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation12 124 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4803) (Sat.Literal.pos 124) (Sat.Literal.pos 31) (lex_12_124_prefix s) (positive_select s 124) (lex_12_124_image s)

theorem lex_12_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.pos 4803)] :=
  (lex_12_124_gate s).prop _ (List.Mem.head _)

theorem lex_12_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.neg 124), (Sat.Literal.pos 31)] :=
  (lex_12_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.pos 124), (Sat.Literal.neg 31)] :=
  (lex_12_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.neg 124), (Sat.Literal.neg 31), (Sat.Literal.pos 4804)] :=
  (lex_12_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4803), (Sat.Literal.pos 124), (Sat.Literal.pos 31), (Sat.Literal.pos 4804)] :=
  (lex_12_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4804) = lexBefore s permutation12 123 := by
  exact (positive_lex_of_descriptor s 4804 permutation12 124 (by rfl)).trans ((lex_skipped s permutation12 123 124 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation12 123) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation12 123 by rw [image12_eq]; rfl))

theorem lex_12_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4805) (Sat.Literal.pos 4804) (Sat.Literal.pos 123) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation12 123 (assignment s)
    (Sat.Literal.pos 4805) (Sat.Literal.pos 4804) (Sat.Literal.pos 123) (Sat.Literal.pos 222) (positive_of_descriptor s 4805 (.lex permutation12 123) (by rfl)) (lex_12_123_prefix s) (positive_select s 123) (lex_12_123_image s)

theorem lex_12_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.pos 123), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation12 123 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4804) (Sat.Literal.pos 123) (Sat.Literal.pos 222) (lex_12_123_prefix s) (positive_select s 123) (lex_12_123_image s)

theorem lex_12_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.pos 4804)] :=
  (lex_12_123_gate s).prop _ (List.Mem.head _)

theorem lex_12_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.neg 123), (Sat.Literal.pos 222)] :=
  (lex_12_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.pos 123), (Sat.Literal.neg 222)] :=
  (lex_12_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.neg 123), (Sat.Literal.neg 222), (Sat.Literal.pos 4805)] :=
  (lex_12_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4804), (Sat.Literal.pos 123), (Sat.Literal.pos 222), (Sat.Literal.pos 4805)] :=
  (lex_12_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4805) = lexBefore s permutation12 122 := by
  exact (positive_lex_of_descriptor s 4805 permutation12 123 (by rfl)).trans ((lex_skipped s permutation12 122 123 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation12 122) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation12 122 by rw [image12_eq]; rfl))

theorem lex_12_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4806) (Sat.Literal.pos 4805) (Sat.Literal.pos 122) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation12 122 (assignment s)
    (Sat.Literal.pos 4806) (Sat.Literal.pos 4805) (Sat.Literal.pos 122) (Sat.Literal.pos 158) (positive_of_descriptor s 4806 (.lex permutation12 122) (by rfl)) (lex_12_122_prefix s) (positive_select s 122) (lex_12_122_image s)

theorem lex_12_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.pos 122), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation12 122 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4805) (Sat.Literal.pos 122) (Sat.Literal.pos 158) (lex_12_122_prefix s) (positive_select s 122) (lex_12_122_image s)

theorem lex_12_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.pos 4805)] :=
  (lex_12_122_gate s).prop _ (List.Mem.head _)

theorem lex_12_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.neg 122), (Sat.Literal.pos 158)] :=
  (lex_12_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.pos 122), (Sat.Literal.neg 158)] :=
  (lex_12_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.neg 122), (Sat.Literal.neg 158), (Sat.Literal.pos 4806)] :=
  (lex_12_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4805), (Sat.Literal.pos 122), (Sat.Literal.pos 158), (Sat.Literal.pos 4806)] :=
  (lex_12_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4806) = lexBefore s permutation12 121 := by
  exact (positive_lex_of_descriptor s 4806 permutation12 122 (by rfl)).trans ((lex_skipped s permutation12 121 122 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation12 121) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation12 121 by rw [image12_eq]; rfl))

theorem lex_12_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4807) (Sat.Literal.pos 4806) (Sat.Literal.pos 121) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation12 121 (assignment s)
    (Sat.Literal.pos 4807) (Sat.Literal.pos 4806) (Sat.Literal.pos 121) (Sat.Literal.pos 94) (positive_of_descriptor s 4807 (.lex permutation12 121) (by rfl)) (lex_12_121_prefix s) (positive_select s 121) (lex_12_121_image s)

theorem lex_12_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.pos 121), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation12 121 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4806) (Sat.Literal.pos 121) (Sat.Literal.pos 94) (lex_12_121_prefix s) (positive_select s 121) (lex_12_121_image s)

theorem lex_12_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.pos 4806)] :=
  (lex_12_121_gate s).prop _ (List.Mem.head _)

theorem lex_12_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.neg 121), (Sat.Literal.pos 94)] :=
  (lex_12_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.pos 121), (Sat.Literal.neg 94)] :=
  (lex_12_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.neg 121), (Sat.Literal.neg 94), (Sat.Literal.pos 4807)] :=
  (lex_12_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4806), (Sat.Literal.pos 121), (Sat.Literal.pos 94), (Sat.Literal.pos 4807)] :=
  (lex_12_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4807) = lexBefore s permutation12 120 := by
  exact (positive_lex_of_descriptor s 4807 permutation12 121 (by rfl)).trans ((lex_skipped s permutation12 120 121 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation12 120) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation12 120 by rw [image12_eq]; rfl))

theorem lex_12_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4808) (Sat.Literal.pos 4807) (Sat.Literal.pos 120) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation12 120 (assignment s)
    (Sat.Literal.pos 4808) (Sat.Literal.pos 4807) (Sat.Literal.pos 120) (Sat.Literal.pos 30) (positive_of_descriptor s 4808 (.lex permutation12 120) (by rfl)) (lex_12_120_prefix s) (positive_select s 120) (lex_12_120_image s)

theorem lex_12_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.pos 120), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation12 120 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4807) (Sat.Literal.pos 120) (Sat.Literal.pos 30) (lex_12_120_prefix s) (positive_select s 120) (lex_12_120_image s)

theorem lex_12_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.pos 4807)] :=
  (lex_12_120_gate s).prop _ (List.Mem.head _)

theorem lex_12_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.neg 120), (Sat.Literal.pos 30)] :=
  (lex_12_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.pos 120), (Sat.Literal.neg 30)] :=
  (lex_12_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.neg 120), (Sat.Literal.neg 30), (Sat.Literal.pos 4808)] :=
  (lex_12_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4807), (Sat.Literal.pos 120), (Sat.Literal.pos 30), (Sat.Literal.pos 4808)] :=
  (lex_12_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4808) = lexBefore s permutation12 119 := by
  exact (positive_lex_of_descriptor s 4808 permutation12 120 (by rfl)).trans ((lex_skipped s permutation12 119 120 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation12 119) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation12 119 by rw [image12_eq]; rfl))

theorem lex_12_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4809) (Sat.Literal.pos 4808) (Sat.Literal.pos 119) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation12 119 (assignment s)
    (Sat.Literal.pos 4809) (Sat.Literal.pos 4808) (Sat.Literal.pos 119) (Sat.Literal.pos 221) (positive_of_descriptor s 4809 (.lex permutation12 119) (by rfl)) (lex_12_119_prefix s) (positive_select s 119) (lex_12_119_image s)

theorem lex_12_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.pos 119), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation12 119 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4808) (Sat.Literal.pos 119) (Sat.Literal.pos 221) (lex_12_119_prefix s) (positive_select s 119) (lex_12_119_image s)

theorem lex_12_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.pos 4808)] :=
  (lex_12_119_gate s).prop _ (List.Mem.head _)

theorem lex_12_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.neg 119), (Sat.Literal.pos 221)] :=
  (lex_12_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.pos 119), (Sat.Literal.neg 221)] :=
  (lex_12_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.neg 119), (Sat.Literal.neg 221), (Sat.Literal.pos 4809)] :=
  (lex_12_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4808), (Sat.Literal.pos 119), (Sat.Literal.pos 221), (Sat.Literal.pos 4809)] :=
  (lex_12_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4809) = lexBefore s permutation12 118 := by
  exact (positive_lex_of_descriptor s 4809 permutation12 119 (by rfl)).trans ((lex_skipped s permutation12 118 119 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation12 118) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation12 118 by rw [image12_eq]; rfl))

theorem lex_12_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4810) (Sat.Literal.pos 4809) (Sat.Literal.pos 118) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation12 118 (assignment s)
    (Sat.Literal.pos 4810) (Sat.Literal.pos 4809) (Sat.Literal.pos 118) (Sat.Literal.pos 157) (positive_of_descriptor s 4810 (.lex permutation12 118) (by rfl)) (lex_12_118_prefix s) (positive_select s 118) (lex_12_118_image s)

theorem lex_12_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.pos 118), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation12 118 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4809) (Sat.Literal.pos 118) (Sat.Literal.pos 157) (lex_12_118_prefix s) (positive_select s 118) (lex_12_118_image s)

theorem lex_12_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.pos 4809)] :=
  (lex_12_118_gate s).prop _ (List.Mem.head _)

theorem lex_12_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.neg 118), (Sat.Literal.pos 157)] :=
  (lex_12_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.pos 118), (Sat.Literal.neg 157)] :=
  (lex_12_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.neg 118), (Sat.Literal.neg 157), (Sat.Literal.pos 4810)] :=
  (lex_12_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4809), (Sat.Literal.pos 118), (Sat.Literal.pos 157), (Sat.Literal.pos 4810)] :=
  (lex_12_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4810) = lexBefore s permutation12 117 := by
  exact (positive_lex_of_descriptor s 4810 permutation12 118 (by rfl)).trans ((lex_skipped s permutation12 117 118 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation12 117) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation12 117 by rw [image12_eq]; rfl))

theorem lex_12_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4811) (Sat.Literal.pos 4810) (Sat.Literal.pos 117) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation12 117 (assignment s)
    (Sat.Literal.pos 4811) (Sat.Literal.pos 4810) (Sat.Literal.pos 117) (Sat.Literal.pos 93) (positive_of_descriptor s 4811 (.lex permutation12 117) (by rfl)) (lex_12_117_prefix s) (positive_select s 117) (lex_12_117_image s)

theorem lex_12_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.pos 117), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation12 117 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4810) (Sat.Literal.pos 117) (Sat.Literal.pos 93) (lex_12_117_prefix s) (positive_select s 117) (lex_12_117_image s)

theorem lex_12_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.pos 4810)] :=
  (lex_12_117_gate s).prop _ (List.Mem.head _)

theorem lex_12_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.neg 117), (Sat.Literal.pos 93)] :=
  (lex_12_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.pos 117), (Sat.Literal.neg 93)] :=
  (lex_12_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.neg 117), (Sat.Literal.neg 93), (Sat.Literal.pos 4811)] :=
  (lex_12_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4810), (Sat.Literal.pos 117), (Sat.Literal.pos 93), (Sat.Literal.pos 4811)] :=
  (lex_12_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4811) = lexBefore s permutation12 116 := by
  exact (positive_lex_of_descriptor s 4811 permutation12 117 (by rfl)).trans ((lex_skipped s permutation12 116 117 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation12 116) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation12 116 by rw [image12_eq]; rfl))

theorem lex_12_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4812) (Sat.Literal.pos 4811) (Sat.Literal.pos 116) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation12 116 (assignment s)
    (Sat.Literal.pos 4812) (Sat.Literal.pos 4811) (Sat.Literal.pos 116) (Sat.Literal.pos 29) (positive_of_descriptor s 4812 (.lex permutation12 116) (by rfl)) (lex_12_116_prefix s) (positive_select s 116) (lex_12_116_image s)

theorem lex_12_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.pos 116), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation12 116 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4811) (Sat.Literal.pos 116) (Sat.Literal.pos 29) (lex_12_116_prefix s) (positive_select s 116) (lex_12_116_image s)

theorem lex_12_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.pos 4811)] :=
  (lex_12_116_gate s).prop _ (List.Mem.head _)

theorem lex_12_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.neg 116), (Sat.Literal.pos 29)] :=
  (lex_12_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.pos 116), (Sat.Literal.neg 29)] :=
  (lex_12_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.neg 116), (Sat.Literal.neg 29), (Sat.Literal.pos 4812)] :=
  (lex_12_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4811), (Sat.Literal.pos 116), (Sat.Literal.pos 29), (Sat.Literal.pos 4812)] :=
  (lex_12_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4812) = lexBefore s permutation12 115 := by
  exact (positive_lex_of_descriptor s 4812 permutation12 116 (by rfl)).trans ((lex_skipped s permutation12 115 116 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation12 115) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation12 115 by rw [image12_eq]; rfl))

theorem lex_12_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4813) (Sat.Literal.pos 4812) (Sat.Literal.pos 115) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation12 115 (assignment s)
    (Sat.Literal.pos 4813) (Sat.Literal.pos 4812) (Sat.Literal.pos 115) (Sat.Literal.pos 220) (positive_of_descriptor s 4813 (.lex permutation12 115) (by rfl)) (lex_12_115_prefix s) (positive_select s 115) (lex_12_115_image s)

theorem lex_12_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.pos 115), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation12 115 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4812) (Sat.Literal.pos 115) (Sat.Literal.pos 220) (lex_12_115_prefix s) (positive_select s 115) (lex_12_115_image s)

theorem lex_12_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.pos 4812)] :=
  (lex_12_115_gate s).prop _ (List.Mem.head _)

theorem lex_12_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.neg 115), (Sat.Literal.pos 220)] :=
  (lex_12_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.pos 115), (Sat.Literal.neg 220)] :=
  (lex_12_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.neg 115), (Sat.Literal.neg 220), (Sat.Literal.pos 4813)] :=
  (lex_12_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4812), (Sat.Literal.pos 115), (Sat.Literal.pos 220), (Sat.Literal.pos 4813)] :=
  (lex_12_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4813) = lexBefore s permutation12 114 := by
  exact (positive_lex_of_descriptor s 4813 permutation12 115 (by rfl)).trans ((lex_skipped s permutation12 114 115 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation12 114) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation12 114 by rw [image12_eq]; rfl))

theorem lex_12_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4814) (Sat.Literal.pos 4813) (Sat.Literal.pos 114) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation12 114 (assignment s)
    (Sat.Literal.pos 4814) (Sat.Literal.pos 4813) (Sat.Literal.pos 114) (Sat.Literal.pos 156) (positive_of_descriptor s 4814 (.lex permutation12 114) (by rfl)) (lex_12_114_prefix s) (positive_select s 114) (lex_12_114_image s)

theorem lex_12_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.pos 114), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation12 114 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4813) (Sat.Literal.pos 114) (Sat.Literal.pos 156) (lex_12_114_prefix s) (positive_select s 114) (lex_12_114_image s)

theorem lex_12_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.pos 4813)] :=
  (lex_12_114_gate s).prop _ (List.Mem.head _)

theorem lex_12_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.neg 114), (Sat.Literal.pos 156)] :=
  (lex_12_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.pos 114), (Sat.Literal.neg 156)] :=
  (lex_12_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.neg 114), (Sat.Literal.neg 156), (Sat.Literal.pos 4814)] :=
  (lex_12_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4813), (Sat.Literal.pos 114), (Sat.Literal.pos 156), (Sat.Literal.pos 4814)] :=
  (lex_12_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4814) = lexBefore s permutation12 113 := by
  exact (positive_lex_of_descriptor s 4814 permutation12 114 (by rfl)).trans ((lex_skipped s permutation12 113 114 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation12 113) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation12 113 by rw [image12_eq]; rfl))

theorem lex_12_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4815) (Sat.Literal.pos 4814) (Sat.Literal.pos 113) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation12 113 (assignment s)
    (Sat.Literal.pos 4815) (Sat.Literal.pos 4814) (Sat.Literal.pos 113) (Sat.Literal.pos 92) (positive_of_descriptor s 4815 (.lex permutation12 113) (by rfl)) (lex_12_113_prefix s) (positive_select s 113) (lex_12_113_image s)

theorem lex_12_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.pos 113), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation12 113 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4814) (Sat.Literal.pos 113) (Sat.Literal.pos 92) (lex_12_113_prefix s) (positive_select s 113) (lex_12_113_image s)

theorem lex_12_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.pos 4814)] :=
  (lex_12_113_gate s).prop _ (List.Mem.head _)

theorem lex_12_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.neg 113), (Sat.Literal.pos 92)] :=
  (lex_12_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.pos 113), (Sat.Literal.neg 92)] :=
  (lex_12_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.neg 113), (Sat.Literal.neg 92), (Sat.Literal.pos 4815)] :=
  (lex_12_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4814), (Sat.Literal.pos 113), (Sat.Literal.pos 92), (Sat.Literal.pos 4815)] :=
  (lex_12_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4815) = lexBefore s permutation12 112 := by
  exact (positive_lex_of_descriptor s 4815 permutation12 113 (by rfl)).trans ((lex_skipped s permutation12 112 113 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation12 112) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation12 112 by rw [image12_eq]; rfl))

theorem lex_12_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4816) (Sat.Literal.pos 4815) (Sat.Literal.pos 112) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation12 112 (assignment s)
    (Sat.Literal.pos 4816) (Sat.Literal.pos 4815) (Sat.Literal.pos 112) (Sat.Literal.pos 28) (positive_of_descriptor s 4816 (.lex permutation12 112) (by rfl)) (lex_12_112_prefix s) (positive_select s 112) (lex_12_112_image s)

theorem lex_12_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.pos 112), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation12 112 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4815) (Sat.Literal.pos 112) (Sat.Literal.pos 28) (lex_12_112_prefix s) (positive_select s 112) (lex_12_112_image s)

theorem lex_12_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.pos 4815)] :=
  (lex_12_112_gate s).prop _ (List.Mem.head _)

theorem lex_12_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.neg 112), (Sat.Literal.pos 28)] :=
  (lex_12_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.pos 112), (Sat.Literal.neg 28)] :=
  (lex_12_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.neg 112), (Sat.Literal.neg 28), (Sat.Literal.pos 4816)] :=
  (lex_12_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4815), (Sat.Literal.pos 112), (Sat.Literal.pos 28), (Sat.Literal.pos 4816)] :=
  (lex_12_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4816) = lexBefore s permutation12 111 := by
  exact (positive_lex_of_descriptor s 4816 permutation12 112 (by rfl)).trans ((lex_skipped s permutation12 111 112 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation12 111) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation12 111 by rw [image12_eq]; rfl))

theorem lex_12_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4817) (Sat.Literal.pos 4816) (Sat.Literal.pos 111) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation12 111 (assignment s)
    (Sat.Literal.pos 4817) (Sat.Literal.pos 4816) (Sat.Literal.pos 111) (Sat.Literal.pos 219) (positive_of_descriptor s 4817 (.lex permutation12 111) (by rfl)) (lex_12_111_prefix s) (positive_select s 111) (lex_12_111_image s)

theorem lex_12_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.pos 111), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation12 111 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4816) (Sat.Literal.pos 111) (Sat.Literal.pos 219) (lex_12_111_prefix s) (positive_select s 111) (lex_12_111_image s)

theorem lex_12_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.pos 4816)] :=
  (lex_12_111_gate s).prop _ (List.Mem.head _)

theorem lex_12_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.neg 111), (Sat.Literal.pos 219)] :=
  (lex_12_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.pos 111), (Sat.Literal.neg 219)] :=
  (lex_12_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.neg 111), (Sat.Literal.neg 219), (Sat.Literal.pos 4817)] :=
  (lex_12_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4816), (Sat.Literal.pos 111), (Sat.Literal.pos 219), (Sat.Literal.pos 4817)] :=
  (lex_12_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4817) = lexBefore s permutation12 110 := by
  exact (positive_lex_of_descriptor s 4817 permutation12 111 (by rfl)).trans ((lex_skipped s permutation12 110 111 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation12 110) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation12 110 by rw [image12_eq]; rfl))

theorem lex_12_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4818) (Sat.Literal.pos 4817) (Sat.Literal.pos 110) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation12 110 (assignment s)
    (Sat.Literal.pos 4818) (Sat.Literal.pos 4817) (Sat.Literal.pos 110) (Sat.Literal.pos 155) (positive_of_descriptor s 4818 (.lex permutation12 110) (by rfl)) (lex_12_110_prefix s) (positive_select s 110) (lex_12_110_image s)

theorem lex_12_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.pos 110), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation12 110 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4817) (Sat.Literal.pos 110) (Sat.Literal.pos 155) (lex_12_110_prefix s) (positive_select s 110) (lex_12_110_image s)

theorem lex_12_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.pos 4817)] :=
  (lex_12_110_gate s).prop _ (List.Mem.head _)

theorem lex_12_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.neg 110), (Sat.Literal.pos 155)] :=
  (lex_12_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.pos 110), (Sat.Literal.neg 155)] :=
  (lex_12_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.neg 110), (Sat.Literal.neg 155), (Sat.Literal.pos 4818)] :=
  (lex_12_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4817), (Sat.Literal.pos 110), (Sat.Literal.pos 155), (Sat.Literal.pos 4818)] :=
  (lex_12_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4818) = lexBefore s permutation12 109 := by
  exact (positive_lex_of_descriptor s 4818 permutation12 110 (by rfl)).trans ((lex_skipped s permutation12 109 110 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation12 109) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation12 109 by rw [image12_eq]; rfl))

theorem lex_12_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4819) (Sat.Literal.pos 4818) (Sat.Literal.pos 109) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation12 109 (assignment s)
    (Sat.Literal.pos 4819) (Sat.Literal.pos 4818) (Sat.Literal.pos 109) (Sat.Literal.pos 91) (positive_of_descriptor s 4819 (.lex permutation12 109) (by rfl)) (lex_12_109_prefix s) (positive_select s 109) (lex_12_109_image s)

theorem lex_12_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.pos 109), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation12 109 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4818) (Sat.Literal.pos 109) (Sat.Literal.pos 91) (lex_12_109_prefix s) (positive_select s 109) (lex_12_109_image s)

theorem lex_12_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.pos 4818)] :=
  (lex_12_109_gate s).prop _ (List.Mem.head _)

theorem lex_12_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.neg 109), (Sat.Literal.pos 91)] :=
  (lex_12_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.pos 109), (Sat.Literal.neg 91)] :=
  (lex_12_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.neg 109), (Sat.Literal.neg 91), (Sat.Literal.pos 4819)] :=
  (lex_12_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4818), (Sat.Literal.pos 109), (Sat.Literal.pos 91), (Sat.Literal.pos 4819)] :=
  (lex_12_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4819) = lexBefore s permutation12 108 := by
  exact (positive_lex_of_descriptor s 4819 permutation12 109 (by rfl)).trans ((lex_skipped s permutation12 108 109 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation12 108) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation12 108 by rw [image12_eq]; rfl))

theorem lex_12_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4820) (Sat.Literal.pos 4819) (Sat.Literal.pos 108) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation12 108 (assignment s)
    (Sat.Literal.pos 4820) (Sat.Literal.pos 4819) (Sat.Literal.pos 108) (Sat.Literal.pos 27) (positive_of_descriptor s 4820 (.lex permutation12 108) (by rfl)) (lex_12_108_prefix s) (positive_select s 108) (lex_12_108_image s)

theorem lex_12_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.pos 108), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation12 108 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4819) (Sat.Literal.pos 108) (Sat.Literal.pos 27) (lex_12_108_prefix s) (positive_select s 108) (lex_12_108_image s)

theorem lex_12_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.pos 4819)] :=
  (lex_12_108_gate s).prop _ (List.Mem.head _)

theorem lex_12_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.neg 108), (Sat.Literal.pos 27)] :=
  (lex_12_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.pos 108), (Sat.Literal.neg 27)] :=
  (lex_12_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.neg 108), (Sat.Literal.neg 27), (Sat.Literal.pos 4820)] :=
  (lex_12_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4819), (Sat.Literal.pos 108), (Sat.Literal.pos 27), (Sat.Literal.pos 4820)] :=
  (lex_12_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4820) = lexBefore s permutation12 107 := by
  exact (positive_lex_of_descriptor s 4820 permutation12 108 (by rfl)).trans ((lex_skipped s permutation12 107 108 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation12 107) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation12 107 by rw [image12_eq]; rfl))

theorem lex_12_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4821) (Sat.Literal.pos 4820) (Sat.Literal.pos 107) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation12 107 (assignment s)
    (Sat.Literal.pos 4821) (Sat.Literal.pos 4820) (Sat.Literal.pos 107) (Sat.Literal.pos 218) (positive_of_descriptor s 4821 (.lex permutation12 107) (by rfl)) (lex_12_107_prefix s) (positive_select s 107) (lex_12_107_image s)

theorem lex_12_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.pos 107), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation12 107 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4820) (Sat.Literal.pos 107) (Sat.Literal.pos 218) (lex_12_107_prefix s) (positive_select s 107) (lex_12_107_image s)

theorem lex_12_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.pos 4820)] :=
  (lex_12_107_gate s).prop _ (List.Mem.head _)

theorem lex_12_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.neg 107), (Sat.Literal.pos 218)] :=
  (lex_12_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.pos 107), (Sat.Literal.neg 218)] :=
  (lex_12_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.neg 107), (Sat.Literal.neg 218), (Sat.Literal.pos 4821)] :=
  (lex_12_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4820), (Sat.Literal.pos 107), (Sat.Literal.pos 218), (Sat.Literal.pos 4821)] :=
  (lex_12_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4821) = lexBefore s permutation12 106 := by
  exact (positive_lex_of_descriptor s 4821 permutation12 107 (by rfl)).trans ((lex_skipped s permutation12 106 107 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation12 106) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation12 106 by rw [image12_eq]; rfl))

theorem lex_12_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4822) (Sat.Literal.pos 4821) (Sat.Literal.pos 106) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation12 106 (assignment s)
    (Sat.Literal.pos 4822) (Sat.Literal.pos 4821) (Sat.Literal.pos 106) (Sat.Literal.pos 154) (positive_of_descriptor s 4822 (.lex permutation12 106) (by rfl)) (lex_12_106_prefix s) (positive_select s 106) (lex_12_106_image s)

theorem lex_12_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.pos 106), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation12 106 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4821) (Sat.Literal.pos 106) (Sat.Literal.pos 154) (lex_12_106_prefix s) (positive_select s 106) (lex_12_106_image s)

theorem lex_12_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.pos 4821)] :=
  (lex_12_106_gate s).prop _ (List.Mem.head _)

theorem lex_12_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.neg 106), (Sat.Literal.pos 154)] :=
  (lex_12_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.pos 106), (Sat.Literal.neg 154)] :=
  (lex_12_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.neg 106), (Sat.Literal.neg 154), (Sat.Literal.pos 4822)] :=
  (lex_12_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4821), (Sat.Literal.pos 106), (Sat.Literal.pos 154), (Sat.Literal.pos 4822)] :=
  (lex_12_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4822) = lexBefore s permutation12 105 := by
  exact (positive_lex_of_descriptor s 4822 permutation12 106 (by rfl)).trans ((lex_skipped s permutation12 105 106 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation12 105) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation12 105 by rw [image12_eq]; rfl))

theorem lex_12_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4823) (Sat.Literal.pos 4822) (Sat.Literal.pos 105) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation12 105 (assignment s)
    (Sat.Literal.pos 4823) (Sat.Literal.pos 4822) (Sat.Literal.pos 105) (Sat.Literal.pos 90) (positive_of_descriptor s 4823 (.lex permutation12 105) (by rfl)) (lex_12_105_prefix s) (positive_select s 105) (lex_12_105_image s)

theorem lex_12_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.pos 105), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation12 105 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4822) (Sat.Literal.pos 105) (Sat.Literal.pos 90) (lex_12_105_prefix s) (positive_select s 105) (lex_12_105_image s)

theorem lex_12_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.pos 4822)] :=
  (lex_12_105_gate s).prop _ (List.Mem.head _)

theorem lex_12_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.neg 105), (Sat.Literal.pos 90)] :=
  (lex_12_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.pos 105), (Sat.Literal.neg 90)] :=
  (lex_12_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.neg 105), (Sat.Literal.neg 90), (Sat.Literal.pos 4823)] :=
  (lex_12_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4822), (Sat.Literal.pos 105), (Sat.Literal.pos 90), (Sat.Literal.pos 4823)] :=
  (lex_12_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4823) = lexBefore s permutation12 104 := by
  exact (positive_lex_of_descriptor s 4823 permutation12 105 (by rfl)).trans ((lex_skipped s permutation12 104 105 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation12 104) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation12 104 by rw [image12_eq]; rfl))

theorem lex_12_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4824) (Sat.Literal.pos 4823) (Sat.Literal.pos 104) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation12 104 (assignment s)
    (Sat.Literal.pos 4824) (Sat.Literal.pos 4823) (Sat.Literal.pos 104) (Sat.Literal.pos 26) (positive_of_descriptor s 4824 (.lex permutation12 104) (by rfl)) (lex_12_104_prefix s) (positive_select s 104) (lex_12_104_image s)

theorem lex_12_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.pos 104), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation12 104 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4823) (Sat.Literal.pos 104) (Sat.Literal.pos 26) (lex_12_104_prefix s) (positive_select s 104) (lex_12_104_image s)

theorem lex_12_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.pos 4823)] :=
  (lex_12_104_gate s).prop _ (List.Mem.head _)

theorem lex_12_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.neg 104), (Sat.Literal.pos 26)] :=
  (lex_12_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.pos 104), (Sat.Literal.neg 26)] :=
  (lex_12_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.neg 104), (Sat.Literal.neg 26), (Sat.Literal.pos 4824)] :=
  (lex_12_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4823), (Sat.Literal.pos 104), (Sat.Literal.pos 26), (Sat.Literal.pos 4824)] :=
  (lex_12_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_12_204_gate

end Crown.CertificateData
