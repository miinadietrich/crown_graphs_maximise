import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_8_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3724) = lexBefore s permutation8 204 := by
  exact (positive_lex_of_descriptor s 3724 permutation8 205 (by rfl)).trans ((lex_skipped s permutation8 204 205 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation8 204) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation8 204 by rw [image8_eq]; rfl))

theorem lex_8_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3725) (Sat.Literal.pos 3724) (Sat.Literal.pos 204) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation8 204 (assignment s)
    (Sat.Literal.pos 3725) (Sat.Literal.pos 3724) (Sat.Literal.pos 204) (Sat.Literal.pos 51) (positive_of_descriptor s 3725 (.lex permutation8 204) (by rfl)) (lex_8_204_prefix s) (positive_select s 204) (lex_8_204_image s)

theorem lex_8_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.pos 204), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation8 204 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3724) (Sat.Literal.pos 204) (Sat.Literal.pos 51) (lex_8_204_prefix s) (positive_select s 204) (lex_8_204_image s)

theorem lex_8_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.pos 3724)] :=
  (lex_8_204_gate s).prop _ (List.Mem.head _)

theorem lex_8_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.neg 204), (Sat.Literal.pos 51)] :=
  (lex_8_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.pos 204), (Sat.Literal.neg 51)] :=
  (lex_8_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.neg 204), (Sat.Literal.neg 51), (Sat.Literal.pos 3725)] :=
  (lex_8_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.pos 204), (Sat.Literal.pos 51), (Sat.Literal.pos 3725)] :=
  (lex_8_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3725) = lexBefore s permutation8 203 := by
  exact (positive_lex_of_descriptor s 3725 permutation8 204 (by rfl)).trans ((lex_skipped s permutation8 203 204 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation8 203) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation8 203 by rw [image8_eq]; rfl))

theorem lex_8_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3726) (Sat.Literal.pos 3725) (Sat.Literal.pos 203) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation8 203 (assignment s)
    (Sat.Literal.pos 3726) (Sat.Literal.pos 3725) (Sat.Literal.pos 203) (Sat.Literal.pos 47) (positive_of_descriptor s 3726 (.lex permutation8 203) (by rfl)) (lex_8_203_prefix s) (positive_select s 203) (lex_8_203_image s)

theorem lex_8_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.pos 203), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation8 203 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3725) (Sat.Literal.pos 203) (Sat.Literal.pos 47) (lex_8_203_prefix s) (positive_select s 203) (lex_8_203_image s)

theorem lex_8_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.pos 3725)] :=
  (lex_8_203_gate s).prop _ (List.Mem.head _)

theorem lex_8_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.neg 203), (Sat.Literal.pos 47)] :=
  (lex_8_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.pos 203), (Sat.Literal.neg 47)] :=
  (lex_8_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.neg 203), (Sat.Literal.neg 47), (Sat.Literal.pos 3726)] :=
  (lex_8_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3725), (Sat.Literal.pos 203), (Sat.Literal.pos 47), (Sat.Literal.pos 3726)] :=
  (lex_8_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3726) = lexBefore s permutation8 202 := by
  exact (positive_lex_of_descriptor s 3726 permutation8 203 (by rfl)).trans ((lex_skipped s permutation8 202 203 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation8 202) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation8 202 by rw [image8_eq]; rfl))

theorem lex_8_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3727) (Sat.Literal.pos 3726) (Sat.Literal.pos 202) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation8 202 (assignment s)
    (Sat.Literal.pos 3727) (Sat.Literal.pos 3726) (Sat.Literal.pos 202) (Sat.Literal.pos 43) (positive_of_descriptor s 3727 (.lex permutation8 202) (by rfl)) (lex_8_202_prefix s) (positive_select s 202) (lex_8_202_image s)

theorem lex_8_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.pos 202), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation8 202 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3726) (Sat.Literal.pos 202) (Sat.Literal.pos 43) (lex_8_202_prefix s) (positive_select s 202) (lex_8_202_image s)

theorem lex_8_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.pos 3726)] :=
  (lex_8_202_gate s).prop _ (List.Mem.head _)

theorem lex_8_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.neg 202), (Sat.Literal.pos 43)] :=
  (lex_8_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.pos 202), (Sat.Literal.neg 43)] :=
  (lex_8_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.neg 202), (Sat.Literal.neg 43), (Sat.Literal.pos 3727)] :=
  (lex_8_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3726), (Sat.Literal.pos 202), (Sat.Literal.pos 43), (Sat.Literal.pos 3727)] :=
  (lex_8_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3727) = lexBefore s permutation8 201 := by
  exact (positive_lex_of_descriptor s 3727 permutation8 202 (by rfl)).trans ((lex_skipped s permutation8 201 202 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation8 201) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation8 201 by rw [image8_eq]; rfl))

theorem lex_8_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3728) (Sat.Literal.pos 3727) (Sat.Literal.pos 201) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation8 201 (assignment s)
    (Sat.Literal.pos 3728) (Sat.Literal.pos 3727) (Sat.Literal.pos 201) (Sat.Literal.pos 39) (positive_of_descriptor s 3728 (.lex permutation8 201) (by rfl)) (lex_8_201_prefix s) (positive_select s 201) (lex_8_201_image s)

theorem lex_8_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.pos 201), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation8 201 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3727) (Sat.Literal.pos 201) (Sat.Literal.pos 39) (lex_8_201_prefix s) (positive_select s 201) (lex_8_201_image s)

theorem lex_8_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.pos 3727)] :=
  (lex_8_201_gate s).prop _ (List.Mem.head _)

theorem lex_8_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.neg 201), (Sat.Literal.pos 39)] :=
  (lex_8_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.pos 201), (Sat.Literal.neg 39)] :=
  (lex_8_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.neg 201), (Sat.Literal.neg 39), (Sat.Literal.pos 3728)] :=
  (lex_8_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3727), (Sat.Literal.pos 201), (Sat.Literal.pos 39), (Sat.Literal.pos 3728)] :=
  (lex_8_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3728) = lexBefore s permutation8 200 := by
  exact (positive_lex_of_descriptor s 3728 permutation8 201 (by rfl)).trans ((lex_skipped s permutation8 200 201 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation8 200) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation8 200 by rw [image8_eq]; rfl))

theorem lex_8_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3729) (Sat.Literal.pos 3728) (Sat.Literal.pos 200) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation8 200 (assignment s)
    (Sat.Literal.pos 3729) (Sat.Literal.pos 3728) (Sat.Literal.pos 200) (Sat.Literal.pos 35) (positive_of_descriptor s 3729 (.lex permutation8 200) (by rfl)) (lex_8_200_prefix s) (positive_select s 200) (lex_8_200_image s)

theorem lex_8_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.pos 200), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation8 200 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3728) (Sat.Literal.pos 200) (Sat.Literal.pos 35) (lex_8_200_prefix s) (positive_select s 200) (lex_8_200_image s)

theorem lex_8_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.pos 3728)] :=
  (lex_8_200_gate s).prop _ (List.Mem.head _)

theorem lex_8_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.neg 200), (Sat.Literal.pos 35)] :=
  (lex_8_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.pos 200), (Sat.Literal.neg 35)] :=
  (lex_8_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.neg 200), (Sat.Literal.neg 35), (Sat.Literal.pos 3729)] :=
  (lex_8_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3728), (Sat.Literal.pos 200), (Sat.Literal.pos 35), (Sat.Literal.pos 3729)] :=
  (lex_8_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3729) = lexBefore s permutation8 199 := by
  exact (positive_lex_of_descriptor s 3729 permutation8 200 (by rfl)).trans ((lex_skipped s permutation8 199 200 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation8 199) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation8 199 by rw [image8_eq]; rfl))

theorem lex_8_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3730) (Sat.Literal.pos 3729) (Sat.Literal.pos 199) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation8 199 (assignment s)
    (Sat.Literal.pos 3730) (Sat.Literal.pos 3729) (Sat.Literal.pos 199) (Sat.Literal.pos 31) (positive_of_descriptor s 3730 (.lex permutation8 199) (by rfl)) (lex_8_199_prefix s) (positive_select s 199) (lex_8_199_image s)

theorem lex_8_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.pos 199), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation8 199 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3729) (Sat.Literal.pos 199) (Sat.Literal.pos 31) (lex_8_199_prefix s) (positive_select s 199) (lex_8_199_image s)

theorem lex_8_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.pos 3729)] :=
  (lex_8_199_gate s).prop _ (List.Mem.head _)

theorem lex_8_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.neg 199), (Sat.Literal.pos 31)] :=
  (lex_8_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.pos 199), (Sat.Literal.neg 31)] :=
  (lex_8_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.neg 199), (Sat.Literal.neg 31), (Sat.Literal.pos 3730)] :=
  (lex_8_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3729), (Sat.Literal.pos 199), (Sat.Literal.pos 31), (Sat.Literal.pos 3730)] :=
  (lex_8_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3730) = lexBefore s permutation8 198 := by
  exact (positive_lex_of_descriptor s 3730 permutation8 199 (by rfl)).trans ((lex_skipped s permutation8 198 199 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation8 198) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation8 198 by rw [image8_eq]; rfl))

theorem lex_8_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3731) (Sat.Literal.pos 3730) (Sat.Literal.pos 198) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation8 198 (assignment s)
    (Sat.Literal.pos 3731) (Sat.Literal.pos 3730) (Sat.Literal.pos 198) (Sat.Literal.pos 27) (positive_of_descriptor s 3731 (.lex permutation8 198) (by rfl)) (lex_8_198_prefix s) (positive_select s 198) (lex_8_198_image s)

theorem lex_8_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.pos 198), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation8 198 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3730) (Sat.Literal.pos 198) (Sat.Literal.pos 27) (lex_8_198_prefix s) (positive_select s 198) (lex_8_198_image s)

theorem lex_8_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.pos 3730)] :=
  (lex_8_198_gate s).prop _ (List.Mem.head _)

theorem lex_8_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.neg 198), (Sat.Literal.pos 27)] :=
  (lex_8_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.pos 198), (Sat.Literal.neg 27)] :=
  (lex_8_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.neg 198), (Sat.Literal.neg 27), (Sat.Literal.pos 3731)] :=
  (lex_8_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3730), (Sat.Literal.pos 198), (Sat.Literal.pos 27), (Sat.Literal.pos 3731)] :=
  (lex_8_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3731) = lexBefore s permutation8 197 := by
  exact (positive_lex_of_descriptor s 3731 permutation8 198 (by rfl)).trans ((lex_skipped s permutation8 197 198 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation8 197) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation8 197 by rw [image8_eq]; rfl))

theorem lex_8_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3732) (Sat.Literal.pos 3731) (Sat.Literal.pos 197) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation8 197 (assignment s)
    (Sat.Literal.pos 3732) (Sat.Literal.pos 3731) (Sat.Literal.pos 197) (Sat.Literal.pos 23) (positive_of_descriptor s 3732 (.lex permutation8 197) (by rfl)) (lex_8_197_prefix s) (positive_select s 197) (lex_8_197_image s)

theorem lex_8_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.pos 197), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation8 197 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3731) (Sat.Literal.pos 197) (Sat.Literal.pos 23) (lex_8_197_prefix s) (positive_select s 197) (lex_8_197_image s)

theorem lex_8_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.pos 3731)] :=
  (lex_8_197_gate s).prop _ (List.Mem.head _)

theorem lex_8_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.neg 197), (Sat.Literal.pos 23)] :=
  (lex_8_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.pos 197), (Sat.Literal.neg 23)] :=
  (lex_8_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.neg 197), (Sat.Literal.neg 23), (Sat.Literal.pos 3732)] :=
  (lex_8_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3731), (Sat.Literal.pos 197), (Sat.Literal.pos 23), (Sat.Literal.pos 3732)] :=
  (lex_8_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3732) = lexBefore s permutation8 196 := by
  exact (positive_lex_of_descriptor s 3732 permutation8 197 (by rfl)).trans ((lex_skipped s permutation8 196 197 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation8 196) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation8 196 by rw [image8_eq]; rfl))

theorem lex_8_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3733) (Sat.Literal.pos 3732) (Sat.Literal.pos 196) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation8 196 (assignment s)
    (Sat.Literal.pos 3733) (Sat.Literal.pos 3732) (Sat.Literal.pos 196) (Sat.Literal.pos 19) (positive_of_descriptor s 3733 (.lex permutation8 196) (by rfl)) (lex_8_196_prefix s) (positive_select s 196) (lex_8_196_image s)

theorem lex_8_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.pos 196), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation8 196 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3732) (Sat.Literal.pos 196) (Sat.Literal.pos 19) (lex_8_196_prefix s) (positive_select s 196) (lex_8_196_image s)

theorem lex_8_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.pos 3732)] :=
  (lex_8_196_gate s).prop _ (List.Mem.head _)

theorem lex_8_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.neg 196), (Sat.Literal.pos 19)] :=
  (lex_8_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.pos 196), (Sat.Literal.neg 19)] :=
  (lex_8_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.neg 196), (Sat.Literal.neg 19), (Sat.Literal.pos 3733)] :=
  (lex_8_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3732), (Sat.Literal.pos 196), (Sat.Literal.pos 19), (Sat.Literal.pos 3733)] :=
  (lex_8_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3733) = lexBefore s permutation8 195 := by
  exact (positive_lex_of_descriptor s 3733 permutation8 196 (by rfl)).trans ((lex_skipped s permutation8 195 196 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation8 195) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation8 195 by rw [image8_eq]; rfl))

theorem lex_8_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3734) (Sat.Literal.pos 3733) (Sat.Literal.pos 195) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation8 195 (assignment s)
    (Sat.Literal.pos 3734) (Sat.Literal.pos 3733) (Sat.Literal.pos 195) (Sat.Literal.pos 15) (positive_of_descriptor s 3734 (.lex permutation8 195) (by rfl)) (lex_8_195_prefix s) (positive_select s 195) (lex_8_195_image s)

theorem lex_8_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.pos 195), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation8 195 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3733) (Sat.Literal.pos 195) (Sat.Literal.pos 15) (lex_8_195_prefix s) (positive_select s 195) (lex_8_195_image s)

theorem lex_8_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.pos 3733)] :=
  (lex_8_195_gate s).prop _ (List.Mem.head _)

theorem lex_8_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.neg 195), (Sat.Literal.pos 15)] :=
  (lex_8_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.pos 195), (Sat.Literal.neg 15)] :=
  (lex_8_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.neg 195), (Sat.Literal.neg 15), (Sat.Literal.pos 3734)] :=
  (lex_8_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3733), (Sat.Literal.pos 195), (Sat.Literal.pos 15), (Sat.Literal.pos 3734)] :=
  (lex_8_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3734) = lexBefore s permutation8 194 := by
  exact (positive_lex_of_descriptor s 3734 permutation8 195 (by rfl)).trans ((lex_skipped s permutation8 194 195 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation8 194) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation8 194 by rw [image8_eq]; rfl))

theorem lex_8_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3735) (Sat.Literal.pos 3734) (Sat.Literal.pos 194) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation8 194 (assignment s)
    (Sat.Literal.pos 3735) (Sat.Literal.pos 3734) (Sat.Literal.pos 194) (Sat.Literal.pos 11) (positive_of_descriptor s 3735 (.lex permutation8 194) (by rfl)) (lex_8_194_prefix s) (positive_select s 194) (lex_8_194_image s)

theorem lex_8_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.pos 194), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation8 194 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3734) (Sat.Literal.pos 194) (Sat.Literal.pos 11) (lex_8_194_prefix s) (positive_select s 194) (lex_8_194_image s)

theorem lex_8_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.pos 3734)] :=
  (lex_8_194_gate s).prop _ (List.Mem.head _)

theorem lex_8_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.neg 194), (Sat.Literal.pos 11)] :=
  (lex_8_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.pos 194), (Sat.Literal.neg 11)] :=
  (lex_8_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.neg 194), (Sat.Literal.neg 11), (Sat.Literal.pos 3735)] :=
  (lex_8_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3734), (Sat.Literal.pos 194), (Sat.Literal.pos 11), (Sat.Literal.pos 3735)] :=
  (lex_8_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3735) = lexBefore s permutation8 193 := by
  exact (positive_lex_of_descriptor s 3735 permutation8 194 (by rfl)).trans ((lex_skipped s permutation8 193 194 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation8 193) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation8 193 by rw [image8_eq]; rfl))

theorem lex_8_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3736) (Sat.Literal.pos 3735) (Sat.Literal.pos 193) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation8 193 (assignment s)
    (Sat.Literal.pos 3736) (Sat.Literal.pos 3735) (Sat.Literal.pos 193) (Sat.Literal.pos 7) (positive_of_descriptor s 3736 (.lex permutation8 193) (by rfl)) (lex_8_193_prefix s) (positive_select s 193) (lex_8_193_image s)

theorem lex_8_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.pos 193), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation8 193 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3735) (Sat.Literal.pos 193) (Sat.Literal.pos 7) (lex_8_193_prefix s) (positive_select s 193) (lex_8_193_image s)

theorem lex_8_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.pos 3735)] :=
  (lex_8_193_gate s).prop _ (List.Mem.head _)

theorem lex_8_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.neg 193), (Sat.Literal.pos 7)] :=
  (lex_8_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.pos 193), (Sat.Literal.neg 7)] :=
  (lex_8_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.neg 193), (Sat.Literal.neg 7), (Sat.Literal.pos 3736)] :=
  (lex_8_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3735), (Sat.Literal.pos 193), (Sat.Literal.pos 7), (Sat.Literal.pos 3736)] :=
  (lex_8_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3736) = lexBefore s permutation8 192 := by
  exact (positive_lex_of_descriptor s 3736 permutation8 193 (by rfl)).trans ((lex_skipped s permutation8 192 193 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation8 192) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation8 192 by rw [image8_eq]; rfl))

theorem lex_8_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3737) (Sat.Literal.pos 3736) (Sat.Literal.pos 192) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation8 192 (assignment s)
    (Sat.Literal.pos 3737) (Sat.Literal.pos 3736) (Sat.Literal.pos 192) (Sat.Literal.pos 3) (positive_of_descriptor s 3737 (.lex permutation8 192) (by rfl)) (lex_8_192_prefix s) (positive_select s 192) (lex_8_192_image s)

theorem lex_8_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.pos 192), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation8 192 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3736) (Sat.Literal.pos 192) (Sat.Literal.pos 3) (lex_8_192_prefix s) (positive_select s 192) (lex_8_192_image s)

theorem lex_8_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.pos 3736)] :=
  (lex_8_192_gate s).prop _ (List.Mem.head _)

theorem lex_8_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.neg 192), (Sat.Literal.pos 3)] :=
  (lex_8_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.pos 192), (Sat.Literal.neg 3)] :=
  (lex_8_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.neg 192), (Sat.Literal.neg 3), (Sat.Literal.pos 3737)] :=
  (lex_8_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3736), (Sat.Literal.pos 192), (Sat.Literal.pos 3), (Sat.Literal.pos 3737)] :=
  (lex_8_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3737) = lexBefore s permutation8 191 := by
  exact (positive_lex_of_descriptor s 3737 permutation8 192 (by rfl)).trans ((lex_skipped s permutation8 191 192 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation8 191) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation8 191 by rw [image8_eq]; rfl))

theorem lex_8_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3738) (Sat.Literal.pos 3737) (Sat.Literal.pos 191) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation8 191 (assignment s)
    (Sat.Literal.pos 3738) (Sat.Literal.pos 3737) (Sat.Literal.pos 191) (Sat.Literal.pos 254) (positive_of_descriptor s 3738 (.lex permutation8 191) (by rfl)) (lex_8_191_prefix s) (positive_select s 191) (lex_8_191_image s)

theorem lex_8_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.pos 191), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation8 191 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3737) (Sat.Literal.pos 191) (Sat.Literal.pos 254) (lex_8_191_prefix s) (positive_select s 191) (lex_8_191_image s)

theorem lex_8_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.pos 3737)] :=
  (lex_8_191_gate s).prop _ (List.Mem.head _)

theorem lex_8_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.neg 191), (Sat.Literal.pos 254)] :=
  (lex_8_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.pos 191), (Sat.Literal.neg 254)] :=
  (lex_8_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.neg 191), (Sat.Literal.neg 254), (Sat.Literal.pos 3738)] :=
  (lex_8_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3737), (Sat.Literal.pos 191), (Sat.Literal.pos 254), (Sat.Literal.pos 3738)] :=
  (lex_8_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3738) = lexBefore s permutation8 190 := by
  exact (positive_lex_of_descriptor s 3738 permutation8 191 (by rfl)).trans ((lex_skipped s permutation8 190 191 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation8 190) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation8 190 by rw [image8_eq]; rfl))

theorem lex_8_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3739) (Sat.Literal.pos 3738) (Sat.Literal.pos 190) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation8 190 (assignment s)
    (Sat.Literal.pos 3739) (Sat.Literal.pos 3738) (Sat.Literal.pos 190) (Sat.Literal.pos 250) (positive_of_descriptor s 3739 (.lex permutation8 190) (by rfl)) (lex_8_190_prefix s) (positive_select s 190) (lex_8_190_image s)

theorem lex_8_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.pos 190), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation8 190 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3738) (Sat.Literal.pos 190) (Sat.Literal.pos 250) (lex_8_190_prefix s) (positive_select s 190) (lex_8_190_image s)

theorem lex_8_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.pos 3738)] :=
  (lex_8_190_gate s).prop _ (List.Mem.head _)

theorem lex_8_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.neg 190), (Sat.Literal.pos 250)] :=
  (lex_8_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.pos 190), (Sat.Literal.neg 250)] :=
  (lex_8_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.neg 190), (Sat.Literal.neg 250), (Sat.Literal.pos 3739)] :=
  (lex_8_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3738), (Sat.Literal.pos 190), (Sat.Literal.pos 250), (Sat.Literal.pos 3739)] :=
  (lex_8_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3739) = lexBefore s permutation8 189 := by
  exact (positive_lex_of_descriptor s 3739 permutation8 190 (by rfl)).trans ((lex_skipped s permutation8 189 190 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation8 189) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation8 189 by rw [image8_eq]; rfl))

theorem lex_8_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3740) (Sat.Literal.pos 3739) (Sat.Literal.pos 189) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation8 189 (assignment s)
    (Sat.Literal.pos 3740) (Sat.Literal.pos 3739) (Sat.Literal.pos 189) (Sat.Literal.pos 246) (positive_of_descriptor s 3740 (.lex permutation8 189) (by rfl)) (lex_8_189_prefix s) (positive_select s 189) (lex_8_189_image s)

theorem lex_8_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.pos 189), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation8 189 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3739) (Sat.Literal.pos 189) (Sat.Literal.pos 246) (lex_8_189_prefix s) (positive_select s 189) (lex_8_189_image s)

theorem lex_8_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.pos 3739)] :=
  (lex_8_189_gate s).prop _ (List.Mem.head _)

theorem lex_8_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.neg 189), (Sat.Literal.pos 246)] :=
  (lex_8_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.pos 189), (Sat.Literal.neg 246)] :=
  (lex_8_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.neg 189), (Sat.Literal.neg 246), (Sat.Literal.pos 3740)] :=
  (lex_8_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3739), (Sat.Literal.pos 189), (Sat.Literal.pos 246), (Sat.Literal.pos 3740)] :=
  (lex_8_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3740) = lexBefore s permutation8 188 := by
  exact (positive_lex_of_descriptor s 3740 permutation8 189 (by rfl)).trans ((lex_skipped s permutation8 188 189 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation8 188) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation8 188 by rw [image8_eq]; rfl))

theorem lex_8_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3741) (Sat.Literal.pos 3740) (Sat.Literal.pos 188) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation8 188 (assignment s)
    (Sat.Literal.pos 3741) (Sat.Literal.pos 3740) (Sat.Literal.pos 188) (Sat.Literal.pos 242) (positive_of_descriptor s 3741 (.lex permutation8 188) (by rfl)) (lex_8_188_prefix s) (positive_select s 188) (lex_8_188_image s)

theorem lex_8_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.pos 188), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation8 188 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3740) (Sat.Literal.pos 188) (Sat.Literal.pos 242) (lex_8_188_prefix s) (positive_select s 188) (lex_8_188_image s)

theorem lex_8_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.pos 3740)] :=
  (lex_8_188_gate s).prop _ (List.Mem.head _)

theorem lex_8_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.neg 188), (Sat.Literal.pos 242)] :=
  (lex_8_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.pos 188), (Sat.Literal.neg 242)] :=
  (lex_8_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.neg 188), (Sat.Literal.neg 242), (Sat.Literal.pos 3741)] :=
  (lex_8_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3740), (Sat.Literal.pos 188), (Sat.Literal.pos 242), (Sat.Literal.pos 3741)] :=
  (lex_8_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3741) = lexBefore s permutation8 187 := by
  exact (positive_lex_of_descriptor s 3741 permutation8 188 (by rfl)).trans ((lex_skipped s permutation8 187 188 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation8 187) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation8 187 by rw [image8_eq]; rfl))

theorem lex_8_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3742) (Sat.Literal.pos 3741) (Sat.Literal.pos 187) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation8 187 (assignment s)
    (Sat.Literal.pos 3742) (Sat.Literal.pos 3741) (Sat.Literal.pos 187) (Sat.Literal.pos 238) (positive_of_descriptor s 3742 (.lex permutation8 187) (by rfl)) (lex_8_187_prefix s) (positive_select s 187) (lex_8_187_image s)

theorem lex_8_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.pos 187), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation8 187 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3741) (Sat.Literal.pos 187) (Sat.Literal.pos 238) (lex_8_187_prefix s) (positive_select s 187) (lex_8_187_image s)

theorem lex_8_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.pos 3741)] :=
  (lex_8_187_gate s).prop _ (List.Mem.head _)

theorem lex_8_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.neg 187), (Sat.Literal.pos 238)] :=
  (lex_8_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.pos 187), (Sat.Literal.neg 238)] :=
  (lex_8_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.neg 187), (Sat.Literal.neg 238), (Sat.Literal.pos 3742)] :=
  (lex_8_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3741), (Sat.Literal.pos 187), (Sat.Literal.pos 238), (Sat.Literal.pos 3742)] :=
  (lex_8_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3742) = lexBefore s permutation8 186 := by
  exact (positive_lex_of_descriptor s 3742 permutation8 187 (by rfl)).trans ((lex_skipped s permutation8 186 187 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation8 186) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation8 186 by rw [image8_eq]; rfl))

theorem lex_8_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3743) (Sat.Literal.pos 3742) (Sat.Literal.pos 186) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation8 186 (assignment s)
    (Sat.Literal.pos 3743) (Sat.Literal.pos 3742) (Sat.Literal.pos 186) (Sat.Literal.pos 234) (positive_of_descriptor s 3743 (.lex permutation8 186) (by rfl)) (lex_8_186_prefix s) (positive_select s 186) (lex_8_186_image s)

theorem lex_8_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.pos 186), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation8 186 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3742) (Sat.Literal.pos 186) (Sat.Literal.pos 234) (lex_8_186_prefix s) (positive_select s 186) (lex_8_186_image s)

theorem lex_8_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.pos 3742)] :=
  (lex_8_186_gate s).prop _ (List.Mem.head _)

theorem lex_8_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.neg 186), (Sat.Literal.pos 234)] :=
  (lex_8_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.pos 186), (Sat.Literal.neg 234)] :=
  (lex_8_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.neg 186), (Sat.Literal.neg 234), (Sat.Literal.pos 3743)] :=
  (lex_8_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3742), (Sat.Literal.pos 186), (Sat.Literal.pos 234), (Sat.Literal.pos 3743)] :=
  (lex_8_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3743) = lexBefore s permutation8 185 := by
  exact (positive_lex_of_descriptor s 3743 permutation8 186 (by rfl)).trans ((lex_skipped s permutation8 185 186 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation8 185) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation8 185 by rw [image8_eq]; rfl))

theorem lex_8_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3744) (Sat.Literal.pos 3743) (Sat.Literal.pos 185) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation8 185 (assignment s)
    (Sat.Literal.pos 3744) (Sat.Literal.pos 3743) (Sat.Literal.pos 185) (Sat.Literal.pos 230) (positive_of_descriptor s 3744 (.lex permutation8 185) (by rfl)) (lex_8_185_prefix s) (positive_select s 185) (lex_8_185_image s)

theorem lex_8_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.pos 185), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation8 185 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3743) (Sat.Literal.pos 185) (Sat.Literal.pos 230) (lex_8_185_prefix s) (positive_select s 185) (lex_8_185_image s)

theorem lex_8_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.pos 3743)] :=
  (lex_8_185_gate s).prop _ (List.Mem.head _)

theorem lex_8_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.neg 185), (Sat.Literal.pos 230)] :=
  (lex_8_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.pos 185), (Sat.Literal.neg 230)] :=
  (lex_8_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.neg 185), (Sat.Literal.neg 230), (Sat.Literal.pos 3744)] :=
  (lex_8_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3743), (Sat.Literal.pos 185), (Sat.Literal.pos 230), (Sat.Literal.pos 3744)] :=
  (lex_8_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3744) = lexBefore s permutation8 184 := by
  exact (positive_lex_of_descriptor s 3744 permutation8 185 (by rfl)).trans ((lex_skipped s permutation8 184 185 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation8 184) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation8 184 by rw [image8_eq]; rfl))

theorem lex_8_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3745) (Sat.Literal.pos 3744) (Sat.Literal.pos 184) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation8 184 (assignment s)
    (Sat.Literal.pos 3745) (Sat.Literal.pos 3744) (Sat.Literal.pos 184) (Sat.Literal.pos 226) (positive_of_descriptor s 3745 (.lex permutation8 184) (by rfl)) (lex_8_184_prefix s) (positive_select s 184) (lex_8_184_image s)

theorem lex_8_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.pos 184), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation8 184 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3744) (Sat.Literal.pos 184) (Sat.Literal.pos 226) (lex_8_184_prefix s) (positive_select s 184) (lex_8_184_image s)

theorem lex_8_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.pos 3744)] :=
  (lex_8_184_gate s).prop _ (List.Mem.head _)

theorem lex_8_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.neg 184), (Sat.Literal.pos 226)] :=
  (lex_8_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.pos 184), (Sat.Literal.neg 226)] :=
  (lex_8_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.neg 184), (Sat.Literal.neg 226), (Sat.Literal.pos 3745)] :=
  (lex_8_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3744), (Sat.Literal.pos 184), (Sat.Literal.pos 226), (Sat.Literal.pos 3745)] :=
  (lex_8_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3745) = lexBefore s permutation8 183 := by
  exact (positive_lex_of_descriptor s 3745 permutation8 184 (by rfl)).trans ((lex_skipped s permutation8 183 184 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation8 183) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation8 183 by rw [image8_eq]; rfl))

theorem lex_8_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3746) (Sat.Literal.pos 3745) (Sat.Literal.pos 183) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation8 183 (assignment s)
    (Sat.Literal.pos 3746) (Sat.Literal.pos 3745) (Sat.Literal.pos 183) (Sat.Literal.pos 222) (positive_of_descriptor s 3746 (.lex permutation8 183) (by rfl)) (lex_8_183_prefix s) (positive_select s 183) (lex_8_183_image s)

theorem lex_8_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.pos 183), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation8 183 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3745) (Sat.Literal.pos 183) (Sat.Literal.pos 222) (lex_8_183_prefix s) (positive_select s 183) (lex_8_183_image s)

theorem lex_8_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.pos 3745)] :=
  (lex_8_183_gate s).prop _ (List.Mem.head _)

theorem lex_8_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.neg 183), (Sat.Literal.pos 222)] :=
  (lex_8_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.pos 183), (Sat.Literal.neg 222)] :=
  (lex_8_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.neg 183), (Sat.Literal.neg 222), (Sat.Literal.pos 3746)] :=
  (lex_8_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3745), (Sat.Literal.pos 183), (Sat.Literal.pos 222), (Sat.Literal.pos 3746)] :=
  (lex_8_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3746) = lexBefore s permutation8 182 := by
  exact (positive_lex_of_descriptor s 3746 permutation8 183 (by rfl)).trans ((lex_skipped s permutation8 182 183 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation8 182) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation8 182 by rw [image8_eq]; rfl))

theorem lex_8_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3747) (Sat.Literal.pos 3746) (Sat.Literal.pos 182) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation8 182 (assignment s)
    (Sat.Literal.pos 3747) (Sat.Literal.pos 3746) (Sat.Literal.pos 182) (Sat.Literal.pos 218) (positive_of_descriptor s 3747 (.lex permutation8 182) (by rfl)) (lex_8_182_prefix s) (positive_select s 182) (lex_8_182_image s)

theorem lex_8_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.pos 182), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation8 182 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3746) (Sat.Literal.pos 182) (Sat.Literal.pos 218) (lex_8_182_prefix s) (positive_select s 182) (lex_8_182_image s)

theorem lex_8_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.pos 3746)] :=
  (lex_8_182_gate s).prop _ (List.Mem.head _)

theorem lex_8_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.neg 182), (Sat.Literal.pos 218)] :=
  (lex_8_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.pos 182), (Sat.Literal.neg 218)] :=
  (lex_8_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.neg 182), (Sat.Literal.neg 218), (Sat.Literal.pos 3747)] :=
  (lex_8_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3746), (Sat.Literal.pos 182), (Sat.Literal.pos 218), (Sat.Literal.pos 3747)] :=
  (lex_8_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3747) = lexBefore s permutation8 181 := by
  exact (positive_lex_of_descriptor s 3747 permutation8 182 (by rfl)).trans ((lex_skipped s permutation8 181 182 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation8 181) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation8 181 by rw [image8_eq]; rfl))

theorem lex_8_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3748) (Sat.Literal.pos 3747) (Sat.Literal.pos 181) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation8 181 (assignment s)
    (Sat.Literal.pos 3748) (Sat.Literal.pos 3747) (Sat.Literal.pos 181) (Sat.Literal.pos 214) (positive_of_descriptor s 3748 (.lex permutation8 181) (by rfl)) (lex_8_181_prefix s) (positive_select s 181) (lex_8_181_image s)

theorem lex_8_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.pos 181), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation8 181 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3747) (Sat.Literal.pos 181) (Sat.Literal.pos 214) (lex_8_181_prefix s) (positive_select s 181) (lex_8_181_image s)

theorem lex_8_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.pos 3747)] :=
  (lex_8_181_gate s).prop _ (List.Mem.head _)

theorem lex_8_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.neg 181), (Sat.Literal.pos 214)] :=
  (lex_8_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.pos 181), (Sat.Literal.neg 214)] :=
  (lex_8_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.neg 181), (Sat.Literal.neg 214), (Sat.Literal.pos 3748)] :=
  (lex_8_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3747), (Sat.Literal.pos 181), (Sat.Literal.pos 214), (Sat.Literal.pos 3748)] :=
  (lex_8_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3748) = lexBefore s permutation8 180 := by
  exact (positive_lex_of_descriptor s 3748 permutation8 181 (by rfl)).trans ((lex_skipped s permutation8 180 181 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation8 180) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation8 180 by rw [image8_eq]; rfl))

theorem lex_8_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3749) (Sat.Literal.pos 3748) (Sat.Literal.pos 180) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation8 180 (assignment s)
    (Sat.Literal.pos 3749) (Sat.Literal.pos 3748) (Sat.Literal.pos 180) (Sat.Literal.pos 210) (positive_of_descriptor s 3749 (.lex permutation8 180) (by rfl)) (lex_8_180_prefix s) (positive_select s 180) (lex_8_180_image s)

theorem lex_8_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.pos 180), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation8 180 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3748) (Sat.Literal.pos 180) (Sat.Literal.pos 210) (lex_8_180_prefix s) (positive_select s 180) (lex_8_180_image s)

theorem lex_8_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.pos 3748)] :=
  (lex_8_180_gate s).prop _ (List.Mem.head _)

theorem lex_8_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.neg 180), (Sat.Literal.pos 210)] :=
  (lex_8_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.pos 180), (Sat.Literal.neg 210)] :=
  (lex_8_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.neg 180), (Sat.Literal.neg 210), (Sat.Literal.pos 3749)] :=
  (lex_8_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3748), (Sat.Literal.pos 180), (Sat.Literal.pos 210), (Sat.Literal.pos 3749)] :=
  (lex_8_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3749) = lexBefore s permutation8 179 := by
  exact (positive_lex_of_descriptor s 3749 permutation8 180 (by rfl)).trans ((lex_skipped s permutation8 179 180 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation8 179) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation8 179 by rw [image8_eq]; rfl))

theorem lex_8_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3750) (Sat.Literal.pos 3749) (Sat.Literal.pos 179) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation8 179 (assignment s)
    (Sat.Literal.pos 3750) (Sat.Literal.pos 3749) (Sat.Literal.pos 179) (Sat.Literal.pos 206) (positive_of_descriptor s 3750 (.lex permutation8 179) (by rfl)) (lex_8_179_prefix s) (positive_select s 179) (lex_8_179_image s)

theorem lex_8_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.pos 179), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation8 179 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3749) (Sat.Literal.pos 179) (Sat.Literal.pos 206) (lex_8_179_prefix s) (positive_select s 179) (lex_8_179_image s)

theorem lex_8_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.pos 3749)] :=
  (lex_8_179_gate s).prop _ (List.Mem.head _)

theorem lex_8_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.neg 179), (Sat.Literal.pos 206)] :=
  (lex_8_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.pos 179), (Sat.Literal.neg 206)] :=
  (lex_8_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.neg 179), (Sat.Literal.neg 206), (Sat.Literal.pos 3750)] :=
  (lex_8_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3749), (Sat.Literal.pos 179), (Sat.Literal.pos 206), (Sat.Literal.pos 3750)] :=
  (lex_8_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3750) = lexBefore s permutation8 178 := by
  exact (positive_lex_of_descriptor s 3750 permutation8 179 (by rfl)).trans ((lex_skipped s permutation8 178 179 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation8 178) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation8 178 by rw [image8_eq]; rfl))

theorem lex_8_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3751) (Sat.Literal.pos 3750) (Sat.Literal.pos 178) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation8 178 (assignment s)
    (Sat.Literal.pos 3751) (Sat.Literal.pos 3750) (Sat.Literal.pos 178) (Sat.Literal.pos 202) (positive_of_descriptor s 3751 (.lex permutation8 178) (by rfl)) (lex_8_178_prefix s) (positive_select s 178) (lex_8_178_image s)

theorem lex_8_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.pos 178), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation8 178 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3750) (Sat.Literal.pos 178) (Sat.Literal.pos 202) (lex_8_178_prefix s) (positive_select s 178) (lex_8_178_image s)

theorem lex_8_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.pos 3750)] :=
  (lex_8_178_gate s).prop _ (List.Mem.head _)

theorem lex_8_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.neg 178), (Sat.Literal.pos 202)] :=
  (lex_8_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.pos 178), (Sat.Literal.neg 202)] :=
  (lex_8_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.neg 178), (Sat.Literal.neg 202), (Sat.Literal.pos 3751)] :=
  (lex_8_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3750), (Sat.Literal.pos 178), (Sat.Literal.pos 202), (Sat.Literal.pos 3751)] :=
  (lex_8_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3751) = lexBefore s permutation8 177 := by
  exact (positive_lex_of_descriptor s 3751 permutation8 178 (by rfl)).trans ((lex_skipped s permutation8 177 178 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation8 177) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation8 177 by rw [image8_eq]; rfl))

theorem lex_8_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3752) (Sat.Literal.pos 3751) (Sat.Literal.pos 177) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation8 177 (assignment s)
    (Sat.Literal.pos 3752) (Sat.Literal.pos 3751) (Sat.Literal.pos 177) (Sat.Literal.pos 198) (positive_of_descriptor s 3752 (.lex permutation8 177) (by rfl)) (lex_8_177_prefix s) (positive_select s 177) (lex_8_177_image s)

theorem lex_8_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.pos 177), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation8 177 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3751) (Sat.Literal.pos 177) (Sat.Literal.pos 198) (lex_8_177_prefix s) (positive_select s 177) (lex_8_177_image s)

theorem lex_8_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.pos 3751)] :=
  (lex_8_177_gate s).prop _ (List.Mem.head _)

theorem lex_8_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.neg 177), (Sat.Literal.pos 198)] :=
  (lex_8_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.pos 177), (Sat.Literal.neg 198)] :=
  (lex_8_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.neg 177), (Sat.Literal.neg 198), (Sat.Literal.pos 3752)] :=
  (lex_8_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3751), (Sat.Literal.pos 177), (Sat.Literal.pos 198), (Sat.Literal.pos 3752)] :=
  (lex_8_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3752) = lexBefore s permutation8 176 := by
  exact (positive_lex_of_descriptor s 3752 permutation8 177 (by rfl)).trans ((lex_skipped s permutation8 176 177 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation8 176) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation8 176 by rw [image8_eq]; rfl))

theorem lex_8_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3753) (Sat.Literal.pos 3752) (Sat.Literal.pos 176) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation8 176 (assignment s)
    (Sat.Literal.pos 3753) (Sat.Literal.pos 3752) (Sat.Literal.pos 176) (Sat.Literal.pos 194) (positive_of_descriptor s 3753 (.lex permutation8 176) (by rfl)) (lex_8_176_prefix s) (positive_select s 176) (lex_8_176_image s)

theorem lex_8_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.pos 176), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation8 176 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3752) (Sat.Literal.pos 176) (Sat.Literal.pos 194) (lex_8_176_prefix s) (positive_select s 176) (lex_8_176_image s)

theorem lex_8_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.pos 3752)] :=
  (lex_8_176_gate s).prop _ (List.Mem.head _)

theorem lex_8_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.neg 176), (Sat.Literal.pos 194)] :=
  (lex_8_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.pos 176), (Sat.Literal.neg 194)] :=
  (lex_8_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.neg 176), (Sat.Literal.neg 194), (Sat.Literal.pos 3753)] :=
  (lex_8_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3752), (Sat.Literal.pos 176), (Sat.Literal.pos 194), (Sat.Literal.pos 3753)] :=
  (lex_8_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3753) = lexBefore s permutation8 175 := by
  exact (positive_lex_of_descriptor s 3753 permutation8 176 (by rfl)).trans ((lex_skipped s permutation8 175 176 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation8 175) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation8 175 by rw [image8_eq]; rfl))

theorem lex_8_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3754) (Sat.Literal.pos 3753) (Sat.Literal.pos 175) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation8 175 (assignment s)
    (Sat.Literal.pos 3754) (Sat.Literal.pos 3753) (Sat.Literal.pos 175) (Sat.Literal.pos 190) (positive_of_descriptor s 3754 (.lex permutation8 175) (by rfl)) (lex_8_175_prefix s) (positive_select s 175) (lex_8_175_image s)

theorem lex_8_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.pos 175), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation8 175 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3753) (Sat.Literal.pos 175) (Sat.Literal.pos 190) (lex_8_175_prefix s) (positive_select s 175) (lex_8_175_image s)

theorem lex_8_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.pos 3753)] :=
  (lex_8_175_gate s).prop _ (List.Mem.head _)

theorem lex_8_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.neg 175), (Sat.Literal.pos 190)] :=
  (lex_8_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.pos 175), (Sat.Literal.neg 190)] :=
  (lex_8_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.neg 175), (Sat.Literal.neg 190), (Sat.Literal.pos 3754)] :=
  (lex_8_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3753), (Sat.Literal.pos 175), (Sat.Literal.pos 190), (Sat.Literal.pos 3754)] :=
  (lex_8_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3754) = lexBefore s permutation8 174 := by
  exact (positive_lex_of_descriptor s 3754 permutation8 175 (by rfl)).trans ((lex_skipped s permutation8 174 175 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation8 174) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation8 174 by rw [image8_eq]; rfl))

theorem lex_8_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3755) (Sat.Literal.pos 3754) (Sat.Literal.pos 174) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation8 174 (assignment s)
    (Sat.Literal.pos 3755) (Sat.Literal.pos 3754) (Sat.Literal.pos 174) (Sat.Literal.pos 186) (positive_of_descriptor s 3755 (.lex permutation8 174) (by rfl)) (lex_8_174_prefix s) (positive_select s 174) (lex_8_174_image s)

theorem lex_8_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.pos 174), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation8 174 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3754) (Sat.Literal.pos 174) (Sat.Literal.pos 186) (lex_8_174_prefix s) (positive_select s 174) (lex_8_174_image s)

theorem lex_8_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.pos 3754)] :=
  (lex_8_174_gate s).prop _ (List.Mem.head _)

theorem lex_8_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.neg 174), (Sat.Literal.pos 186)] :=
  (lex_8_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.pos 174), (Sat.Literal.neg 186)] :=
  (lex_8_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.neg 174), (Sat.Literal.neg 186), (Sat.Literal.pos 3755)] :=
  (lex_8_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3754), (Sat.Literal.pos 174), (Sat.Literal.pos 186), (Sat.Literal.pos 3755)] :=
  (lex_8_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3755) = lexBefore s permutation8 173 := by
  exact (positive_lex_of_descriptor s 3755 permutation8 174 (by rfl)).trans ((lex_skipped s permutation8 173 174 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation8 173) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation8 173 by rw [image8_eq]; rfl))

theorem lex_8_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3756) (Sat.Literal.pos 3755) (Sat.Literal.pos 173) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation8 173 (assignment s)
    (Sat.Literal.pos 3756) (Sat.Literal.pos 3755) (Sat.Literal.pos 173) (Sat.Literal.pos 182) (positive_of_descriptor s 3756 (.lex permutation8 173) (by rfl)) (lex_8_173_prefix s) (positive_select s 173) (lex_8_173_image s)

theorem lex_8_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.pos 173), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation8 173 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3755) (Sat.Literal.pos 173) (Sat.Literal.pos 182) (lex_8_173_prefix s) (positive_select s 173) (lex_8_173_image s)

theorem lex_8_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.pos 3755)] :=
  (lex_8_173_gate s).prop _ (List.Mem.head _)

theorem lex_8_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.neg 173), (Sat.Literal.pos 182)] :=
  (lex_8_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.pos 173), (Sat.Literal.neg 182)] :=
  (lex_8_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.neg 173), (Sat.Literal.neg 182), (Sat.Literal.pos 3756)] :=
  (lex_8_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3755), (Sat.Literal.pos 173), (Sat.Literal.pos 182), (Sat.Literal.pos 3756)] :=
  (lex_8_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3756) = lexBefore s permutation8 172 := by
  exact (positive_lex_of_descriptor s 3756 permutation8 173 (by rfl)).trans ((lex_skipped s permutation8 172 173 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation8 172) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation8 172 by rw [image8_eq]; rfl))

theorem lex_8_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3757) (Sat.Literal.pos 3756) (Sat.Literal.pos 172) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation8 172 (assignment s)
    (Sat.Literal.pos 3757) (Sat.Literal.pos 3756) (Sat.Literal.pos 172) (Sat.Literal.pos 178) (positive_of_descriptor s 3757 (.lex permutation8 172) (by rfl)) (lex_8_172_prefix s) (positive_select s 172) (lex_8_172_image s)

theorem lex_8_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.pos 172), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation8 172 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3756) (Sat.Literal.pos 172) (Sat.Literal.pos 178) (lex_8_172_prefix s) (positive_select s 172) (lex_8_172_image s)

theorem lex_8_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.pos 3756)] :=
  (lex_8_172_gate s).prop _ (List.Mem.head _)

theorem lex_8_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.neg 172), (Sat.Literal.pos 178)] :=
  (lex_8_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.pos 172), (Sat.Literal.neg 178)] :=
  (lex_8_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.neg 172), (Sat.Literal.neg 178), (Sat.Literal.pos 3757)] :=
  (lex_8_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3756), (Sat.Literal.pos 172), (Sat.Literal.pos 178), (Sat.Literal.pos 3757)] :=
  (lex_8_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3757) = lexBefore s permutation8 171 := by
  exact (positive_lex_of_descriptor s 3757 permutation8 172 (by rfl)).trans ((lex_skipped s permutation8 171 172 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation8 171) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation8 171 by rw [image8_eq]; rfl))

theorem lex_8_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3758) (Sat.Literal.pos 3757) (Sat.Literal.pos 171) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation8 171 (assignment s)
    (Sat.Literal.pos 3758) (Sat.Literal.pos 3757) (Sat.Literal.pos 171) (Sat.Literal.pos 174) (positive_of_descriptor s 3758 (.lex permutation8 171) (by rfl)) (lex_8_171_prefix s) (positive_select s 171) (lex_8_171_image s)

theorem lex_8_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.pos 171), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation8 171 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3757) (Sat.Literal.pos 171) (Sat.Literal.pos 174) (lex_8_171_prefix s) (positive_select s 171) (lex_8_171_image s)

theorem lex_8_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.pos 3757)] :=
  (lex_8_171_gate s).prop _ (List.Mem.head _)

theorem lex_8_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.neg 171), (Sat.Literal.pos 174)] :=
  (lex_8_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.pos 171), (Sat.Literal.neg 174)] :=
  (lex_8_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.neg 171), (Sat.Literal.neg 174), (Sat.Literal.pos 3758)] :=
  (lex_8_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3757), (Sat.Literal.pos 171), (Sat.Literal.pos 174), (Sat.Literal.pos 3758)] :=
  (lex_8_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3758) = lexBefore s permutation8 169 := by
  exact (positive_lex_of_descriptor s 3758 permutation8 171 (by rfl)).trans ((lex_skipped s permutation8 169 171 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 170 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation8 169) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation8 169 by rw [image8_eq]; rfl))

theorem lex_8_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3759) (Sat.Literal.pos 3758) (Sat.Literal.pos 169) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation8 169 (assignment s)
    (Sat.Literal.pos 3759) (Sat.Literal.pos 3758) (Sat.Literal.pos 169) (Sat.Literal.pos 166) (positive_of_descriptor s 3759 (.lex permutation8 169) (by rfl)) (lex_8_169_prefix s) (positive_select s 169) (lex_8_169_image s)

theorem lex_8_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.pos 169), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation8 169 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3758) (Sat.Literal.pos 169) (Sat.Literal.pos 166) (lex_8_169_prefix s) (positive_select s 169) (lex_8_169_image s)

theorem lex_8_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.pos 3758)] :=
  (lex_8_169_gate s).prop _ (List.Mem.head _)

theorem lex_8_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.neg 169), (Sat.Literal.pos 166)] :=
  (lex_8_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.pos 169), (Sat.Literal.neg 166)] :=
  (lex_8_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.neg 169), (Sat.Literal.neg 166), (Sat.Literal.pos 3759)] :=
  (lex_8_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3758), (Sat.Literal.pos 169), (Sat.Literal.pos 166), (Sat.Literal.pos 3759)] :=
  (lex_8_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3759) = lexBefore s permutation8 168 := by
  exact (positive_lex_of_descriptor s 3759 permutation8 169 (by rfl)).trans ((lex_skipped s permutation8 168 169 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation8 168) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation8 168 by rw [image8_eq]; rfl))

theorem lex_8_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3760) (Sat.Literal.pos 3759) (Sat.Literal.pos 168) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation8 168 (assignment s)
    (Sat.Literal.pos 3760) (Sat.Literal.pos 3759) (Sat.Literal.pos 168) (Sat.Literal.pos 162) (positive_of_descriptor s 3760 (.lex permutation8 168) (by rfl)) (lex_8_168_prefix s) (positive_select s 168) (lex_8_168_image s)

theorem lex_8_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.pos 168), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation8 168 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3759) (Sat.Literal.pos 168) (Sat.Literal.pos 162) (lex_8_168_prefix s) (positive_select s 168) (lex_8_168_image s)

theorem lex_8_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.pos 3759)] :=
  (lex_8_168_gate s).prop _ (List.Mem.head _)

theorem lex_8_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.neg 168), (Sat.Literal.pos 162)] :=
  (lex_8_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.pos 168), (Sat.Literal.neg 162)] :=
  (lex_8_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.neg 168), (Sat.Literal.neg 162), (Sat.Literal.pos 3760)] :=
  (lex_8_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3759), (Sat.Literal.pos 168), (Sat.Literal.pos 162), (Sat.Literal.pos 3760)] :=
  (lex_8_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3760) = lexBefore s permutation8 167 := by
  exact (positive_lex_of_descriptor s 3760 permutation8 168 (by rfl)).trans ((lex_skipped s permutation8 167 168 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation8 167) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation8 167 by rw [image8_eq]; rfl))

theorem lex_8_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3761) (Sat.Literal.pos 3760) (Sat.Literal.pos 167) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation8 167 (assignment s)
    (Sat.Literal.pos 3761) (Sat.Literal.pos 3760) (Sat.Literal.pos 167) (Sat.Literal.pos 158) (positive_of_descriptor s 3761 (.lex permutation8 167) (by rfl)) (lex_8_167_prefix s) (positive_select s 167) (lex_8_167_image s)

theorem lex_8_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.pos 167), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation8 167 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3760) (Sat.Literal.pos 167) (Sat.Literal.pos 158) (lex_8_167_prefix s) (positive_select s 167) (lex_8_167_image s)

theorem lex_8_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.pos 3760)] :=
  (lex_8_167_gate s).prop _ (List.Mem.head _)

theorem lex_8_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.neg 167), (Sat.Literal.pos 158)] :=
  (lex_8_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.pos 167), (Sat.Literal.neg 158)] :=
  (lex_8_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.neg 167), (Sat.Literal.neg 158), (Sat.Literal.pos 3761)] :=
  (lex_8_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3760), (Sat.Literal.pos 167), (Sat.Literal.pos 158), (Sat.Literal.pos 3761)] :=
  (lex_8_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3761) = lexBefore s permutation8 166 := by
  exact (positive_lex_of_descriptor s 3761 permutation8 167 (by rfl)).trans ((lex_skipped s permutation8 166 167 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation8 166) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation8 166 by rw [image8_eq]; rfl))

theorem lex_8_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3762) (Sat.Literal.pos 3761) (Sat.Literal.pos 166) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation8 166 (assignment s)
    (Sat.Literal.pos 3762) (Sat.Literal.pos 3761) (Sat.Literal.pos 166) (Sat.Literal.pos 154) (positive_of_descriptor s 3762 (.lex permutation8 166) (by rfl)) (lex_8_166_prefix s) (positive_select s 166) (lex_8_166_image s)

theorem lex_8_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.pos 166), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation8 166 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3761) (Sat.Literal.pos 166) (Sat.Literal.pos 154) (lex_8_166_prefix s) (positive_select s 166) (lex_8_166_image s)

theorem lex_8_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.pos 3761)] :=
  (lex_8_166_gate s).prop _ (List.Mem.head _)

theorem lex_8_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.neg 166), (Sat.Literal.pos 154)] :=
  (lex_8_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.pos 166), (Sat.Literal.neg 154)] :=
  (lex_8_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.neg 166), (Sat.Literal.neg 154), (Sat.Literal.pos 3762)] :=
  (lex_8_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3761), (Sat.Literal.pos 166), (Sat.Literal.pos 154), (Sat.Literal.pos 3762)] :=
  (lex_8_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3762) = lexBefore s permutation8 165 := by
  exact (positive_lex_of_descriptor s 3762 permutation8 166 (by rfl)).trans ((lex_skipped s permutation8 165 166 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation8 165) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation8 165 by rw [image8_eq]; rfl))

theorem lex_8_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3763) (Sat.Literal.pos 3762) (Sat.Literal.pos 165) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation8 165 (assignment s)
    (Sat.Literal.pos 3763) (Sat.Literal.pos 3762) (Sat.Literal.pos 165) (Sat.Literal.pos 150) (positive_of_descriptor s 3763 (.lex permutation8 165) (by rfl)) (lex_8_165_prefix s) (positive_select s 165) (lex_8_165_image s)

theorem lex_8_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.pos 165), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation8 165 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3762) (Sat.Literal.pos 165) (Sat.Literal.pos 150) (lex_8_165_prefix s) (positive_select s 165) (lex_8_165_image s)

theorem lex_8_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.pos 3762)] :=
  (lex_8_165_gate s).prop _ (List.Mem.head _)

theorem lex_8_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.neg 165), (Sat.Literal.pos 150)] :=
  (lex_8_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.pos 165), (Sat.Literal.neg 150)] :=
  (lex_8_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.neg 165), (Sat.Literal.neg 150), (Sat.Literal.pos 3763)] :=
  (lex_8_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3762), (Sat.Literal.pos 165), (Sat.Literal.pos 150), (Sat.Literal.pos 3763)] :=
  (lex_8_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3763) = lexBefore s permutation8 164 := by
  exact (positive_lex_of_descriptor s 3763 permutation8 165 (by rfl)).trans ((lex_skipped s permutation8 164 165 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation8 164) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation8 164 by rw [image8_eq]; rfl))

theorem lex_8_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3764) (Sat.Literal.pos 3763) (Sat.Literal.pos 164) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation8 164 (assignment s)
    (Sat.Literal.pos 3764) (Sat.Literal.pos 3763) (Sat.Literal.pos 164) (Sat.Literal.pos 146) (positive_of_descriptor s 3764 (.lex permutation8 164) (by rfl)) (lex_8_164_prefix s) (positive_select s 164) (lex_8_164_image s)

theorem lex_8_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.pos 164), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation8 164 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3763) (Sat.Literal.pos 164) (Sat.Literal.pos 146) (lex_8_164_prefix s) (positive_select s 164) (lex_8_164_image s)

theorem lex_8_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.pos 3763)] :=
  (lex_8_164_gate s).prop _ (List.Mem.head _)

theorem lex_8_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.neg 164), (Sat.Literal.pos 146)] :=
  (lex_8_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.pos 164), (Sat.Literal.neg 146)] :=
  (lex_8_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.neg 164), (Sat.Literal.neg 146), (Sat.Literal.pos 3764)] :=
  (lex_8_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3763), (Sat.Literal.pos 164), (Sat.Literal.pos 146), (Sat.Literal.pos 3764)] :=
  (lex_8_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3764) = lexBefore s permutation8 163 := by
  exact (positive_lex_of_descriptor s 3764 permutation8 164 (by rfl)).trans ((lex_skipped s permutation8 163 164 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation8 163) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation8 163 by rw [image8_eq]; rfl))

theorem lex_8_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3765) (Sat.Literal.pos 3764) (Sat.Literal.pos 163) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation8 163 (assignment s)
    (Sat.Literal.pos 3765) (Sat.Literal.pos 3764) (Sat.Literal.pos 163) (Sat.Literal.pos 142) (positive_of_descriptor s 3765 (.lex permutation8 163) (by rfl)) (lex_8_163_prefix s) (positive_select s 163) (lex_8_163_image s)

theorem lex_8_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.pos 163), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation8 163 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3764) (Sat.Literal.pos 163) (Sat.Literal.pos 142) (lex_8_163_prefix s) (positive_select s 163) (lex_8_163_image s)

theorem lex_8_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.pos 3764)] :=
  (lex_8_163_gate s).prop _ (List.Mem.head _)

theorem lex_8_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.neg 163), (Sat.Literal.pos 142)] :=
  (lex_8_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.pos 163), (Sat.Literal.neg 142)] :=
  (lex_8_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.neg 163), (Sat.Literal.neg 142), (Sat.Literal.pos 3765)] :=
  (lex_8_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3764), (Sat.Literal.pos 163), (Sat.Literal.pos 142), (Sat.Literal.pos 3765)] :=
  (lex_8_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3765) = lexBefore s permutation8 162 := by
  exact (positive_lex_of_descriptor s 3765 permutation8 163 (by rfl)).trans ((lex_skipped s permutation8 162 163 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation8 162) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation8 162 by rw [image8_eq]; rfl))

theorem lex_8_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3766) (Sat.Literal.pos 3765) (Sat.Literal.pos 162) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation8 162 (assignment s)
    (Sat.Literal.pos 3766) (Sat.Literal.pos 3765) (Sat.Literal.pos 162) (Sat.Literal.pos 138) (positive_of_descriptor s 3766 (.lex permutation8 162) (by rfl)) (lex_8_162_prefix s) (positive_select s 162) (lex_8_162_image s)

theorem lex_8_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.pos 162), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation8 162 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3765) (Sat.Literal.pos 162) (Sat.Literal.pos 138) (lex_8_162_prefix s) (positive_select s 162) (lex_8_162_image s)

theorem lex_8_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.pos 3765)] :=
  (lex_8_162_gate s).prop _ (List.Mem.head _)

theorem lex_8_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.neg 162), (Sat.Literal.pos 138)] :=
  (lex_8_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.pos 162), (Sat.Literal.neg 138)] :=
  (lex_8_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.neg 162), (Sat.Literal.neg 138), (Sat.Literal.pos 3766)] :=
  (lex_8_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3765), (Sat.Literal.pos 162), (Sat.Literal.pos 138), (Sat.Literal.pos 3766)] :=
  (lex_8_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3766) = lexBefore s permutation8 161 := by
  exact (positive_lex_of_descriptor s 3766 permutation8 162 (by rfl)).trans ((lex_skipped s permutation8 161 162 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation8 161) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation8 161 by rw [image8_eq]; rfl))

theorem lex_8_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3767) (Sat.Literal.pos 3766) (Sat.Literal.pos 161) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation8 161 (assignment s)
    (Sat.Literal.pos 3767) (Sat.Literal.pos 3766) (Sat.Literal.pos 161) (Sat.Literal.pos 134) (positive_of_descriptor s 3767 (.lex permutation8 161) (by rfl)) (lex_8_161_prefix s) (positive_select s 161) (lex_8_161_image s)

theorem lex_8_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.pos 161), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation8 161 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3766) (Sat.Literal.pos 161) (Sat.Literal.pos 134) (lex_8_161_prefix s) (positive_select s 161) (lex_8_161_image s)

theorem lex_8_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.pos 3766)] :=
  (lex_8_161_gate s).prop _ (List.Mem.head _)

theorem lex_8_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.neg 161), (Sat.Literal.pos 134)] :=
  (lex_8_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.pos 161), (Sat.Literal.neg 134)] :=
  (lex_8_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.neg 161), (Sat.Literal.neg 134), (Sat.Literal.pos 3767)] :=
  (lex_8_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3766), (Sat.Literal.pos 161), (Sat.Literal.pos 134), (Sat.Literal.pos 3767)] :=
  (lex_8_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3767) = lexBefore s permutation8 160 := by
  exact (positive_lex_of_descriptor s 3767 permutation8 161 (by rfl)).trans ((lex_skipped s permutation8 160 161 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation8 160) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation8 160 by rw [image8_eq]; rfl))

theorem lex_8_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3768) (Sat.Literal.pos 3767) (Sat.Literal.pos 160) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation8 160 (assignment s)
    (Sat.Literal.pos 3768) (Sat.Literal.pos 3767) (Sat.Literal.pos 160) (Sat.Literal.pos 130) (positive_of_descriptor s 3768 (.lex permutation8 160) (by rfl)) (lex_8_160_prefix s) (positive_select s 160) (lex_8_160_image s)

theorem lex_8_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.pos 160), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation8 160 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3767) (Sat.Literal.pos 160) (Sat.Literal.pos 130) (lex_8_160_prefix s) (positive_select s 160) (lex_8_160_image s)

theorem lex_8_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.pos 3767)] :=
  (lex_8_160_gate s).prop _ (List.Mem.head _)

theorem lex_8_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.neg 160), (Sat.Literal.pos 130)] :=
  (lex_8_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.pos 160), (Sat.Literal.neg 130)] :=
  (lex_8_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.neg 160), (Sat.Literal.neg 130), (Sat.Literal.pos 3768)] :=
  (lex_8_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3767), (Sat.Literal.pos 160), (Sat.Literal.pos 130), (Sat.Literal.pos 3768)] :=
  (lex_8_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3768) = lexBefore s permutation8 159 := by
  exact (positive_lex_of_descriptor s 3768 permutation8 160 (by rfl)).trans ((lex_skipped s permutation8 159 160 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation8 159) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation8 159 by rw [image8_eq]; rfl))

theorem lex_8_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3769) (Sat.Literal.pos 3768) (Sat.Literal.pos 159) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation8 159 (assignment s)
    (Sat.Literal.pos 3769) (Sat.Literal.pos 3768) (Sat.Literal.pos 159) (Sat.Literal.pos 126) (positive_of_descriptor s 3769 (.lex permutation8 159) (by rfl)) (lex_8_159_prefix s) (positive_select s 159) (lex_8_159_image s)

theorem lex_8_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.pos 159), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation8 159 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3768) (Sat.Literal.pos 159) (Sat.Literal.pos 126) (lex_8_159_prefix s) (positive_select s 159) (lex_8_159_image s)

theorem lex_8_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.pos 3768)] :=
  (lex_8_159_gate s).prop _ (List.Mem.head _)

theorem lex_8_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.neg 159), (Sat.Literal.pos 126)] :=
  (lex_8_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.pos 159), (Sat.Literal.neg 126)] :=
  (lex_8_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.neg 159), (Sat.Literal.neg 126), (Sat.Literal.pos 3769)] :=
  (lex_8_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3768), (Sat.Literal.pos 159), (Sat.Literal.pos 126), (Sat.Literal.pos 3769)] :=
  (lex_8_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3769) = lexBefore s permutation8 158 := by
  exact (positive_lex_of_descriptor s 3769 permutation8 159 (by rfl)).trans ((lex_skipped s permutation8 158 159 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation8 158) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation8 158 by rw [image8_eq]; rfl))

theorem lex_8_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3770) (Sat.Literal.pos 3769) (Sat.Literal.pos 158) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation8 158 (assignment s)
    (Sat.Literal.pos 3770) (Sat.Literal.pos 3769) (Sat.Literal.pos 158) (Sat.Literal.pos 122) (positive_of_descriptor s 3770 (.lex permutation8 158) (by rfl)) (lex_8_158_prefix s) (positive_select s 158) (lex_8_158_image s)

theorem lex_8_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.pos 158), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation8 158 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3769) (Sat.Literal.pos 158) (Sat.Literal.pos 122) (lex_8_158_prefix s) (positive_select s 158) (lex_8_158_image s)

theorem lex_8_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.pos 3769)] :=
  (lex_8_158_gate s).prop _ (List.Mem.head _)

theorem lex_8_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.neg 158), (Sat.Literal.pos 122)] :=
  (lex_8_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.pos 158), (Sat.Literal.neg 122)] :=
  (lex_8_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.neg 158), (Sat.Literal.neg 122), (Sat.Literal.pos 3770)] :=
  (lex_8_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3769), (Sat.Literal.pos 158), (Sat.Literal.pos 122), (Sat.Literal.pos 3770)] :=
  (lex_8_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3770) = lexBefore s permutation8 157 := by
  exact (positive_lex_of_descriptor s 3770 permutation8 158 (by rfl)).trans ((lex_skipped s permutation8 157 158 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation8 157) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation8 157 by rw [image8_eq]; rfl))

theorem lex_8_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3771) (Sat.Literal.pos 3770) (Sat.Literal.pos 157) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation8 157 (assignment s)
    (Sat.Literal.pos 3771) (Sat.Literal.pos 3770) (Sat.Literal.pos 157) (Sat.Literal.pos 118) (positive_of_descriptor s 3771 (.lex permutation8 157) (by rfl)) (lex_8_157_prefix s) (positive_select s 157) (lex_8_157_image s)

theorem lex_8_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.pos 157), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation8 157 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3770) (Sat.Literal.pos 157) (Sat.Literal.pos 118) (lex_8_157_prefix s) (positive_select s 157) (lex_8_157_image s)

theorem lex_8_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.pos 3770)] :=
  (lex_8_157_gate s).prop _ (List.Mem.head _)

theorem lex_8_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.neg 157), (Sat.Literal.pos 118)] :=
  (lex_8_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.pos 157), (Sat.Literal.neg 118)] :=
  (lex_8_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.neg 157), (Sat.Literal.neg 118), (Sat.Literal.pos 3771)] :=
  (lex_8_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3770), (Sat.Literal.pos 157), (Sat.Literal.pos 118), (Sat.Literal.pos 3771)] :=
  (lex_8_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3771) = lexBefore s permutation8 156 := by
  exact (positive_lex_of_descriptor s 3771 permutation8 157 (by rfl)).trans ((lex_skipped s permutation8 156 157 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation8 156) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation8 156 by rw [image8_eq]; rfl))

theorem lex_8_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3772) (Sat.Literal.pos 3771) (Sat.Literal.pos 156) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation8 156 (assignment s)
    (Sat.Literal.pos 3772) (Sat.Literal.pos 3771) (Sat.Literal.pos 156) (Sat.Literal.pos 114) (positive_of_descriptor s 3772 (.lex permutation8 156) (by rfl)) (lex_8_156_prefix s) (positive_select s 156) (lex_8_156_image s)

theorem lex_8_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.pos 156), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation8 156 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3771) (Sat.Literal.pos 156) (Sat.Literal.pos 114) (lex_8_156_prefix s) (positive_select s 156) (lex_8_156_image s)

theorem lex_8_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.pos 3771)] :=
  (lex_8_156_gate s).prop _ (List.Mem.head _)

theorem lex_8_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.neg 156), (Sat.Literal.pos 114)] :=
  (lex_8_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.pos 156), (Sat.Literal.neg 114)] :=
  (lex_8_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.neg 156), (Sat.Literal.neg 114), (Sat.Literal.pos 3772)] :=
  (lex_8_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3771), (Sat.Literal.pos 156), (Sat.Literal.pos 114), (Sat.Literal.pos 3772)] :=
  (lex_8_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3772) = lexBefore s permutation8 155 := by
  exact (positive_lex_of_descriptor s 3772 permutation8 156 (by rfl)).trans ((lex_skipped s permutation8 155 156 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation8 155) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation8 155 by rw [image8_eq]; rfl))

theorem lex_8_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3773) (Sat.Literal.pos 3772) (Sat.Literal.pos 155) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation8 155 (assignment s)
    (Sat.Literal.pos 3773) (Sat.Literal.pos 3772) (Sat.Literal.pos 155) (Sat.Literal.pos 110) (positive_of_descriptor s 3773 (.lex permutation8 155) (by rfl)) (lex_8_155_prefix s) (positive_select s 155) (lex_8_155_image s)

theorem lex_8_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.pos 155), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation8 155 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3772) (Sat.Literal.pos 155) (Sat.Literal.pos 110) (lex_8_155_prefix s) (positive_select s 155) (lex_8_155_image s)

theorem lex_8_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.pos 3772)] :=
  (lex_8_155_gate s).prop _ (List.Mem.head _)

theorem lex_8_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.neg 155), (Sat.Literal.pos 110)] :=
  (lex_8_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.pos 155), (Sat.Literal.neg 110)] :=
  (lex_8_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.neg 155), (Sat.Literal.neg 110), (Sat.Literal.pos 3773)] :=
  (lex_8_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3772), (Sat.Literal.pos 155), (Sat.Literal.pos 110), (Sat.Literal.pos 3773)] :=
  (lex_8_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3773) = lexBefore s permutation8 154 := by
  exact (positive_lex_of_descriptor s 3773 permutation8 155 (by rfl)).trans ((lex_skipped s permutation8 154 155 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation8 154) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation8 154 by rw [image8_eq]; rfl))

theorem lex_8_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3774) (Sat.Literal.pos 3773) (Sat.Literal.pos 154) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation8 154 (assignment s)
    (Sat.Literal.pos 3774) (Sat.Literal.pos 3773) (Sat.Literal.pos 154) (Sat.Literal.pos 106) (positive_of_descriptor s 3774 (.lex permutation8 154) (by rfl)) (lex_8_154_prefix s) (positive_select s 154) (lex_8_154_image s)

theorem lex_8_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.pos 154), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation8 154 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3773) (Sat.Literal.pos 154) (Sat.Literal.pos 106) (lex_8_154_prefix s) (positive_select s 154) (lex_8_154_image s)

theorem lex_8_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.pos 3773)] :=
  (lex_8_154_gate s).prop _ (List.Mem.head _)

theorem lex_8_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.neg 154), (Sat.Literal.pos 106)] :=
  (lex_8_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.pos 154), (Sat.Literal.neg 106)] :=
  (lex_8_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.neg 154), (Sat.Literal.neg 106), (Sat.Literal.pos 3774)] :=
  (lex_8_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3773), (Sat.Literal.pos 154), (Sat.Literal.pos 106), (Sat.Literal.pos 3774)] :=
  (lex_8_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3774) = lexBefore s permutation8 153 := by
  exact (positive_lex_of_descriptor s 3774 permutation8 154 (by rfl)).trans ((lex_skipped s permutation8 153 154 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation8 153) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation8 153 by rw [image8_eq]; rfl))

theorem lex_8_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3775) (Sat.Literal.pos 3774) (Sat.Literal.pos 153) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation8 153 (assignment s)
    (Sat.Literal.pos 3775) (Sat.Literal.pos 3774) (Sat.Literal.pos 153) (Sat.Literal.pos 102) (positive_of_descriptor s 3775 (.lex permutation8 153) (by rfl)) (lex_8_153_prefix s) (positive_select s 153) (lex_8_153_image s)

theorem lex_8_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.pos 153), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation8 153 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3774) (Sat.Literal.pos 153) (Sat.Literal.pos 102) (lex_8_153_prefix s) (positive_select s 153) (lex_8_153_image s)

theorem lex_8_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.pos 3774)] :=
  (lex_8_153_gate s).prop _ (List.Mem.head _)

theorem lex_8_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.neg 153), (Sat.Literal.pos 102)] :=
  (lex_8_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.pos 153), (Sat.Literal.neg 102)] :=
  (lex_8_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.neg 153), (Sat.Literal.neg 102), (Sat.Literal.pos 3775)] :=
  (lex_8_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3774), (Sat.Literal.pos 153), (Sat.Literal.pos 102), (Sat.Literal.pos 3775)] :=
  (lex_8_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3775) = lexBefore s permutation8 152 := by
  exact (positive_lex_of_descriptor s 3775 permutation8 153 (by rfl)).trans ((lex_skipped s permutation8 152 153 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation8 152) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation8 152 by rw [image8_eq]; rfl))

theorem lex_8_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3776) (Sat.Literal.pos 3775) (Sat.Literal.pos 152) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation8 152 (assignment s)
    (Sat.Literal.pos 3776) (Sat.Literal.pos 3775) (Sat.Literal.pos 152) (Sat.Literal.pos 98) (positive_of_descriptor s 3776 (.lex permutation8 152) (by rfl)) (lex_8_152_prefix s) (positive_select s 152) (lex_8_152_image s)

theorem lex_8_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.pos 152), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation8 152 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3775) (Sat.Literal.pos 152) (Sat.Literal.pos 98) (lex_8_152_prefix s) (positive_select s 152) (lex_8_152_image s)

theorem lex_8_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.pos 3775)] :=
  (lex_8_152_gate s).prop _ (List.Mem.head _)

theorem lex_8_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.neg 152), (Sat.Literal.pos 98)] :=
  (lex_8_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.pos 152), (Sat.Literal.neg 98)] :=
  (lex_8_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.neg 152), (Sat.Literal.neg 98), (Sat.Literal.pos 3776)] :=
  (lex_8_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3775), (Sat.Literal.pos 152), (Sat.Literal.pos 98), (Sat.Literal.pos 3776)] :=
  (lex_8_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3776) = lexBefore s permutation8 151 := by
  exact (positive_lex_of_descriptor s 3776 permutation8 152 (by rfl)).trans ((lex_skipped s permutation8 151 152 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation8 151) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation8 151 by rw [image8_eq]; rfl))

theorem lex_8_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3777) (Sat.Literal.pos 3776) (Sat.Literal.pos 151) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation8 151 (assignment s)
    (Sat.Literal.pos 3777) (Sat.Literal.pos 3776) (Sat.Literal.pos 151) (Sat.Literal.pos 94) (positive_of_descriptor s 3777 (.lex permutation8 151) (by rfl)) (lex_8_151_prefix s) (positive_select s 151) (lex_8_151_image s)

theorem lex_8_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.pos 151), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation8 151 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3776) (Sat.Literal.pos 151) (Sat.Literal.pos 94) (lex_8_151_prefix s) (positive_select s 151) (lex_8_151_image s)

theorem lex_8_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.pos 3776)] :=
  (lex_8_151_gate s).prop _ (List.Mem.head _)

theorem lex_8_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.neg 151), (Sat.Literal.pos 94)] :=
  (lex_8_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.pos 151), (Sat.Literal.neg 94)] :=
  (lex_8_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.neg 151), (Sat.Literal.neg 94), (Sat.Literal.pos 3777)] :=
  (lex_8_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3776), (Sat.Literal.pos 151), (Sat.Literal.pos 94), (Sat.Literal.pos 3777)] :=
  (lex_8_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3777) = lexBefore s permutation8 150 := by
  exact (positive_lex_of_descriptor s 3777 permutation8 151 (by rfl)).trans ((lex_skipped s permutation8 150 151 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation8 150) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation8 150 by rw [image8_eq]; rfl))

theorem lex_8_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3778) (Sat.Literal.pos 3777) (Sat.Literal.pos 150) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation8 150 (assignment s)
    (Sat.Literal.pos 3778) (Sat.Literal.pos 3777) (Sat.Literal.pos 150) (Sat.Literal.pos 90) (positive_of_descriptor s 3778 (.lex permutation8 150) (by rfl)) (lex_8_150_prefix s) (positive_select s 150) (lex_8_150_image s)

theorem lex_8_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.pos 150), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation8 150 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3777) (Sat.Literal.pos 150) (Sat.Literal.pos 90) (lex_8_150_prefix s) (positive_select s 150) (lex_8_150_image s)

theorem lex_8_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.pos 3777)] :=
  (lex_8_150_gate s).prop _ (List.Mem.head _)

theorem lex_8_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.neg 150), (Sat.Literal.pos 90)] :=
  (lex_8_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.pos 150), (Sat.Literal.neg 90)] :=
  (lex_8_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.neg 150), (Sat.Literal.neg 90), (Sat.Literal.pos 3778)] :=
  (lex_8_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3777), (Sat.Literal.pos 150), (Sat.Literal.pos 90), (Sat.Literal.pos 3778)] :=
  (lex_8_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3778) = lexBefore s permutation8 149 := by
  exact (positive_lex_of_descriptor s 3778 permutation8 150 (by rfl)).trans ((lex_skipped s permutation8 149 150 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation8 149) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation8 149 by rw [image8_eq]; rfl))

theorem lex_8_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3779) (Sat.Literal.pos 3778) (Sat.Literal.pos 149) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation8 149 (assignment s)
    (Sat.Literal.pos 3779) (Sat.Literal.pos 3778) (Sat.Literal.pos 149) (Sat.Literal.pos 86) (positive_of_descriptor s 3779 (.lex permutation8 149) (by rfl)) (lex_8_149_prefix s) (positive_select s 149) (lex_8_149_image s)

theorem lex_8_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.pos 149), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation8 149 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3778) (Sat.Literal.pos 149) (Sat.Literal.pos 86) (lex_8_149_prefix s) (positive_select s 149) (lex_8_149_image s)

theorem lex_8_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.pos 3778)] :=
  (lex_8_149_gate s).prop _ (List.Mem.head _)

theorem lex_8_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.neg 149), (Sat.Literal.pos 86)] :=
  (lex_8_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.pos 149), (Sat.Literal.neg 86)] :=
  (lex_8_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.neg 149), (Sat.Literal.neg 86), (Sat.Literal.pos 3779)] :=
  (lex_8_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3778), (Sat.Literal.pos 149), (Sat.Literal.pos 86), (Sat.Literal.pos 3779)] :=
  (lex_8_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3779) = lexBefore s permutation8 148 := by
  exact (positive_lex_of_descriptor s 3779 permutation8 149 (by rfl)).trans ((lex_skipped s permutation8 148 149 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation8 148) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation8 148 by rw [image8_eq]; rfl))

theorem lex_8_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3780) (Sat.Literal.pos 3779) (Sat.Literal.pos 148) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation8 148 (assignment s)
    (Sat.Literal.pos 3780) (Sat.Literal.pos 3779) (Sat.Literal.pos 148) (Sat.Literal.pos 82) (positive_of_descriptor s 3780 (.lex permutation8 148) (by rfl)) (lex_8_148_prefix s) (positive_select s 148) (lex_8_148_image s)

theorem lex_8_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.pos 148), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation8 148 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3779) (Sat.Literal.pos 148) (Sat.Literal.pos 82) (lex_8_148_prefix s) (positive_select s 148) (lex_8_148_image s)

theorem lex_8_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.pos 3779)] :=
  (lex_8_148_gate s).prop _ (List.Mem.head _)

theorem lex_8_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.neg 148), (Sat.Literal.pos 82)] :=
  (lex_8_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.pos 148), (Sat.Literal.neg 82)] :=
  (lex_8_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.neg 148), (Sat.Literal.neg 82), (Sat.Literal.pos 3780)] :=
  (lex_8_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3779), (Sat.Literal.pos 148), (Sat.Literal.pos 82), (Sat.Literal.pos 3780)] :=
  (lex_8_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3780) = lexBefore s permutation8 147 := by
  exact (positive_lex_of_descriptor s 3780 permutation8 148 (by rfl)).trans ((lex_skipped s permutation8 147 148 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation8 147) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation8 147 by rw [image8_eq]; rfl))

theorem lex_8_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3781) (Sat.Literal.pos 3780) (Sat.Literal.pos 147) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation8 147 (assignment s)
    (Sat.Literal.pos 3781) (Sat.Literal.pos 3780) (Sat.Literal.pos 147) (Sat.Literal.pos 78) (positive_of_descriptor s 3781 (.lex permutation8 147) (by rfl)) (lex_8_147_prefix s) (positive_select s 147) (lex_8_147_image s)

theorem lex_8_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.pos 147), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation8 147 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3780) (Sat.Literal.pos 147) (Sat.Literal.pos 78) (lex_8_147_prefix s) (positive_select s 147) (lex_8_147_image s)

theorem lex_8_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.pos 3780)] :=
  (lex_8_147_gate s).prop _ (List.Mem.head _)

theorem lex_8_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.neg 147), (Sat.Literal.pos 78)] :=
  (lex_8_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.pos 147), (Sat.Literal.neg 78)] :=
  (lex_8_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.neg 147), (Sat.Literal.neg 78), (Sat.Literal.pos 3781)] :=
  (lex_8_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3780), (Sat.Literal.pos 147), (Sat.Literal.pos 78), (Sat.Literal.pos 3781)] :=
  (lex_8_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3781) = lexBefore s permutation8 146 := by
  exact (positive_lex_of_descriptor s 3781 permutation8 147 (by rfl)).trans ((lex_skipped s permutation8 146 147 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation8 146) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation8 146 by rw [image8_eq]; rfl))

theorem lex_8_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3782) (Sat.Literal.pos 3781) (Sat.Literal.pos 146) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation8 146 (assignment s)
    (Sat.Literal.pos 3782) (Sat.Literal.pos 3781) (Sat.Literal.pos 146) (Sat.Literal.pos 74) (positive_of_descriptor s 3782 (.lex permutation8 146) (by rfl)) (lex_8_146_prefix s) (positive_select s 146) (lex_8_146_image s)

theorem lex_8_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.pos 146), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation8 146 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3781) (Sat.Literal.pos 146) (Sat.Literal.pos 74) (lex_8_146_prefix s) (positive_select s 146) (lex_8_146_image s)

theorem lex_8_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.pos 3781)] :=
  (lex_8_146_gate s).prop _ (List.Mem.head _)

theorem lex_8_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.neg 146), (Sat.Literal.pos 74)] :=
  (lex_8_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.pos 146), (Sat.Literal.neg 74)] :=
  (lex_8_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.neg 146), (Sat.Literal.neg 74), (Sat.Literal.pos 3782)] :=
  (lex_8_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3781), (Sat.Literal.pos 146), (Sat.Literal.pos 74), (Sat.Literal.pos 3782)] :=
  (lex_8_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3782) = lexBefore s permutation8 145 := by
  exact (positive_lex_of_descriptor s 3782 permutation8 146 (by rfl)).trans ((lex_skipped s permutation8 145 146 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation8 145) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation8 145 by rw [image8_eq]; rfl))

theorem lex_8_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3783) (Sat.Literal.pos 3782) (Sat.Literal.pos 145) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation8 145 (assignment s)
    (Sat.Literal.pos 3783) (Sat.Literal.pos 3782) (Sat.Literal.pos 145) (Sat.Literal.pos 70) (positive_of_descriptor s 3783 (.lex permutation8 145) (by rfl)) (lex_8_145_prefix s) (positive_select s 145) (lex_8_145_image s)

theorem lex_8_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.pos 145), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation8 145 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3782) (Sat.Literal.pos 145) (Sat.Literal.pos 70) (lex_8_145_prefix s) (positive_select s 145) (lex_8_145_image s)

theorem lex_8_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.pos 3782)] :=
  (lex_8_145_gate s).prop _ (List.Mem.head _)

theorem lex_8_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.neg 145), (Sat.Literal.pos 70)] :=
  (lex_8_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.pos 145), (Sat.Literal.neg 70)] :=
  (lex_8_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.neg 145), (Sat.Literal.neg 70), (Sat.Literal.pos 3783)] :=
  (lex_8_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3782), (Sat.Literal.pos 145), (Sat.Literal.pos 70), (Sat.Literal.pos 3783)] :=
  (lex_8_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3783) = lexBefore s permutation8 144 := by
  exact (positive_lex_of_descriptor s 3783 permutation8 145 (by rfl)).trans ((lex_skipped s permutation8 144 145 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation8 144) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation8 144 by rw [image8_eq]; rfl))

theorem lex_8_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3784) (Sat.Literal.pos 3783) (Sat.Literal.pos 144) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation8 144 (assignment s)
    (Sat.Literal.pos 3784) (Sat.Literal.pos 3783) (Sat.Literal.pos 144) (Sat.Literal.pos 66) (positive_of_descriptor s 3784 (.lex permutation8 144) (by rfl)) (lex_8_144_prefix s) (positive_select s 144) (lex_8_144_image s)

theorem lex_8_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.pos 144), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation8 144 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3783) (Sat.Literal.pos 144) (Sat.Literal.pos 66) (lex_8_144_prefix s) (positive_select s 144) (lex_8_144_image s)

theorem lex_8_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.pos 3783)] :=
  (lex_8_144_gate s).prop _ (List.Mem.head _)

theorem lex_8_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.neg 144), (Sat.Literal.pos 66)] :=
  (lex_8_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.pos 144), (Sat.Literal.neg 66)] :=
  (lex_8_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.neg 144), (Sat.Literal.neg 66), (Sat.Literal.pos 3784)] :=
  (lex_8_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3783), (Sat.Literal.pos 144), (Sat.Literal.pos 66), (Sat.Literal.pos 3784)] :=
  (lex_8_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3784) = lexBefore s permutation8 143 := by
  exact (positive_lex_of_descriptor s 3784 permutation8 144 (by rfl)).trans ((lex_skipped s permutation8 143 144 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation8 143) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation8 143 by rw [image8_eq]; rfl))

theorem lex_8_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3785) (Sat.Literal.pos 3784) (Sat.Literal.pos 143) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation8 143 (assignment s)
    (Sat.Literal.pos 3785) (Sat.Literal.pos 3784) (Sat.Literal.pos 143) (Sat.Literal.pos 62) (positive_of_descriptor s 3785 (.lex permutation8 143) (by rfl)) (lex_8_143_prefix s) (positive_select s 143) (lex_8_143_image s)

theorem lex_8_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.pos 143), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation8 143 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3784) (Sat.Literal.pos 143) (Sat.Literal.pos 62) (lex_8_143_prefix s) (positive_select s 143) (lex_8_143_image s)

theorem lex_8_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.pos 3784)] :=
  (lex_8_143_gate s).prop _ (List.Mem.head _)

theorem lex_8_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.neg 143), (Sat.Literal.pos 62)] :=
  (lex_8_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.pos 143), (Sat.Literal.neg 62)] :=
  (lex_8_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.neg 143), (Sat.Literal.neg 62), (Sat.Literal.pos 3785)] :=
  (lex_8_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3784), (Sat.Literal.pos 143), (Sat.Literal.pos 62), (Sat.Literal.pos 3785)] :=
  (lex_8_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3785) = lexBefore s permutation8 142 := by
  exact (positive_lex_of_descriptor s 3785 permutation8 143 (by rfl)).trans ((lex_skipped s permutation8 142 143 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation8 142) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation8 142 by rw [image8_eq]; rfl))

theorem lex_8_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3786) (Sat.Literal.pos 3785) (Sat.Literal.pos 142) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation8 142 (assignment s)
    (Sat.Literal.pos 3786) (Sat.Literal.pos 3785) (Sat.Literal.pos 142) (Sat.Literal.pos 58) (positive_of_descriptor s 3786 (.lex permutation8 142) (by rfl)) (lex_8_142_prefix s) (positive_select s 142) (lex_8_142_image s)

theorem lex_8_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.pos 142), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation8 142 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3785) (Sat.Literal.pos 142) (Sat.Literal.pos 58) (lex_8_142_prefix s) (positive_select s 142) (lex_8_142_image s)

theorem lex_8_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.pos 3785)] :=
  (lex_8_142_gate s).prop _ (List.Mem.head _)

theorem lex_8_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.neg 142), (Sat.Literal.pos 58)] :=
  (lex_8_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.pos 142), (Sat.Literal.neg 58)] :=
  (lex_8_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.neg 142), (Sat.Literal.neg 58), (Sat.Literal.pos 3786)] :=
  (lex_8_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3785), (Sat.Literal.pos 142), (Sat.Literal.pos 58), (Sat.Literal.pos 3786)] :=
  (lex_8_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3786) = lexBefore s permutation8 141 := by
  exact (positive_lex_of_descriptor s 3786 permutation8 142 (by rfl)).trans ((lex_skipped s permutation8 141 142 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation8 141) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation8 141 by rw [image8_eq]; rfl))

theorem lex_8_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3787) (Sat.Literal.pos 3786) (Sat.Literal.pos 141) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation8 141 (assignment s)
    (Sat.Literal.pos 3787) (Sat.Literal.pos 3786) (Sat.Literal.pos 141) (Sat.Literal.pos 54) (positive_of_descriptor s 3787 (.lex permutation8 141) (by rfl)) (lex_8_141_prefix s) (positive_select s 141) (lex_8_141_image s)

theorem lex_8_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.pos 141), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation8 141 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3786) (Sat.Literal.pos 141) (Sat.Literal.pos 54) (lex_8_141_prefix s) (positive_select s 141) (lex_8_141_image s)

theorem lex_8_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.pos 3786)] :=
  (lex_8_141_gate s).prop _ (List.Mem.head _)

theorem lex_8_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.neg 141), (Sat.Literal.pos 54)] :=
  (lex_8_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.pos 141), (Sat.Literal.neg 54)] :=
  (lex_8_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.neg 141), (Sat.Literal.neg 54), (Sat.Literal.pos 3787)] :=
  (lex_8_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3786), (Sat.Literal.pos 141), (Sat.Literal.pos 54), (Sat.Literal.pos 3787)] :=
  (lex_8_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3787) = lexBefore s permutation8 140 := by
  exact (positive_lex_of_descriptor s 3787 permutation8 141 (by rfl)).trans ((lex_skipped s permutation8 140 141 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation8 140) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation8 140 by rw [image8_eq]; rfl))

theorem lex_8_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3788) (Sat.Literal.pos 3787) (Sat.Literal.pos 140) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation8 140 (assignment s)
    (Sat.Literal.pos 3788) (Sat.Literal.pos 3787) (Sat.Literal.pos 140) (Sat.Literal.pos 50) (positive_of_descriptor s 3788 (.lex permutation8 140) (by rfl)) (lex_8_140_prefix s) (positive_select s 140) (lex_8_140_image s)

theorem lex_8_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.pos 140), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation8 140 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3787) (Sat.Literal.pos 140) (Sat.Literal.pos 50) (lex_8_140_prefix s) (positive_select s 140) (lex_8_140_image s)

theorem lex_8_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.pos 3787)] :=
  (lex_8_140_gate s).prop _ (List.Mem.head _)

theorem lex_8_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.neg 140), (Sat.Literal.pos 50)] :=
  (lex_8_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.pos 140), (Sat.Literal.neg 50)] :=
  (lex_8_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.neg 140), (Sat.Literal.neg 50), (Sat.Literal.pos 3788)] :=
  (lex_8_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3787), (Sat.Literal.pos 140), (Sat.Literal.pos 50), (Sat.Literal.pos 3788)] :=
  (lex_8_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3788) = lexBefore s permutation8 139 := by
  exact (positive_lex_of_descriptor s 3788 permutation8 140 (by rfl)).trans ((lex_skipped s permutation8 139 140 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation8 139) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation8 139 by rw [image8_eq]; rfl))

theorem lex_8_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3789) (Sat.Literal.pos 3788) (Sat.Literal.pos 139) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation8 139 (assignment s)
    (Sat.Literal.pos 3789) (Sat.Literal.pos 3788) (Sat.Literal.pos 139) (Sat.Literal.pos 46) (positive_of_descriptor s 3789 (.lex permutation8 139) (by rfl)) (lex_8_139_prefix s) (positive_select s 139) (lex_8_139_image s)

theorem lex_8_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.pos 139), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation8 139 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3788) (Sat.Literal.pos 139) (Sat.Literal.pos 46) (lex_8_139_prefix s) (positive_select s 139) (lex_8_139_image s)

theorem lex_8_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.pos 3788)] :=
  (lex_8_139_gate s).prop _ (List.Mem.head _)

theorem lex_8_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.neg 139), (Sat.Literal.pos 46)] :=
  (lex_8_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.pos 139), (Sat.Literal.neg 46)] :=
  (lex_8_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.neg 139), (Sat.Literal.neg 46), (Sat.Literal.pos 3789)] :=
  (lex_8_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3788), (Sat.Literal.pos 139), (Sat.Literal.pos 46), (Sat.Literal.pos 3789)] :=
  (lex_8_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3789) = lexBefore s permutation8 138 := by
  exact (positive_lex_of_descriptor s 3789 permutation8 139 (by rfl)).trans ((lex_skipped s permutation8 138 139 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation8 138) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation8 138 by rw [image8_eq]; rfl))

theorem lex_8_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3790) (Sat.Literal.pos 3789) (Sat.Literal.pos 138) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation8 138 (assignment s)
    (Sat.Literal.pos 3790) (Sat.Literal.pos 3789) (Sat.Literal.pos 138) (Sat.Literal.pos 42) (positive_of_descriptor s 3790 (.lex permutation8 138) (by rfl)) (lex_8_138_prefix s) (positive_select s 138) (lex_8_138_image s)

theorem lex_8_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.pos 138), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation8 138 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3789) (Sat.Literal.pos 138) (Sat.Literal.pos 42) (lex_8_138_prefix s) (positive_select s 138) (lex_8_138_image s)

theorem lex_8_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.pos 3789)] :=
  (lex_8_138_gate s).prop _ (List.Mem.head _)

theorem lex_8_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.neg 138), (Sat.Literal.pos 42)] :=
  (lex_8_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.pos 138), (Sat.Literal.neg 42)] :=
  (lex_8_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.neg 138), (Sat.Literal.neg 42), (Sat.Literal.pos 3790)] :=
  (lex_8_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3789), (Sat.Literal.pos 138), (Sat.Literal.pos 42), (Sat.Literal.pos 3790)] :=
  (lex_8_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3790) = lexBefore s permutation8 137 := by
  exact (positive_lex_of_descriptor s 3790 permutation8 138 (by rfl)).trans ((lex_skipped s permutation8 137 138 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation8 137) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation8 137 by rw [image8_eq]; rfl))

theorem lex_8_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3791) (Sat.Literal.pos 3790) (Sat.Literal.pos 137) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation8 137 (assignment s)
    (Sat.Literal.pos 3791) (Sat.Literal.pos 3790) (Sat.Literal.pos 137) (Sat.Literal.pos 38) (positive_of_descriptor s 3791 (.lex permutation8 137) (by rfl)) (lex_8_137_prefix s) (positive_select s 137) (lex_8_137_image s)

theorem lex_8_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.pos 137), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation8 137 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3790) (Sat.Literal.pos 137) (Sat.Literal.pos 38) (lex_8_137_prefix s) (positive_select s 137) (lex_8_137_image s)

theorem lex_8_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.pos 3790)] :=
  (lex_8_137_gate s).prop _ (List.Mem.head _)

theorem lex_8_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.neg 137), (Sat.Literal.pos 38)] :=
  (lex_8_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.pos 137), (Sat.Literal.neg 38)] :=
  (lex_8_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.neg 137), (Sat.Literal.neg 38), (Sat.Literal.pos 3791)] :=
  (lex_8_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3790), (Sat.Literal.pos 137), (Sat.Literal.pos 38), (Sat.Literal.pos 3791)] :=
  (lex_8_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3791) = lexBefore s permutation8 136 := by
  exact (positive_lex_of_descriptor s 3791 permutation8 137 (by rfl)).trans ((lex_skipped s permutation8 136 137 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation8 136) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation8 136 by rw [image8_eq]; rfl))

theorem lex_8_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3792) (Sat.Literal.pos 3791) (Sat.Literal.pos 136) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation8 136 (assignment s)
    (Sat.Literal.pos 3792) (Sat.Literal.pos 3791) (Sat.Literal.pos 136) (Sat.Literal.pos 34) (positive_of_descriptor s 3792 (.lex permutation8 136) (by rfl)) (lex_8_136_prefix s) (positive_select s 136) (lex_8_136_image s)

theorem lex_8_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.pos 136), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation8 136 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3791) (Sat.Literal.pos 136) (Sat.Literal.pos 34) (lex_8_136_prefix s) (positive_select s 136) (lex_8_136_image s)

theorem lex_8_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.pos 3791)] :=
  (lex_8_136_gate s).prop _ (List.Mem.head _)

theorem lex_8_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.neg 136), (Sat.Literal.pos 34)] :=
  (lex_8_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.pos 136), (Sat.Literal.neg 34)] :=
  (lex_8_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.neg 136), (Sat.Literal.neg 34), (Sat.Literal.pos 3792)] :=
  (lex_8_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3791), (Sat.Literal.pos 136), (Sat.Literal.pos 34), (Sat.Literal.pos 3792)] :=
  (lex_8_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3792) = lexBefore s permutation8 135 := by
  exact (positive_lex_of_descriptor s 3792 permutation8 136 (by rfl)).trans ((lex_skipped s permutation8 135 136 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation8 135) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation8 135 by rw [image8_eq]; rfl))

theorem lex_8_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3793) (Sat.Literal.pos 3792) (Sat.Literal.pos 135) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation8 135 (assignment s)
    (Sat.Literal.pos 3793) (Sat.Literal.pos 3792) (Sat.Literal.pos 135) (Sat.Literal.pos 30) (positive_of_descriptor s 3793 (.lex permutation8 135) (by rfl)) (lex_8_135_prefix s) (positive_select s 135) (lex_8_135_image s)

theorem lex_8_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.pos 135), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation8 135 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3792) (Sat.Literal.pos 135) (Sat.Literal.pos 30) (lex_8_135_prefix s) (positive_select s 135) (lex_8_135_image s)

theorem lex_8_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.pos 3792)] :=
  (lex_8_135_gate s).prop _ (List.Mem.head _)

theorem lex_8_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.neg 135), (Sat.Literal.pos 30)] :=
  (lex_8_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.pos 135), (Sat.Literal.neg 30)] :=
  (lex_8_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.neg 135), (Sat.Literal.neg 30), (Sat.Literal.pos 3793)] :=
  (lex_8_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3792), (Sat.Literal.pos 135), (Sat.Literal.pos 30), (Sat.Literal.pos 3793)] :=
  (lex_8_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3793) = lexBefore s permutation8 134 := by
  exact (positive_lex_of_descriptor s 3793 permutation8 135 (by rfl)).trans ((lex_skipped s permutation8 134 135 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation8 134) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation8 134 by rw [image8_eq]; rfl))

theorem lex_8_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3794) (Sat.Literal.pos 3793) (Sat.Literal.pos 134) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation8 134 (assignment s)
    (Sat.Literal.pos 3794) (Sat.Literal.pos 3793) (Sat.Literal.pos 134) (Sat.Literal.pos 26) (positive_of_descriptor s 3794 (.lex permutation8 134) (by rfl)) (lex_8_134_prefix s) (positive_select s 134) (lex_8_134_image s)

theorem lex_8_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.pos 134), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation8 134 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3793) (Sat.Literal.pos 134) (Sat.Literal.pos 26) (lex_8_134_prefix s) (positive_select s 134) (lex_8_134_image s)

theorem lex_8_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.pos 3793)] :=
  (lex_8_134_gate s).prop _ (List.Mem.head _)

theorem lex_8_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.neg 134), (Sat.Literal.pos 26)] :=
  (lex_8_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.pos 134), (Sat.Literal.neg 26)] :=
  (lex_8_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.neg 134), (Sat.Literal.neg 26), (Sat.Literal.pos 3794)] :=
  (lex_8_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3793), (Sat.Literal.pos 134), (Sat.Literal.pos 26), (Sat.Literal.pos 3794)] :=
  (lex_8_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3794) = lexBefore s permutation8 133 := by
  exact (positive_lex_of_descriptor s 3794 permutation8 134 (by rfl)).trans ((lex_skipped s permutation8 133 134 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation8 133) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation8 133 by rw [image8_eq]; rfl))

theorem lex_8_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3795) (Sat.Literal.pos 3794) (Sat.Literal.pos 133) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation8 133 (assignment s)
    (Sat.Literal.pos 3795) (Sat.Literal.pos 3794) (Sat.Literal.pos 133) (Sat.Literal.pos 22) (positive_of_descriptor s 3795 (.lex permutation8 133) (by rfl)) (lex_8_133_prefix s) (positive_select s 133) (lex_8_133_image s)

theorem lex_8_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.pos 133), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation8 133 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3794) (Sat.Literal.pos 133) (Sat.Literal.pos 22) (lex_8_133_prefix s) (positive_select s 133) (lex_8_133_image s)

theorem lex_8_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.pos 3794)] :=
  (lex_8_133_gate s).prop _ (List.Mem.head _)

theorem lex_8_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.neg 133), (Sat.Literal.pos 22)] :=
  (lex_8_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.pos 133), (Sat.Literal.neg 22)] :=
  (lex_8_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.neg 133), (Sat.Literal.neg 22), (Sat.Literal.pos 3795)] :=
  (lex_8_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3794), (Sat.Literal.pos 133), (Sat.Literal.pos 22), (Sat.Literal.pos 3795)] :=
  (lex_8_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3795) = lexBefore s permutation8 132 := by
  exact (positive_lex_of_descriptor s 3795 permutation8 133 (by rfl)).trans ((lex_skipped s permutation8 132 133 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation8 132) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation8 132 by rw [image8_eq]; rfl))

theorem lex_8_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3796) (Sat.Literal.pos 3795) (Sat.Literal.pos 132) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation8 132 (assignment s)
    (Sat.Literal.pos 3796) (Sat.Literal.pos 3795) (Sat.Literal.pos 132) (Sat.Literal.pos 18) (positive_of_descriptor s 3796 (.lex permutation8 132) (by rfl)) (lex_8_132_prefix s) (positive_select s 132) (lex_8_132_image s)

theorem lex_8_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.pos 132), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation8 132 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3795) (Sat.Literal.pos 132) (Sat.Literal.pos 18) (lex_8_132_prefix s) (positive_select s 132) (lex_8_132_image s)

theorem lex_8_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.pos 3795)] :=
  (lex_8_132_gate s).prop _ (List.Mem.head _)

theorem lex_8_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.neg 132), (Sat.Literal.pos 18)] :=
  (lex_8_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.pos 132), (Sat.Literal.neg 18)] :=
  (lex_8_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.neg 132), (Sat.Literal.neg 18), (Sat.Literal.pos 3796)] :=
  (lex_8_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3795), (Sat.Literal.pos 132), (Sat.Literal.pos 18), (Sat.Literal.pos 3796)] :=
  (lex_8_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3796) = lexBefore s permutation8 131 := by
  exact (positive_lex_of_descriptor s 3796 permutation8 132 (by rfl)).trans ((lex_skipped s permutation8 131 132 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation8 131) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation8 131 by rw [image8_eq]; rfl))

theorem lex_8_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3797) (Sat.Literal.pos 3796) (Sat.Literal.pos 131) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation8 131 (assignment s)
    (Sat.Literal.pos 3797) (Sat.Literal.pos 3796) (Sat.Literal.pos 131) (Sat.Literal.pos 14) (positive_of_descriptor s 3797 (.lex permutation8 131) (by rfl)) (lex_8_131_prefix s) (positive_select s 131) (lex_8_131_image s)

theorem lex_8_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.pos 131), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation8 131 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3796) (Sat.Literal.pos 131) (Sat.Literal.pos 14) (lex_8_131_prefix s) (positive_select s 131) (lex_8_131_image s)

theorem lex_8_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.pos 3796)] :=
  (lex_8_131_gate s).prop _ (List.Mem.head _)

theorem lex_8_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.neg 131), (Sat.Literal.pos 14)] :=
  (lex_8_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.pos 131), (Sat.Literal.neg 14)] :=
  (lex_8_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.neg 131), (Sat.Literal.neg 14), (Sat.Literal.pos 3797)] :=
  (lex_8_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3796), (Sat.Literal.pos 131), (Sat.Literal.pos 14), (Sat.Literal.pos 3797)] :=
  (lex_8_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3797) = lexBefore s permutation8 130 := by
  exact (positive_lex_of_descriptor s 3797 permutation8 131 (by rfl)).trans ((lex_skipped s permutation8 130 131 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation8 130) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation8 130 by rw [image8_eq]; rfl))

theorem lex_8_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3798) (Sat.Literal.pos 3797) (Sat.Literal.pos 130) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation8 130 (assignment s)
    (Sat.Literal.pos 3798) (Sat.Literal.pos 3797) (Sat.Literal.pos 130) (Sat.Literal.pos 10) (positive_of_descriptor s 3798 (.lex permutation8 130) (by rfl)) (lex_8_130_prefix s) (positive_select s 130) (lex_8_130_image s)

theorem lex_8_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.pos 130), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation8 130 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3797) (Sat.Literal.pos 130) (Sat.Literal.pos 10) (lex_8_130_prefix s) (positive_select s 130) (lex_8_130_image s)

theorem lex_8_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.pos 3797)] :=
  (lex_8_130_gate s).prop _ (List.Mem.head _)

theorem lex_8_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.neg 130), (Sat.Literal.pos 10)] :=
  (lex_8_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.pos 130), (Sat.Literal.neg 10)] :=
  (lex_8_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.neg 130), (Sat.Literal.neg 10), (Sat.Literal.pos 3798)] :=
  (lex_8_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3797), (Sat.Literal.pos 130), (Sat.Literal.pos 10), (Sat.Literal.pos 3798)] :=
  (lex_8_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3798) = lexBefore s permutation8 129 := by
  exact (positive_lex_of_descriptor s 3798 permutation8 130 (by rfl)).trans ((lex_skipped s permutation8 129 130 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation8 129) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation8 129 by rw [image8_eq]; rfl))

theorem lex_8_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3799) (Sat.Literal.pos 3798) (Sat.Literal.pos 129) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation8 129 (assignment s)
    (Sat.Literal.pos 3799) (Sat.Literal.pos 3798) (Sat.Literal.pos 129) (Sat.Literal.pos 6) (positive_of_descriptor s 3799 (.lex permutation8 129) (by rfl)) (lex_8_129_prefix s) (positive_select s 129) (lex_8_129_image s)

theorem lex_8_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.pos 129), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation8 129 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3798) (Sat.Literal.pos 129) (Sat.Literal.pos 6) (lex_8_129_prefix s) (positive_select s 129) (lex_8_129_image s)

theorem lex_8_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.pos 3798)] :=
  (lex_8_129_gate s).prop _ (List.Mem.head _)

theorem lex_8_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.neg 129), (Sat.Literal.pos 6)] :=
  (lex_8_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.pos 129), (Sat.Literal.neg 6)] :=
  (lex_8_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.neg 129), (Sat.Literal.neg 6), (Sat.Literal.pos 3799)] :=
  (lex_8_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3798), (Sat.Literal.pos 129), (Sat.Literal.pos 6), (Sat.Literal.pos 3799)] :=
  (lex_8_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3799) = lexBefore s permutation8 128 := by
  exact (positive_lex_of_descriptor s 3799 permutation8 129 (by rfl)).trans ((lex_skipped s permutation8 128 129 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation8 128) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation8 128 by rw [image8_eq]; rfl))

theorem lex_8_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3800) (Sat.Literal.pos 3799) (Sat.Literal.pos 128) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation8 128 (assignment s)
    (Sat.Literal.pos 3800) (Sat.Literal.pos 3799) (Sat.Literal.pos 128) (Sat.Literal.pos 2) (positive_of_descriptor s 3800 (.lex permutation8 128) (by rfl)) (lex_8_128_prefix s) (positive_select s 128) (lex_8_128_image s)

theorem lex_8_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.pos 128), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation8 128 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3799) (Sat.Literal.pos 128) (Sat.Literal.pos 2) (lex_8_128_prefix s) (positive_select s 128) (lex_8_128_image s)

theorem lex_8_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.pos 3799)] :=
  (lex_8_128_gate s).prop _ (List.Mem.head _)

theorem lex_8_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.neg 128), (Sat.Literal.pos 2)] :=
  (lex_8_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.pos 128), (Sat.Literal.neg 2)] :=
  (lex_8_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.neg 128), (Sat.Literal.neg 2), (Sat.Literal.pos 3800)] :=
  (lex_8_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3799), (Sat.Literal.pos 128), (Sat.Literal.pos 2), (Sat.Literal.pos 3800)] :=
  (lex_8_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3800) = lexBefore s permutation8 127 := by
  exact (positive_lex_of_descriptor s 3800 permutation8 128 (by rfl)).trans ((lex_skipped s permutation8 127 128 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation8 127) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation8 127 by rw [image8_eq]; rfl))

theorem lex_8_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3801) (Sat.Literal.pos 3800) (Sat.Literal.pos 127) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation8 127 (assignment s)
    (Sat.Literal.pos 3801) (Sat.Literal.pos 3800) (Sat.Literal.pos 127) (Sat.Literal.pos 253) (positive_of_descriptor s 3801 (.lex permutation8 127) (by rfl)) (lex_8_127_prefix s) (positive_select s 127) (lex_8_127_image s)

theorem lex_8_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.pos 127), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation8 127 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3800) (Sat.Literal.pos 127) (Sat.Literal.pos 253) (lex_8_127_prefix s) (positive_select s 127) (lex_8_127_image s)

theorem lex_8_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.pos 3800)] :=
  (lex_8_127_gate s).prop _ (List.Mem.head _)

theorem lex_8_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.neg 127), (Sat.Literal.pos 253)] :=
  (lex_8_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.pos 127), (Sat.Literal.neg 253)] :=
  (lex_8_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.neg 127), (Sat.Literal.neg 253), (Sat.Literal.pos 3801)] :=
  (lex_8_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3800), (Sat.Literal.pos 127), (Sat.Literal.pos 253), (Sat.Literal.pos 3801)] :=
  (lex_8_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3801) = lexBefore s permutation8 126 := by
  exact (positive_lex_of_descriptor s 3801 permutation8 127 (by rfl)).trans ((lex_skipped s permutation8 126 127 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation8 126) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation8 126 by rw [image8_eq]; rfl))

theorem lex_8_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3802) (Sat.Literal.pos 3801) (Sat.Literal.pos 126) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation8 126 (assignment s)
    (Sat.Literal.pos 3802) (Sat.Literal.pos 3801) (Sat.Literal.pos 126) (Sat.Literal.pos 249) (positive_of_descriptor s 3802 (.lex permutation8 126) (by rfl)) (lex_8_126_prefix s) (positive_select s 126) (lex_8_126_image s)

theorem lex_8_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.pos 126), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation8 126 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3801) (Sat.Literal.pos 126) (Sat.Literal.pos 249) (lex_8_126_prefix s) (positive_select s 126) (lex_8_126_image s)

theorem lex_8_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.pos 3801)] :=
  (lex_8_126_gate s).prop _ (List.Mem.head _)

theorem lex_8_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.neg 126), (Sat.Literal.pos 249)] :=
  (lex_8_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.pos 126), (Sat.Literal.neg 249)] :=
  (lex_8_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.neg 126), (Sat.Literal.neg 249), (Sat.Literal.pos 3802)] :=
  (lex_8_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3801), (Sat.Literal.pos 126), (Sat.Literal.pos 249), (Sat.Literal.pos 3802)] :=
  (lex_8_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3802) = lexBefore s permutation8 125 := by
  exact (positive_lex_of_descriptor s 3802 permutation8 126 (by rfl)).trans ((lex_skipped s permutation8 125 126 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation8 125) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation8 125 by rw [image8_eq]; rfl))

theorem lex_8_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3803) (Sat.Literal.pos 3802) (Sat.Literal.pos 125) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation8 125 (assignment s)
    (Sat.Literal.pos 3803) (Sat.Literal.pos 3802) (Sat.Literal.pos 125) (Sat.Literal.pos 245) (positive_of_descriptor s 3803 (.lex permutation8 125) (by rfl)) (lex_8_125_prefix s) (positive_select s 125) (lex_8_125_image s)

theorem lex_8_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.pos 125), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation8 125 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3802) (Sat.Literal.pos 125) (Sat.Literal.pos 245) (lex_8_125_prefix s) (positive_select s 125) (lex_8_125_image s)

theorem lex_8_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.pos 3802)] :=
  (lex_8_125_gate s).prop _ (List.Mem.head _)

theorem lex_8_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.neg 125), (Sat.Literal.pos 245)] :=
  (lex_8_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.pos 125), (Sat.Literal.neg 245)] :=
  (lex_8_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.neg 125), (Sat.Literal.neg 245), (Sat.Literal.pos 3803)] :=
  (lex_8_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3802), (Sat.Literal.pos 125), (Sat.Literal.pos 245), (Sat.Literal.pos 3803)] :=
  (lex_8_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3803) = lexBefore s permutation8 124 := by
  exact (positive_lex_of_descriptor s 3803 permutation8 125 (by rfl)).trans ((lex_skipped s permutation8 124 125 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation8 124) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation8 124 by rw [image8_eq]; rfl))

theorem lex_8_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3804) (Sat.Literal.pos 3803) (Sat.Literal.pos 124) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation8 124 (assignment s)
    (Sat.Literal.pos 3804) (Sat.Literal.pos 3803) (Sat.Literal.pos 124) (Sat.Literal.pos 241) (positive_of_descriptor s 3804 (.lex permutation8 124) (by rfl)) (lex_8_124_prefix s) (positive_select s 124) (lex_8_124_image s)

theorem lex_8_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.pos 124), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation8 124 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3803) (Sat.Literal.pos 124) (Sat.Literal.pos 241) (lex_8_124_prefix s) (positive_select s 124) (lex_8_124_image s)

theorem lex_8_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.pos 3803)] :=
  (lex_8_124_gate s).prop _ (List.Mem.head _)

theorem lex_8_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.neg 124), (Sat.Literal.pos 241)] :=
  (lex_8_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.pos 124), (Sat.Literal.neg 241)] :=
  (lex_8_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.neg 124), (Sat.Literal.neg 241), (Sat.Literal.pos 3804)] :=
  (lex_8_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3803), (Sat.Literal.pos 124), (Sat.Literal.pos 241), (Sat.Literal.pos 3804)] :=
  (lex_8_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3804) = lexBefore s permutation8 123 := by
  exact (positive_lex_of_descriptor s 3804 permutation8 124 (by rfl)).trans ((lex_skipped s permutation8 123 124 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation8 123) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation8 123 by rw [image8_eq]; rfl))

theorem lex_8_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3805) (Sat.Literal.pos 3804) (Sat.Literal.pos 123) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation8 123 (assignment s)
    (Sat.Literal.pos 3805) (Sat.Literal.pos 3804) (Sat.Literal.pos 123) (Sat.Literal.pos 237) (positive_of_descriptor s 3805 (.lex permutation8 123) (by rfl)) (lex_8_123_prefix s) (positive_select s 123) (lex_8_123_image s)

theorem lex_8_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.pos 123), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation8 123 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3804) (Sat.Literal.pos 123) (Sat.Literal.pos 237) (lex_8_123_prefix s) (positive_select s 123) (lex_8_123_image s)

theorem lex_8_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.pos 3804)] :=
  (lex_8_123_gate s).prop _ (List.Mem.head _)

theorem lex_8_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.neg 123), (Sat.Literal.pos 237)] :=
  (lex_8_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.pos 123), (Sat.Literal.neg 237)] :=
  (lex_8_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.neg 123), (Sat.Literal.neg 237), (Sat.Literal.pos 3805)] :=
  (lex_8_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3804), (Sat.Literal.pos 123), (Sat.Literal.pos 237), (Sat.Literal.pos 3805)] :=
  (lex_8_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3805) = lexBefore s permutation8 122 := by
  exact (positive_lex_of_descriptor s 3805 permutation8 123 (by rfl)).trans ((lex_skipped s permutation8 122 123 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation8 122) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation8 122 by rw [image8_eq]; rfl))

theorem lex_8_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3806) (Sat.Literal.pos 3805) (Sat.Literal.pos 122) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation8 122 (assignment s)
    (Sat.Literal.pos 3806) (Sat.Literal.pos 3805) (Sat.Literal.pos 122) (Sat.Literal.pos 233) (positive_of_descriptor s 3806 (.lex permutation8 122) (by rfl)) (lex_8_122_prefix s) (positive_select s 122) (lex_8_122_image s)

theorem lex_8_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.pos 122), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation8 122 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3805) (Sat.Literal.pos 122) (Sat.Literal.pos 233) (lex_8_122_prefix s) (positive_select s 122) (lex_8_122_image s)

theorem lex_8_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.pos 3805)] :=
  (lex_8_122_gate s).prop _ (List.Mem.head _)

theorem lex_8_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.neg 122), (Sat.Literal.pos 233)] :=
  (lex_8_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.pos 122), (Sat.Literal.neg 233)] :=
  (lex_8_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.neg 122), (Sat.Literal.neg 233), (Sat.Literal.pos 3806)] :=
  (lex_8_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3805), (Sat.Literal.pos 122), (Sat.Literal.pos 233), (Sat.Literal.pos 3806)] :=
  (lex_8_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3806) = lexBefore s permutation8 121 := by
  exact (positive_lex_of_descriptor s 3806 permutation8 122 (by rfl)).trans ((lex_skipped s permutation8 121 122 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation8 121) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation8 121 by rw [image8_eq]; rfl))

theorem lex_8_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3807) (Sat.Literal.pos 3806) (Sat.Literal.pos 121) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation8 121 (assignment s)
    (Sat.Literal.pos 3807) (Sat.Literal.pos 3806) (Sat.Literal.pos 121) (Sat.Literal.pos 229) (positive_of_descriptor s 3807 (.lex permutation8 121) (by rfl)) (lex_8_121_prefix s) (positive_select s 121) (lex_8_121_image s)

theorem lex_8_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.pos 121), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation8 121 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3806) (Sat.Literal.pos 121) (Sat.Literal.pos 229) (lex_8_121_prefix s) (positive_select s 121) (lex_8_121_image s)

theorem lex_8_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.pos 3806)] :=
  (lex_8_121_gate s).prop _ (List.Mem.head _)

theorem lex_8_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.neg 121), (Sat.Literal.pos 229)] :=
  (lex_8_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.pos 121), (Sat.Literal.neg 229)] :=
  (lex_8_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.neg 121), (Sat.Literal.neg 229), (Sat.Literal.pos 3807)] :=
  (lex_8_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3806), (Sat.Literal.pos 121), (Sat.Literal.pos 229), (Sat.Literal.pos 3807)] :=
  (lex_8_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3807) = lexBefore s permutation8 120 := by
  exact (positive_lex_of_descriptor s 3807 permutation8 121 (by rfl)).trans ((lex_skipped s permutation8 120 121 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation8 120) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation8 120 by rw [image8_eq]; rfl))

theorem lex_8_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3808) (Sat.Literal.pos 3807) (Sat.Literal.pos 120) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation8 120 (assignment s)
    (Sat.Literal.pos 3808) (Sat.Literal.pos 3807) (Sat.Literal.pos 120) (Sat.Literal.pos 225) (positive_of_descriptor s 3808 (.lex permutation8 120) (by rfl)) (lex_8_120_prefix s) (positive_select s 120) (lex_8_120_image s)

theorem lex_8_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.pos 120), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation8 120 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3807) (Sat.Literal.pos 120) (Sat.Literal.pos 225) (lex_8_120_prefix s) (positive_select s 120) (lex_8_120_image s)

theorem lex_8_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.pos 3807)] :=
  (lex_8_120_gate s).prop _ (List.Mem.head _)

theorem lex_8_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.neg 120), (Sat.Literal.pos 225)] :=
  (lex_8_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.pos 120), (Sat.Literal.neg 225)] :=
  (lex_8_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.neg 120), (Sat.Literal.neg 225), (Sat.Literal.pos 3808)] :=
  (lex_8_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3807), (Sat.Literal.pos 120), (Sat.Literal.pos 225), (Sat.Literal.pos 3808)] :=
  (lex_8_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3808) = lexBefore s permutation8 119 := by
  exact (positive_lex_of_descriptor s 3808 permutation8 120 (by rfl)).trans ((lex_skipped s permutation8 119 120 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation8 119) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation8 119 by rw [image8_eq]; rfl))

theorem lex_8_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3809) (Sat.Literal.pos 3808) (Sat.Literal.pos 119) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation8 119 (assignment s)
    (Sat.Literal.pos 3809) (Sat.Literal.pos 3808) (Sat.Literal.pos 119) (Sat.Literal.pos 221) (positive_of_descriptor s 3809 (.lex permutation8 119) (by rfl)) (lex_8_119_prefix s) (positive_select s 119) (lex_8_119_image s)

theorem lex_8_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.pos 119), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation8 119 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3808) (Sat.Literal.pos 119) (Sat.Literal.pos 221) (lex_8_119_prefix s) (positive_select s 119) (lex_8_119_image s)

theorem lex_8_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.pos 3808)] :=
  (lex_8_119_gate s).prop _ (List.Mem.head _)

theorem lex_8_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.neg 119), (Sat.Literal.pos 221)] :=
  (lex_8_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.pos 119), (Sat.Literal.neg 221)] :=
  (lex_8_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.neg 119), (Sat.Literal.neg 221), (Sat.Literal.pos 3809)] :=
  (lex_8_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3808), (Sat.Literal.pos 119), (Sat.Literal.pos 221), (Sat.Literal.pos 3809)] :=
  (lex_8_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3809) = lexBefore s permutation8 118 := by
  exact (positive_lex_of_descriptor s 3809 permutation8 119 (by rfl)).trans ((lex_skipped s permutation8 118 119 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation8 118) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation8 118 by rw [image8_eq]; rfl))

theorem lex_8_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3810) (Sat.Literal.pos 3809) (Sat.Literal.pos 118) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation8 118 (assignment s)
    (Sat.Literal.pos 3810) (Sat.Literal.pos 3809) (Sat.Literal.pos 118) (Sat.Literal.pos 217) (positive_of_descriptor s 3810 (.lex permutation8 118) (by rfl)) (lex_8_118_prefix s) (positive_select s 118) (lex_8_118_image s)

theorem lex_8_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.pos 118), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation8 118 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3809) (Sat.Literal.pos 118) (Sat.Literal.pos 217) (lex_8_118_prefix s) (positive_select s 118) (lex_8_118_image s)

theorem lex_8_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.pos 3809)] :=
  (lex_8_118_gate s).prop _ (List.Mem.head _)

theorem lex_8_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.neg 118), (Sat.Literal.pos 217)] :=
  (lex_8_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.pos 118), (Sat.Literal.neg 217)] :=
  (lex_8_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.neg 118), (Sat.Literal.neg 217), (Sat.Literal.pos 3810)] :=
  (lex_8_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3809), (Sat.Literal.pos 118), (Sat.Literal.pos 217), (Sat.Literal.pos 3810)] :=
  (lex_8_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3810) = lexBefore s permutation8 117 := by
  exact (positive_lex_of_descriptor s 3810 permutation8 118 (by rfl)).trans ((lex_skipped s permutation8 117 118 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation8 117) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation8 117 by rw [image8_eq]; rfl))

theorem lex_8_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3811) (Sat.Literal.pos 3810) (Sat.Literal.pos 117) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation8 117 (assignment s)
    (Sat.Literal.pos 3811) (Sat.Literal.pos 3810) (Sat.Literal.pos 117) (Sat.Literal.pos 213) (positive_of_descriptor s 3811 (.lex permutation8 117) (by rfl)) (lex_8_117_prefix s) (positive_select s 117) (lex_8_117_image s)

theorem lex_8_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.pos 117), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation8 117 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3810) (Sat.Literal.pos 117) (Sat.Literal.pos 213) (lex_8_117_prefix s) (positive_select s 117) (lex_8_117_image s)

theorem lex_8_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.pos 3810)] :=
  (lex_8_117_gate s).prop _ (List.Mem.head _)

theorem lex_8_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.neg 117), (Sat.Literal.pos 213)] :=
  (lex_8_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.pos 117), (Sat.Literal.neg 213)] :=
  (lex_8_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.neg 117), (Sat.Literal.neg 213), (Sat.Literal.pos 3811)] :=
  (lex_8_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3810), (Sat.Literal.pos 117), (Sat.Literal.pos 213), (Sat.Literal.pos 3811)] :=
  (lex_8_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3811) = lexBefore s permutation8 116 := by
  exact (positive_lex_of_descriptor s 3811 permutation8 117 (by rfl)).trans ((lex_skipped s permutation8 116 117 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation8 116) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation8 116 by rw [image8_eq]; rfl))

theorem lex_8_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3812) (Sat.Literal.pos 3811) (Sat.Literal.pos 116) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation8 116 (assignment s)
    (Sat.Literal.pos 3812) (Sat.Literal.pos 3811) (Sat.Literal.pos 116) (Sat.Literal.pos 209) (positive_of_descriptor s 3812 (.lex permutation8 116) (by rfl)) (lex_8_116_prefix s) (positive_select s 116) (lex_8_116_image s)

theorem lex_8_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.pos 116), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation8 116 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3811) (Sat.Literal.pos 116) (Sat.Literal.pos 209) (lex_8_116_prefix s) (positive_select s 116) (lex_8_116_image s)

theorem lex_8_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.pos 3811)] :=
  (lex_8_116_gate s).prop _ (List.Mem.head _)

theorem lex_8_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.neg 116), (Sat.Literal.pos 209)] :=
  (lex_8_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.pos 116), (Sat.Literal.neg 209)] :=
  (lex_8_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.neg 116), (Sat.Literal.neg 209), (Sat.Literal.pos 3812)] :=
  (lex_8_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3811), (Sat.Literal.pos 116), (Sat.Literal.pos 209), (Sat.Literal.pos 3812)] :=
  (lex_8_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3812) = lexBefore s permutation8 115 := by
  exact (positive_lex_of_descriptor s 3812 permutation8 116 (by rfl)).trans ((lex_skipped s permutation8 115 116 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation8 115) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation8 115 by rw [image8_eq]; rfl))

theorem lex_8_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3813) (Sat.Literal.pos 3812) (Sat.Literal.pos 115) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation8 115 (assignment s)
    (Sat.Literal.pos 3813) (Sat.Literal.pos 3812) (Sat.Literal.pos 115) (Sat.Literal.pos 205) (positive_of_descriptor s 3813 (.lex permutation8 115) (by rfl)) (lex_8_115_prefix s) (positive_select s 115) (lex_8_115_image s)

theorem lex_8_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.pos 115), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation8 115 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3812) (Sat.Literal.pos 115) (Sat.Literal.pos 205) (lex_8_115_prefix s) (positive_select s 115) (lex_8_115_image s)

theorem lex_8_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.pos 3812)] :=
  (lex_8_115_gate s).prop _ (List.Mem.head _)

theorem lex_8_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.neg 115), (Sat.Literal.pos 205)] :=
  (lex_8_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.pos 115), (Sat.Literal.neg 205)] :=
  (lex_8_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.neg 115), (Sat.Literal.neg 205), (Sat.Literal.pos 3813)] :=
  (lex_8_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3812), (Sat.Literal.pos 115), (Sat.Literal.pos 205), (Sat.Literal.pos 3813)] :=
  (lex_8_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3813) = lexBefore s permutation8 114 := by
  exact (positive_lex_of_descriptor s 3813 permutation8 115 (by rfl)).trans ((lex_skipped s permutation8 114 115 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation8 114) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation8 114 by rw [image8_eq]; rfl))

theorem lex_8_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3814) (Sat.Literal.pos 3813) (Sat.Literal.pos 114) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation8 114 (assignment s)
    (Sat.Literal.pos 3814) (Sat.Literal.pos 3813) (Sat.Literal.pos 114) (Sat.Literal.pos 201) (positive_of_descriptor s 3814 (.lex permutation8 114) (by rfl)) (lex_8_114_prefix s) (positive_select s 114) (lex_8_114_image s)

theorem lex_8_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.pos 114), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation8 114 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3813) (Sat.Literal.pos 114) (Sat.Literal.pos 201) (lex_8_114_prefix s) (positive_select s 114) (lex_8_114_image s)

theorem lex_8_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.pos 3813)] :=
  (lex_8_114_gate s).prop _ (List.Mem.head _)

theorem lex_8_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.neg 114), (Sat.Literal.pos 201)] :=
  (lex_8_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.pos 114), (Sat.Literal.neg 201)] :=
  (lex_8_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.neg 114), (Sat.Literal.neg 201), (Sat.Literal.pos 3814)] :=
  (lex_8_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3813), (Sat.Literal.pos 114), (Sat.Literal.pos 201), (Sat.Literal.pos 3814)] :=
  (lex_8_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3814) = lexBefore s permutation8 113 := by
  exact (positive_lex_of_descriptor s 3814 permutation8 114 (by rfl)).trans ((lex_skipped s permutation8 113 114 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation8 113) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation8 113 by rw [image8_eq]; rfl))

theorem lex_8_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3815) (Sat.Literal.pos 3814) (Sat.Literal.pos 113) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation8 113 (assignment s)
    (Sat.Literal.pos 3815) (Sat.Literal.pos 3814) (Sat.Literal.pos 113) (Sat.Literal.pos 197) (positive_of_descriptor s 3815 (.lex permutation8 113) (by rfl)) (lex_8_113_prefix s) (positive_select s 113) (lex_8_113_image s)

theorem lex_8_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.pos 113), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation8 113 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3814) (Sat.Literal.pos 113) (Sat.Literal.pos 197) (lex_8_113_prefix s) (positive_select s 113) (lex_8_113_image s)

theorem lex_8_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.pos 3814)] :=
  (lex_8_113_gate s).prop _ (List.Mem.head _)

theorem lex_8_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.neg 113), (Sat.Literal.pos 197)] :=
  (lex_8_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.pos 113), (Sat.Literal.neg 197)] :=
  (lex_8_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.neg 113), (Sat.Literal.neg 197), (Sat.Literal.pos 3815)] :=
  (lex_8_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3814), (Sat.Literal.pos 113), (Sat.Literal.pos 197), (Sat.Literal.pos 3815)] :=
  (lex_8_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3815) = lexBefore s permutation8 112 := by
  exact (positive_lex_of_descriptor s 3815 permutation8 113 (by rfl)).trans ((lex_skipped s permutation8 112 113 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation8 112) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation8 112 by rw [image8_eq]; rfl))

theorem lex_8_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3816) (Sat.Literal.pos 3815) (Sat.Literal.pos 112) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation8 112 (assignment s)
    (Sat.Literal.pos 3816) (Sat.Literal.pos 3815) (Sat.Literal.pos 112) (Sat.Literal.pos 193) (positive_of_descriptor s 3816 (.lex permutation8 112) (by rfl)) (lex_8_112_prefix s) (positive_select s 112) (lex_8_112_image s)

theorem lex_8_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.pos 112), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation8 112 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3815) (Sat.Literal.pos 112) (Sat.Literal.pos 193) (lex_8_112_prefix s) (positive_select s 112) (lex_8_112_image s)

theorem lex_8_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.pos 3815)] :=
  (lex_8_112_gate s).prop _ (List.Mem.head _)

theorem lex_8_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.neg 112), (Sat.Literal.pos 193)] :=
  (lex_8_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.pos 112), (Sat.Literal.neg 193)] :=
  (lex_8_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.neg 112), (Sat.Literal.neg 193), (Sat.Literal.pos 3816)] :=
  (lex_8_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3815), (Sat.Literal.pos 112), (Sat.Literal.pos 193), (Sat.Literal.pos 3816)] :=
  (lex_8_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3816) = lexBefore s permutation8 111 := by
  exact (positive_lex_of_descriptor s 3816 permutation8 112 (by rfl)).trans ((lex_skipped s permutation8 111 112 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation8 111) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation8 111 by rw [image8_eq]; rfl))

theorem lex_8_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3817) (Sat.Literal.pos 3816) (Sat.Literal.pos 111) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation8 111 (assignment s)
    (Sat.Literal.pos 3817) (Sat.Literal.pos 3816) (Sat.Literal.pos 111) (Sat.Literal.pos 189) (positive_of_descriptor s 3817 (.lex permutation8 111) (by rfl)) (lex_8_111_prefix s) (positive_select s 111) (lex_8_111_image s)

theorem lex_8_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.pos 111), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation8 111 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3816) (Sat.Literal.pos 111) (Sat.Literal.pos 189) (lex_8_111_prefix s) (positive_select s 111) (lex_8_111_image s)

theorem lex_8_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.pos 3816)] :=
  (lex_8_111_gate s).prop _ (List.Mem.head _)

theorem lex_8_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.neg 111), (Sat.Literal.pos 189)] :=
  (lex_8_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.pos 111), (Sat.Literal.neg 189)] :=
  (lex_8_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.neg 111), (Sat.Literal.neg 189), (Sat.Literal.pos 3817)] :=
  (lex_8_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3816), (Sat.Literal.pos 111), (Sat.Literal.pos 189), (Sat.Literal.pos 3817)] :=
  (lex_8_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3817) = lexBefore s permutation8 110 := by
  exact (positive_lex_of_descriptor s 3817 permutation8 111 (by rfl)).trans ((lex_skipped s permutation8 110 111 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation8 110) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation8 110 by rw [image8_eq]; rfl))

theorem lex_8_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3818) (Sat.Literal.pos 3817) (Sat.Literal.pos 110) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation8 110 (assignment s)
    (Sat.Literal.pos 3818) (Sat.Literal.pos 3817) (Sat.Literal.pos 110) (Sat.Literal.pos 185) (positive_of_descriptor s 3818 (.lex permutation8 110) (by rfl)) (lex_8_110_prefix s) (positive_select s 110) (lex_8_110_image s)

theorem lex_8_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.pos 110), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation8 110 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3817) (Sat.Literal.pos 110) (Sat.Literal.pos 185) (lex_8_110_prefix s) (positive_select s 110) (lex_8_110_image s)

theorem lex_8_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.pos 3817)] :=
  (lex_8_110_gate s).prop _ (List.Mem.head _)

theorem lex_8_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.neg 110), (Sat.Literal.pos 185)] :=
  (lex_8_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.pos 110), (Sat.Literal.neg 185)] :=
  (lex_8_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.neg 110), (Sat.Literal.neg 185), (Sat.Literal.pos 3818)] :=
  (lex_8_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3817), (Sat.Literal.pos 110), (Sat.Literal.pos 185), (Sat.Literal.pos 3818)] :=
  (lex_8_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3818) = lexBefore s permutation8 109 := by
  exact (positive_lex_of_descriptor s 3818 permutation8 110 (by rfl)).trans ((lex_skipped s permutation8 109 110 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation8 109) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation8 109 by rw [image8_eq]; rfl))

theorem lex_8_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3819) (Sat.Literal.pos 3818) (Sat.Literal.pos 109) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation8 109 (assignment s)
    (Sat.Literal.pos 3819) (Sat.Literal.pos 3818) (Sat.Literal.pos 109) (Sat.Literal.pos 181) (positive_of_descriptor s 3819 (.lex permutation8 109) (by rfl)) (lex_8_109_prefix s) (positive_select s 109) (lex_8_109_image s)

theorem lex_8_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.pos 109), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation8 109 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3818) (Sat.Literal.pos 109) (Sat.Literal.pos 181) (lex_8_109_prefix s) (positive_select s 109) (lex_8_109_image s)

theorem lex_8_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.pos 3818)] :=
  (lex_8_109_gate s).prop _ (List.Mem.head _)

theorem lex_8_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.neg 109), (Sat.Literal.pos 181)] :=
  (lex_8_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.pos 109), (Sat.Literal.neg 181)] :=
  (lex_8_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.neg 109), (Sat.Literal.neg 181), (Sat.Literal.pos 3819)] :=
  (lex_8_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3818), (Sat.Literal.pos 109), (Sat.Literal.pos 181), (Sat.Literal.pos 3819)] :=
  (lex_8_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3819) = lexBefore s permutation8 108 := by
  exact (positive_lex_of_descriptor s 3819 permutation8 109 (by rfl)).trans ((lex_skipped s permutation8 108 109 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation8 108) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation8 108 by rw [image8_eq]; rfl))

theorem lex_8_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3820) (Sat.Literal.pos 3819) (Sat.Literal.pos 108) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation8 108 (assignment s)
    (Sat.Literal.pos 3820) (Sat.Literal.pos 3819) (Sat.Literal.pos 108) (Sat.Literal.pos 177) (positive_of_descriptor s 3820 (.lex permutation8 108) (by rfl)) (lex_8_108_prefix s) (positive_select s 108) (lex_8_108_image s)

theorem lex_8_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.pos 108), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation8 108 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3819) (Sat.Literal.pos 108) (Sat.Literal.pos 177) (lex_8_108_prefix s) (positive_select s 108) (lex_8_108_image s)

theorem lex_8_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.pos 3819)] :=
  (lex_8_108_gate s).prop _ (List.Mem.head _)

theorem lex_8_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.neg 108), (Sat.Literal.pos 177)] :=
  (lex_8_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.pos 108), (Sat.Literal.neg 177)] :=
  (lex_8_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.neg 108), (Sat.Literal.neg 177), (Sat.Literal.pos 3820)] :=
  (lex_8_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3819), (Sat.Literal.pos 108), (Sat.Literal.pos 177), (Sat.Literal.pos 3820)] :=
  (lex_8_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3820) = lexBefore s permutation8 107 := by
  exact (positive_lex_of_descriptor s 3820 permutation8 108 (by rfl)).trans ((lex_skipped s permutation8 107 108 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation8 107) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation8 107 by rw [image8_eq]; rfl))

theorem lex_8_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3821) (Sat.Literal.pos 3820) (Sat.Literal.pos 107) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation8 107 (assignment s)
    (Sat.Literal.pos 3821) (Sat.Literal.pos 3820) (Sat.Literal.pos 107) (Sat.Literal.pos 173) (positive_of_descriptor s 3821 (.lex permutation8 107) (by rfl)) (lex_8_107_prefix s) (positive_select s 107) (lex_8_107_image s)

theorem lex_8_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.pos 107), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation8 107 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3820) (Sat.Literal.pos 107) (Sat.Literal.pos 173) (lex_8_107_prefix s) (positive_select s 107) (lex_8_107_image s)

theorem lex_8_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.pos 3820)] :=
  (lex_8_107_gate s).prop _ (List.Mem.head _)

theorem lex_8_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.neg 107), (Sat.Literal.pos 173)] :=
  (lex_8_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.pos 107), (Sat.Literal.neg 173)] :=
  (lex_8_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.neg 107), (Sat.Literal.neg 173), (Sat.Literal.pos 3821)] :=
  (lex_8_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3820), (Sat.Literal.pos 107), (Sat.Literal.pos 173), (Sat.Literal.pos 3821)] :=
  (lex_8_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3821) = lexBefore s permutation8 106 := by
  exact (positive_lex_of_descriptor s 3821 permutation8 107 (by rfl)).trans ((lex_skipped s permutation8 106 107 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation8 106) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation8 106 by rw [image8_eq]; rfl))

theorem lex_8_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3822) (Sat.Literal.pos 3821) (Sat.Literal.pos 106) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation8 106 (assignment s)
    (Sat.Literal.pos 3822) (Sat.Literal.pos 3821) (Sat.Literal.pos 106) (Sat.Literal.pos 169) (positive_of_descriptor s 3822 (.lex permutation8 106) (by rfl)) (lex_8_106_prefix s) (positive_select s 106) (lex_8_106_image s)

theorem lex_8_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.pos 106), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation8 106 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3821) (Sat.Literal.pos 106) (Sat.Literal.pos 169) (lex_8_106_prefix s) (positive_select s 106) (lex_8_106_image s)

theorem lex_8_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.pos 3821)] :=
  (lex_8_106_gate s).prop _ (List.Mem.head _)

theorem lex_8_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.neg 106), (Sat.Literal.pos 169)] :=
  (lex_8_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.pos 106), (Sat.Literal.neg 169)] :=
  (lex_8_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.neg 106), (Sat.Literal.neg 169), (Sat.Literal.pos 3822)] :=
  (lex_8_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3821), (Sat.Literal.pos 106), (Sat.Literal.pos 169), (Sat.Literal.pos 3822)] :=
  (lex_8_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3822) = lexBefore s permutation8 105 := by
  exact (positive_lex_of_descriptor s 3822 permutation8 106 (by rfl)).trans ((lex_skipped s permutation8 105 106 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation8 105) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation8 105 by rw [image8_eq]; rfl))

theorem lex_8_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3823) (Sat.Literal.pos 3822) (Sat.Literal.pos 105) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation8 105 (assignment s)
    (Sat.Literal.pos 3823) (Sat.Literal.pos 3822) (Sat.Literal.pos 105) (Sat.Literal.pos 165) (positive_of_descriptor s 3823 (.lex permutation8 105) (by rfl)) (lex_8_105_prefix s) (positive_select s 105) (lex_8_105_image s)

theorem lex_8_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.pos 105), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation8 105 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3822) (Sat.Literal.pos 105) (Sat.Literal.pos 165) (lex_8_105_prefix s) (positive_select s 105) (lex_8_105_image s)

theorem lex_8_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.pos 3822)] :=
  (lex_8_105_gate s).prop _ (List.Mem.head _)

theorem lex_8_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.neg 105), (Sat.Literal.pos 165)] :=
  (lex_8_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.pos 105), (Sat.Literal.neg 165)] :=
  (lex_8_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.neg 105), (Sat.Literal.neg 165), (Sat.Literal.pos 3823)] :=
  (lex_8_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3822), (Sat.Literal.pos 105), (Sat.Literal.pos 165), (Sat.Literal.pos 3823)] :=
  (lex_8_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3823) = lexBefore s permutation8 104 := by
  exact (positive_lex_of_descriptor s 3823 permutation8 105 (by rfl)).trans ((lex_skipped s permutation8 104 105 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation8 104) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation8 104 by rw [image8_eq]; rfl))

theorem lex_8_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3824) (Sat.Literal.pos 3823) (Sat.Literal.pos 104) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation8 104 (assignment s)
    (Sat.Literal.pos 3824) (Sat.Literal.pos 3823) (Sat.Literal.pos 104) (Sat.Literal.pos 161) (positive_of_descriptor s 3824 (.lex permutation8 104) (by rfl)) (lex_8_104_prefix s) (positive_select s 104) (lex_8_104_image s)

theorem lex_8_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.pos 104), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation8 104 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3823) (Sat.Literal.pos 104) (Sat.Literal.pos 161) (lex_8_104_prefix s) (positive_select s 104) (lex_8_104_image s)

theorem lex_8_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.pos 3823)] :=
  (lex_8_104_gate s).prop _ (List.Mem.head _)

theorem lex_8_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.neg 104), (Sat.Literal.pos 161)] :=
  (lex_8_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.pos 104), (Sat.Literal.neg 161)] :=
  (lex_8_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.neg 104), (Sat.Literal.neg 161), (Sat.Literal.pos 3824)] :=
  (lex_8_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3823), (Sat.Literal.pos 104), (Sat.Literal.pos 161), (Sat.Literal.pos 3824)] :=
  (lex_8_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_8_204_gate

end Crown.CertificateData
