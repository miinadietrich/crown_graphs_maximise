import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_9_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4024) = lexBefore s permutation9 156 := by
  exact (positive_lex_of_descriptor s 4024 permutation9 157 (by rfl)).trans ((lex_skipped s permutation9 156 157 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation9 156) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation9 156 by rw [image9_eq]; rfl))

theorem lex_9_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4025) (Sat.Literal.pos 4024) (Sat.Literal.pos 156) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation9 156 (assignment s)
    (Sat.Literal.pos 4025) (Sat.Literal.pos 4024) (Sat.Literal.pos 156) (Sat.Literal.pos 228) (positive_of_descriptor s 4025 (.lex permutation9 156) (by rfl)) (lex_9_156_prefix s) (positive_select s 156) (lex_9_156_image s)

theorem lex_9_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.pos 156), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation9 156 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4024) (Sat.Literal.pos 156) (Sat.Literal.pos 228) (lex_9_156_prefix s) (positive_select s 156) (lex_9_156_image s)

theorem lex_9_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.pos 4024)] :=
  (lex_9_156_gate s).prop _ (List.Mem.head _)

theorem lex_9_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.neg 156), (Sat.Literal.pos 228)] :=
  (lex_9_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.pos 156), (Sat.Literal.neg 228)] :=
  (lex_9_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.neg 156), (Sat.Literal.neg 228), (Sat.Literal.pos 4025)] :=
  (lex_9_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.pos 156), (Sat.Literal.pos 228), (Sat.Literal.pos 4025)] :=
  (lex_9_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4025) = lexBefore s permutation9 155 := by
  exact (positive_lex_of_descriptor s 4025 permutation9 156 (by rfl)).trans ((lex_skipped s permutation9 155 156 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation9 155) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation9 155 by rw [image9_eq]; rfl))

theorem lex_9_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4026) (Sat.Literal.pos 4025) (Sat.Literal.pos 155) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation9 155 (assignment s)
    (Sat.Literal.pos 4026) (Sat.Literal.pos 4025) (Sat.Literal.pos 155) (Sat.Literal.pos 220) (positive_of_descriptor s 4026 (.lex permutation9 155) (by rfl)) (lex_9_155_prefix s) (positive_select s 155) (lex_9_155_image s)

theorem lex_9_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.pos 155), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation9 155 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4025) (Sat.Literal.pos 155) (Sat.Literal.pos 220) (lex_9_155_prefix s) (positive_select s 155) (lex_9_155_image s)

theorem lex_9_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.pos 4025)] :=
  (lex_9_155_gate s).prop _ (List.Mem.head _)

theorem lex_9_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.neg 155), (Sat.Literal.pos 220)] :=
  (lex_9_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.pos 155), (Sat.Literal.neg 220)] :=
  (lex_9_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.neg 155), (Sat.Literal.neg 220), (Sat.Literal.pos 4026)] :=
  (lex_9_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4025), (Sat.Literal.pos 155), (Sat.Literal.pos 220), (Sat.Literal.pos 4026)] :=
  (lex_9_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4026) = lexBefore s permutation9 154 := by
  exact (positive_lex_of_descriptor s 4026 permutation9 155 (by rfl)).trans ((lex_skipped s permutation9 154 155 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation9 154) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation9 154 by rw [image9_eq]; rfl))

theorem lex_9_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4027) (Sat.Literal.pos 4026) (Sat.Literal.pos 154) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation9 154 (assignment s)
    (Sat.Literal.pos 4027) (Sat.Literal.pos 4026) (Sat.Literal.pos 154) (Sat.Literal.pos 212) (positive_of_descriptor s 4027 (.lex permutation9 154) (by rfl)) (lex_9_154_prefix s) (positive_select s 154) (lex_9_154_image s)

theorem lex_9_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.pos 154), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation9 154 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4026) (Sat.Literal.pos 154) (Sat.Literal.pos 212) (lex_9_154_prefix s) (positive_select s 154) (lex_9_154_image s)

theorem lex_9_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.pos 4026)] :=
  (lex_9_154_gate s).prop _ (List.Mem.head _)

theorem lex_9_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.neg 154), (Sat.Literal.pos 212)] :=
  (lex_9_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.pos 154), (Sat.Literal.neg 212)] :=
  (lex_9_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.neg 154), (Sat.Literal.neg 212), (Sat.Literal.pos 4027)] :=
  (lex_9_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4026), (Sat.Literal.pos 154), (Sat.Literal.pos 212), (Sat.Literal.pos 4027)] :=
  (lex_9_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4027) = lexBefore s permutation9 153 := by
  exact (positive_lex_of_descriptor s 4027 permutation9 154 (by rfl)).trans ((lex_skipped s permutation9 153 154 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation9 153) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation9 153 by rw [image9_eq]; rfl))

theorem lex_9_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4028) (Sat.Literal.pos 4027) (Sat.Literal.pos 153) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation9 153 (assignment s)
    (Sat.Literal.pos 4028) (Sat.Literal.pos 4027) (Sat.Literal.pos 153) (Sat.Literal.pos 204) (positive_of_descriptor s 4028 (.lex permutation9 153) (by rfl)) (lex_9_153_prefix s) (positive_select s 153) (lex_9_153_image s)

theorem lex_9_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.pos 153), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation9 153 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4027) (Sat.Literal.pos 153) (Sat.Literal.pos 204) (lex_9_153_prefix s) (positive_select s 153) (lex_9_153_image s)

theorem lex_9_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.pos 4027)] :=
  (lex_9_153_gate s).prop _ (List.Mem.head _)

theorem lex_9_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.neg 153), (Sat.Literal.pos 204)] :=
  (lex_9_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.pos 153), (Sat.Literal.neg 204)] :=
  (lex_9_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.neg 153), (Sat.Literal.neg 204), (Sat.Literal.pos 4028)] :=
  (lex_9_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4027), (Sat.Literal.pos 153), (Sat.Literal.pos 204), (Sat.Literal.pos 4028)] :=
  (lex_9_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4028) = lexBefore s permutation9 152 := by
  exact (positive_lex_of_descriptor s 4028 permutation9 153 (by rfl)).trans ((lex_skipped s permutation9 152 153 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation9 152) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation9 152 by rw [image9_eq]; rfl))

theorem lex_9_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4029) (Sat.Literal.pos 4028) (Sat.Literal.pos 152) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation9 152 (assignment s)
    (Sat.Literal.pos 4029) (Sat.Literal.pos 4028) (Sat.Literal.pos 152) (Sat.Literal.pos 196) (positive_of_descriptor s 4029 (.lex permutation9 152) (by rfl)) (lex_9_152_prefix s) (positive_select s 152) (lex_9_152_image s)

theorem lex_9_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.pos 152), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation9 152 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4028) (Sat.Literal.pos 152) (Sat.Literal.pos 196) (lex_9_152_prefix s) (positive_select s 152) (lex_9_152_image s)

theorem lex_9_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.pos 4028)] :=
  (lex_9_152_gate s).prop _ (List.Mem.head _)

theorem lex_9_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.neg 152), (Sat.Literal.pos 196)] :=
  (lex_9_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.pos 152), (Sat.Literal.neg 196)] :=
  (lex_9_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.neg 152), (Sat.Literal.neg 196), (Sat.Literal.pos 4029)] :=
  (lex_9_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4028), (Sat.Literal.pos 152), (Sat.Literal.pos 196), (Sat.Literal.pos 4029)] :=
  (lex_9_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4029) = lexBefore s permutation9 151 := by
  exact (positive_lex_of_descriptor s 4029 permutation9 152 (by rfl)).trans ((lex_skipped s permutation9 151 152 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation9 151) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation9 151 by rw [image9_eq]; rfl))

theorem lex_9_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4030) (Sat.Literal.pos 4029) (Sat.Literal.pos 151) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation9 151 (assignment s)
    (Sat.Literal.pos 4030) (Sat.Literal.pos 4029) (Sat.Literal.pos 151) (Sat.Literal.pos 188) (positive_of_descriptor s 4030 (.lex permutation9 151) (by rfl)) (lex_9_151_prefix s) (positive_select s 151) (lex_9_151_image s)

theorem lex_9_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.pos 151), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation9 151 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4029) (Sat.Literal.pos 151) (Sat.Literal.pos 188) (lex_9_151_prefix s) (positive_select s 151) (lex_9_151_image s)

theorem lex_9_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.pos 4029)] :=
  (lex_9_151_gate s).prop _ (List.Mem.head _)

theorem lex_9_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.neg 151), (Sat.Literal.pos 188)] :=
  (lex_9_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.pos 151), (Sat.Literal.neg 188)] :=
  (lex_9_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.neg 151), (Sat.Literal.neg 188), (Sat.Literal.pos 4030)] :=
  (lex_9_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4029), (Sat.Literal.pos 151), (Sat.Literal.pos 188), (Sat.Literal.pos 4030)] :=
  (lex_9_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4030) = lexBefore s permutation9 150 := by
  exact (positive_lex_of_descriptor s 4030 permutation9 151 (by rfl)).trans ((lex_skipped s permutation9 150 151 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation9 150) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation9 150 by rw [image9_eq]; rfl))

theorem lex_9_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4031) (Sat.Literal.pos 4030) (Sat.Literal.pos 150) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation9 150 (assignment s)
    (Sat.Literal.pos 4031) (Sat.Literal.pos 4030) (Sat.Literal.pos 150) (Sat.Literal.pos 180) (positive_of_descriptor s 4031 (.lex permutation9 150) (by rfl)) (lex_9_150_prefix s) (positive_select s 150) (lex_9_150_image s)

theorem lex_9_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.pos 150), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation9 150 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4030) (Sat.Literal.pos 150) (Sat.Literal.pos 180) (lex_9_150_prefix s) (positive_select s 150) (lex_9_150_image s)

theorem lex_9_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.pos 4030)] :=
  (lex_9_150_gate s).prop _ (List.Mem.head _)

theorem lex_9_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.neg 150), (Sat.Literal.pos 180)] :=
  (lex_9_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.pos 150), (Sat.Literal.neg 180)] :=
  (lex_9_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.neg 150), (Sat.Literal.neg 180), (Sat.Literal.pos 4031)] :=
  (lex_9_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4030), (Sat.Literal.pos 150), (Sat.Literal.pos 180), (Sat.Literal.pos 4031)] :=
  (lex_9_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4031) = lexBefore s permutation9 149 := by
  exact (positive_lex_of_descriptor s 4031 permutation9 150 (by rfl)).trans ((lex_skipped s permutation9 149 150 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation9 149) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation9 149 by rw [image9_eq]; rfl))

theorem lex_9_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4032) (Sat.Literal.pos 4031) (Sat.Literal.pos 149) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation9 149 (assignment s)
    (Sat.Literal.pos 4032) (Sat.Literal.pos 4031) (Sat.Literal.pos 149) (Sat.Literal.pos 172) (positive_of_descriptor s 4032 (.lex permutation9 149) (by rfl)) (lex_9_149_prefix s) (positive_select s 149) (lex_9_149_image s)

theorem lex_9_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.pos 149), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation9 149 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4031) (Sat.Literal.pos 149) (Sat.Literal.pos 172) (lex_9_149_prefix s) (positive_select s 149) (lex_9_149_image s)

theorem lex_9_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.pos 4031)] :=
  (lex_9_149_gate s).prop _ (List.Mem.head _)

theorem lex_9_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.neg 149), (Sat.Literal.pos 172)] :=
  (lex_9_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.pos 149), (Sat.Literal.neg 172)] :=
  (lex_9_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.neg 149), (Sat.Literal.neg 172), (Sat.Literal.pos 4032)] :=
  (lex_9_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4031), (Sat.Literal.pos 149), (Sat.Literal.pos 172), (Sat.Literal.pos 4032)] :=
  (lex_9_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4032) = lexBefore s permutation9 148 := by
  exact (positive_lex_of_descriptor s 4032 permutation9 149 (by rfl)).trans ((lex_skipped s permutation9 148 149 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation9 148) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation9 148 by rw [image9_eq]; rfl))

theorem lex_9_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4033) (Sat.Literal.pos 4032) (Sat.Literal.pos 148) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation9 148 (assignment s)
    (Sat.Literal.pos 4033) (Sat.Literal.pos 4032) (Sat.Literal.pos 148) (Sat.Literal.pos 164) (positive_of_descriptor s 4033 (.lex permutation9 148) (by rfl)) (lex_9_148_prefix s) (positive_select s 148) (lex_9_148_image s)

theorem lex_9_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.pos 148), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation9 148 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4032) (Sat.Literal.pos 148) (Sat.Literal.pos 164) (lex_9_148_prefix s) (positive_select s 148) (lex_9_148_image s)

theorem lex_9_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.pos 4032)] :=
  (lex_9_148_gate s).prop _ (List.Mem.head _)

theorem lex_9_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.neg 148), (Sat.Literal.pos 164)] :=
  (lex_9_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.pos 148), (Sat.Literal.neg 164)] :=
  (lex_9_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.neg 148), (Sat.Literal.neg 164), (Sat.Literal.pos 4033)] :=
  (lex_9_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4032), (Sat.Literal.pos 148), (Sat.Literal.pos 164), (Sat.Literal.pos 4033)] :=
  (lex_9_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4033) = lexBefore s permutation9 147 := by
  exact (positive_lex_of_descriptor s 4033 permutation9 148 (by rfl)).trans ((lex_skipped s permutation9 147 148 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation9 147) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation9 147 by rw [image9_eq]; rfl))

theorem lex_9_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4034) (Sat.Literal.pos 4033) (Sat.Literal.pos 147) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation9 147 (assignment s)
    (Sat.Literal.pos 4034) (Sat.Literal.pos 4033) (Sat.Literal.pos 147) (Sat.Literal.pos 156) (positive_of_descriptor s 4034 (.lex permutation9 147) (by rfl)) (lex_9_147_prefix s) (positive_select s 147) (lex_9_147_image s)

theorem lex_9_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.pos 147), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation9 147 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4033) (Sat.Literal.pos 147) (Sat.Literal.pos 156) (lex_9_147_prefix s) (positive_select s 147) (lex_9_147_image s)

theorem lex_9_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.pos 4033)] :=
  (lex_9_147_gate s).prop _ (List.Mem.head _)

theorem lex_9_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.neg 147), (Sat.Literal.pos 156)] :=
  (lex_9_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.pos 147), (Sat.Literal.neg 156)] :=
  (lex_9_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.neg 147), (Sat.Literal.neg 156), (Sat.Literal.pos 4034)] :=
  (lex_9_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4033), (Sat.Literal.pos 147), (Sat.Literal.pos 156), (Sat.Literal.pos 4034)] :=
  (lex_9_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4034) = lexBefore s permutation9 146 := by
  exact (positive_lex_of_descriptor s 4034 permutation9 147 (by rfl)).trans ((lex_skipped s permutation9 146 147 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation9 146) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation9 146 by rw [image9_eq]; rfl))

theorem lex_9_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4035) (Sat.Literal.pos 4034) (Sat.Literal.pos 146) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation9 146 (assignment s)
    (Sat.Literal.pos 4035) (Sat.Literal.pos 4034) (Sat.Literal.pos 146) (Sat.Literal.pos 148) (positive_of_descriptor s 4035 (.lex permutation9 146) (by rfl)) (lex_9_146_prefix s) (positive_select s 146) (lex_9_146_image s)

theorem lex_9_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.pos 146), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation9 146 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4034) (Sat.Literal.pos 146) (Sat.Literal.pos 148) (lex_9_146_prefix s) (positive_select s 146) (lex_9_146_image s)

theorem lex_9_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.pos 4034)] :=
  (lex_9_146_gate s).prop _ (List.Mem.head _)

theorem lex_9_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.neg 146), (Sat.Literal.pos 148)] :=
  (lex_9_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.pos 146), (Sat.Literal.neg 148)] :=
  (lex_9_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.neg 146), (Sat.Literal.neg 148), (Sat.Literal.pos 4035)] :=
  (lex_9_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4034), (Sat.Literal.pos 146), (Sat.Literal.pos 148), (Sat.Literal.pos 4035)] :=
  (lex_9_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4035) = lexBefore s permutation9 145 := by
  exact (positive_lex_of_descriptor s 4035 permutation9 146 (by rfl)).trans ((lex_skipped s permutation9 145 146 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation9 145) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation9 145 by rw [image9_eq]; rfl))

theorem lex_9_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4036) (Sat.Literal.pos 4035) (Sat.Literal.pos 145) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation9 145 (assignment s)
    (Sat.Literal.pos 4036) (Sat.Literal.pos 4035) (Sat.Literal.pos 145) (Sat.Literal.pos 140) (positive_of_descriptor s 4036 (.lex permutation9 145) (by rfl)) (lex_9_145_prefix s) (positive_select s 145) (lex_9_145_image s)

theorem lex_9_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.pos 145), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation9 145 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4035) (Sat.Literal.pos 145) (Sat.Literal.pos 140) (lex_9_145_prefix s) (positive_select s 145) (lex_9_145_image s)

theorem lex_9_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.pos 4035)] :=
  (lex_9_145_gate s).prop _ (List.Mem.head _)

theorem lex_9_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.neg 145), (Sat.Literal.pos 140)] :=
  (lex_9_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.pos 145), (Sat.Literal.neg 140)] :=
  (lex_9_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.neg 145), (Sat.Literal.neg 140), (Sat.Literal.pos 4036)] :=
  (lex_9_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4035), (Sat.Literal.pos 145), (Sat.Literal.pos 140), (Sat.Literal.pos 4036)] :=
  (lex_9_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4036) = lexBefore s permutation9 144 := by
  exact (positive_lex_of_descriptor s 4036 permutation9 145 (by rfl)).trans ((lex_skipped s permutation9 144 145 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation9 144) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation9 144 by rw [image9_eq]; rfl))

theorem lex_9_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4037) (Sat.Literal.pos 4036) (Sat.Literal.pos 144) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation9 144 (assignment s)
    (Sat.Literal.pos 4037) (Sat.Literal.pos 4036) (Sat.Literal.pos 144) (Sat.Literal.pos 132) (positive_of_descriptor s 4037 (.lex permutation9 144) (by rfl)) (lex_9_144_prefix s) (positive_select s 144) (lex_9_144_image s)

theorem lex_9_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.pos 144), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation9 144 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4036) (Sat.Literal.pos 144) (Sat.Literal.pos 132) (lex_9_144_prefix s) (positive_select s 144) (lex_9_144_image s)

theorem lex_9_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.pos 4036)] :=
  (lex_9_144_gate s).prop _ (List.Mem.head _)

theorem lex_9_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.neg 144), (Sat.Literal.pos 132)] :=
  (lex_9_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.pos 144), (Sat.Literal.neg 132)] :=
  (lex_9_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.neg 144), (Sat.Literal.neg 132), (Sat.Literal.pos 4037)] :=
  (lex_9_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4036), (Sat.Literal.pos 144), (Sat.Literal.pos 132), (Sat.Literal.pos 4037)] :=
  (lex_9_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4037) = lexBefore s permutation9 143 := by
  exact (positive_lex_of_descriptor s 4037 permutation9 144 (by rfl)).trans ((lex_skipped s permutation9 143 144 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation9 143) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation9 143 by rw [image9_eq]; rfl))

theorem lex_9_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4038) (Sat.Literal.pos 4037) (Sat.Literal.pos 143) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation9 143 (assignment s)
    (Sat.Literal.pos 4038) (Sat.Literal.pos 4037) (Sat.Literal.pos 143) (Sat.Literal.pos 124) (positive_of_descriptor s 4038 (.lex permutation9 143) (by rfl)) (lex_9_143_prefix s) (positive_select s 143) (lex_9_143_image s)

theorem lex_9_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.pos 143), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation9 143 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4037) (Sat.Literal.pos 143) (Sat.Literal.pos 124) (lex_9_143_prefix s) (positive_select s 143) (lex_9_143_image s)

theorem lex_9_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.pos 4037)] :=
  (lex_9_143_gate s).prop _ (List.Mem.head _)

theorem lex_9_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.neg 143), (Sat.Literal.pos 124)] :=
  (lex_9_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.pos 143), (Sat.Literal.neg 124)] :=
  (lex_9_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.neg 143), (Sat.Literal.neg 124), (Sat.Literal.pos 4038)] :=
  (lex_9_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4037), (Sat.Literal.pos 143), (Sat.Literal.pos 124), (Sat.Literal.pos 4038)] :=
  (lex_9_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4038) = lexBefore s permutation9 142 := by
  exact (positive_lex_of_descriptor s 4038 permutation9 143 (by rfl)).trans ((lex_skipped s permutation9 142 143 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation9 142) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation9 142 by rw [image9_eq]; rfl))

theorem lex_9_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4039) (Sat.Literal.pos 4038) (Sat.Literal.pos 142) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation9 142 (assignment s)
    (Sat.Literal.pos 4039) (Sat.Literal.pos 4038) (Sat.Literal.pos 142) (Sat.Literal.pos 116) (positive_of_descriptor s 4039 (.lex permutation9 142) (by rfl)) (lex_9_142_prefix s) (positive_select s 142) (lex_9_142_image s)

theorem lex_9_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.pos 142), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation9 142 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4038) (Sat.Literal.pos 142) (Sat.Literal.pos 116) (lex_9_142_prefix s) (positive_select s 142) (lex_9_142_image s)

theorem lex_9_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.pos 4038)] :=
  (lex_9_142_gate s).prop _ (List.Mem.head _)

theorem lex_9_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.neg 142), (Sat.Literal.pos 116)] :=
  (lex_9_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.pos 142), (Sat.Literal.neg 116)] :=
  (lex_9_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.neg 142), (Sat.Literal.neg 116), (Sat.Literal.pos 4039)] :=
  (lex_9_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4038), (Sat.Literal.pos 142), (Sat.Literal.pos 116), (Sat.Literal.pos 4039)] :=
  (lex_9_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4039) = lexBefore s permutation9 141 := by
  exact (positive_lex_of_descriptor s 4039 permutation9 142 (by rfl)).trans ((lex_skipped s permutation9 141 142 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation9 141) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation9 141 by rw [image9_eq]; rfl))

theorem lex_9_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4040) (Sat.Literal.pos 4039) (Sat.Literal.pos 141) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation9 141 (assignment s)
    (Sat.Literal.pos 4040) (Sat.Literal.pos 4039) (Sat.Literal.pos 141) (Sat.Literal.pos 108) (positive_of_descriptor s 4040 (.lex permutation9 141) (by rfl)) (lex_9_141_prefix s) (positive_select s 141) (lex_9_141_image s)

theorem lex_9_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.pos 141), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation9 141 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4039) (Sat.Literal.pos 141) (Sat.Literal.pos 108) (lex_9_141_prefix s) (positive_select s 141) (lex_9_141_image s)

theorem lex_9_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.pos 4039)] :=
  (lex_9_141_gate s).prop _ (List.Mem.head _)

theorem lex_9_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.neg 141), (Sat.Literal.pos 108)] :=
  (lex_9_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.pos 141), (Sat.Literal.neg 108)] :=
  (lex_9_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.neg 141), (Sat.Literal.neg 108), (Sat.Literal.pos 4040)] :=
  (lex_9_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4039), (Sat.Literal.pos 141), (Sat.Literal.pos 108), (Sat.Literal.pos 4040)] :=
  (lex_9_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4040) = lexBefore s permutation9 140 := by
  exact (positive_lex_of_descriptor s 4040 permutation9 141 (by rfl)).trans ((lex_skipped s permutation9 140 141 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation9 140) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation9 140 by rw [image9_eq]; rfl))

theorem lex_9_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4041) (Sat.Literal.pos 4040) (Sat.Literal.pos 140) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation9 140 (assignment s)
    (Sat.Literal.pos 4041) (Sat.Literal.pos 4040) (Sat.Literal.pos 140) (Sat.Literal.pos 100) (positive_of_descriptor s 4041 (.lex permutation9 140) (by rfl)) (lex_9_140_prefix s) (positive_select s 140) (lex_9_140_image s)

theorem lex_9_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.pos 140), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation9 140 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4040) (Sat.Literal.pos 140) (Sat.Literal.pos 100) (lex_9_140_prefix s) (positive_select s 140) (lex_9_140_image s)

theorem lex_9_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.pos 4040)] :=
  (lex_9_140_gate s).prop _ (List.Mem.head _)

theorem lex_9_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.neg 140), (Sat.Literal.pos 100)] :=
  (lex_9_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.pos 140), (Sat.Literal.neg 100)] :=
  (lex_9_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.neg 140), (Sat.Literal.neg 100), (Sat.Literal.pos 4041)] :=
  (lex_9_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4040), (Sat.Literal.pos 140), (Sat.Literal.pos 100), (Sat.Literal.pos 4041)] :=
  (lex_9_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4041) = lexBefore s permutation9 139 := by
  exact (positive_lex_of_descriptor s 4041 permutation9 140 (by rfl)).trans ((lex_skipped s permutation9 139 140 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation9 139) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation9 139 by rw [image9_eq]; rfl))

theorem lex_9_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4042) (Sat.Literal.pos 4041) (Sat.Literal.pos 139) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation9 139 (assignment s)
    (Sat.Literal.pos 4042) (Sat.Literal.pos 4041) (Sat.Literal.pos 139) (Sat.Literal.pos 92) (positive_of_descriptor s 4042 (.lex permutation9 139) (by rfl)) (lex_9_139_prefix s) (positive_select s 139) (lex_9_139_image s)

theorem lex_9_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.pos 139), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation9 139 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4041) (Sat.Literal.pos 139) (Sat.Literal.pos 92) (lex_9_139_prefix s) (positive_select s 139) (lex_9_139_image s)

theorem lex_9_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.pos 4041)] :=
  (lex_9_139_gate s).prop _ (List.Mem.head _)

theorem lex_9_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.neg 139), (Sat.Literal.pos 92)] :=
  (lex_9_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.pos 139), (Sat.Literal.neg 92)] :=
  (lex_9_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.neg 139), (Sat.Literal.neg 92), (Sat.Literal.pos 4042)] :=
  (lex_9_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4041), (Sat.Literal.pos 139), (Sat.Literal.pos 92), (Sat.Literal.pos 4042)] :=
  (lex_9_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4042) = lexBefore s permutation9 138 := by
  exact (positive_lex_of_descriptor s 4042 permutation9 139 (by rfl)).trans ((lex_skipped s permutation9 138 139 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation9 138) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation9 138 by rw [image9_eq]; rfl))

theorem lex_9_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4043) (Sat.Literal.pos 4042) (Sat.Literal.pos 138) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation9 138 (assignment s)
    (Sat.Literal.pos 4043) (Sat.Literal.pos 4042) (Sat.Literal.pos 138) (Sat.Literal.pos 84) (positive_of_descriptor s 4043 (.lex permutation9 138) (by rfl)) (lex_9_138_prefix s) (positive_select s 138) (lex_9_138_image s)

theorem lex_9_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.pos 138), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation9 138 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4042) (Sat.Literal.pos 138) (Sat.Literal.pos 84) (lex_9_138_prefix s) (positive_select s 138) (lex_9_138_image s)

theorem lex_9_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.pos 4042)] :=
  (lex_9_138_gate s).prop _ (List.Mem.head _)

theorem lex_9_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.neg 138), (Sat.Literal.pos 84)] :=
  (lex_9_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.pos 138), (Sat.Literal.neg 84)] :=
  (lex_9_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.neg 138), (Sat.Literal.neg 84), (Sat.Literal.pos 4043)] :=
  (lex_9_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4042), (Sat.Literal.pos 138), (Sat.Literal.pos 84), (Sat.Literal.pos 4043)] :=
  (lex_9_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4043) = lexBefore s permutation9 137 := by
  exact (positive_lex_of_descriptor s 4043 permutation9 138 (by rfl)).trans ((lex_skipped s permutation9 137 138 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation9 137) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation9 137 by rw [image9_eq]; rfl))

theorem lex_9_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4044) (Sat.Literal.pos 4043) (Sat.Literal.pos 137) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation9 137 (assignment s)
    (Sat.Literal.pos 4044) (Sat.Literal.pos 4043) (Sat.Literal.pos 137) (Sat.Literal.pos 76) (positive_of_descriptor s 4044 (.lex permutation9 137) (by rfl)) (lex_9_137_prefix s) (positive_select s 137) (lex_9_137_image s)

theorem lex_9_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.pos 137), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation9 137 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4043) (Sat.Literal.pos 137) (Sat.Literal.pos 76) (lex_9_137_prefix s) (positive_select s 137) (lex_9_137_image s)

theorem lex_9_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.pos 4043)] :=
  (lex_9_137_gate s).prop _ (List.Mem.head _)

theorem lex_9_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.neg 137), (Sat.Literal.pos 76)] :=
  (lex_9_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.pos 137), (Sat.Literal.neg 76)] :=
  (lex_9_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.neg 137), (Sat.Literal.neg 76), (Sat.Literal.pos 4044)] :=
  (lex_9_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4043), (Sat.Literal.pos 137), (Sat.Literal.pos 76), (Sat.Literal.pos 4044)] :=
  (lex_9_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4044) = lexBefore s permutation9 136 := by
  exact (positive_lex_of_descriptor s 4044 permutation9 137 (by rfl)).trans ((lex_skipped s permutation9 136 137 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation9 136) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation9 136 by rw [image9_eq]; rfl))

theorem lex_9_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4045) (Sat.Literal.pos 4044) (Sat.Literal.pos 136) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation9 136 (assignment s)
    (Sat.Literal.pos 4045) (Sat.Literal.pos 4044) (Sat.Literal.pos 136) (Sat.Literal.pos 68) (positive_of_descriptor s 4045 (.lex permutation9 136) (by rfl)) (lex_9_136_prefix s) (positive_select s 136) (lex_9_136_image s)

theorem lex_9_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.pos 136), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation9 136 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4044) (Sat.Literal.pos 136) (Sat.Literal.pos 68) (lex_9_136_prefix s) (positive_select s 136) (lex_9_136_image s)

theorem lex_9_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.pos 4044)] :=
  (lex_9_136_gate s).prop _ (List.Mem.head _)

theorem lex_9_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.neg 136), (Sat.Literal.pos 68)] :=
  (lex_9_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.pos 136), (Sat.Literal.neg 68)] :=
  (lex_9_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.neg 136), (Sat.Literal.neg 68), (Sat.Literal.pos 4045)] :=
  (lex_9_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4044), (Sat.Literal.pos 136), (Sat.Literal.pos 68), (Sat.Literal.pos 4045)] :=
  (lex_9_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4045) = lexBefore s permutation9 135 := by
  exact (positive_lex_of_descriptor s 4045 permutation9 136 (by rfl)).trans ((lex_skipped s permutation9 135 136 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation9 135) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation9 135 by rw [image9_eq]; rfl))

theorem lex_9_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4046) (Sat.Literal.pos 4045) (Sat.Literal.pos 135) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation9 135 (assignment s)
    (Sat.Literal.pos 4046) (Sat.Literal.pos 4045) (Sat.Literal.pos 135) (Sat.Literal.pos 60) (positive_of_descriptor s 4046 (.lex permutation9 135) (by rfl)) (lex_9_135_prefix s) (positive_select s 135) (lex_9_135_image s)

theorem lex_9_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.pos 135), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation9 135 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4045) (Sat.Literal.pos 135) (Sat.Literal.pos 60) (lex_9_135_prefix s) (positive_select s 135) (lex_9_135_image s)

theorem lex_9_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.pos 4045)] :=
  (lex_9_135_gate s).prop _ (List.Mem.head _)

theorem lex_9_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.neg 135), (Sat.Literal.pos 60)] :=
  (lex_9_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.pos 135), (Sat.Literal.neg 60)] :=
  (lex_9_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.neg 135), (Sat.Literal.neg 60), (Sat.Literal.pos 4046)] :=
  (lex_9_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4045), (Sat.Literal.pos 135), (Sat.Literal.pos 60), (Sat.Literal.pos 4046)] :=
  (lex_9_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4046) = lexBefore s permutation9 134 := by
  exact (positive_lex_of_descriptor s 4046 permutation9 135 (by rfl)).trans ((lex_skipped s permutation9 134 135 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation9 134) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation9 134 by rw [image9_eq]; rfl))

theorem lex_9_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4047) (Sat.Literal.pos 4046) (Sat.Literal.pos 134) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation9 134 (assignment s)
    (Sat.Literal.pos 4047) (Sat.Literal.pos 4046) (Sat.Literal.pos 134) (Sat.Literal.pos 52) (positive_of_descriptor s 4047 (.lex permutation9 134) (by rfl)) (lex_9_134_prefix s) (positive_select s 134) (lex_9_134_image s)

theorem lex_9_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.pos 134), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation9 134 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4046) (Sat.Literal.pos 134) (Sat.Literal.pos 52) (lex_9_134_prefix s) (positive_select s 134) (lex_9_134_image s)

theorem lex_9_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.pos 4046)] :=
  (lex_9_134_gate s).prop _ (List.Mem.head _)

theorem lex_9_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.neg 134), (Sat.Literal.pos 52)] :=
  (lex_9_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.pos 134), (Sat.Literal.neg 52)] :=
  (lex_9_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.neg 134), (Sat.Literal.neg 52), (Sat.Literal.pos 4047)] :=
  (lex_9_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4046), (Sat.Literal.pos 134), (Sat.Literal.pos 52), (Sat.Literal.pos 4047)] :=
  (lex_9_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4047) = lexBefore s permutation9 133 := by
  exact (positive_lex_of_descriptor s 4047 permutation9 134 (by rfl)).trans ((lex_skipped s permutation9 133 134 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation9 133) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation9 133 by rw [image9_eq]; rfl))

theorem lex_9_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4048) (Sat.Literal.pos 4047) (Sat.Literal.pos 133) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation9 133 (assignment s)
    (Sat.Literal.pos 4048) (Sat.Literal.pos 4047) (Sat.Literal.pos 133) (Sat.Literal.pos 44) (positive_of_descriptor s 4048 (.lex permutation9 133) (by rfl)) (lex_9_133_prefix s) (positive_select s 133) (lex_9_133_image s)

theorem lex_9_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.pos 133), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation9 133 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4047) (Sat.Literal.pos 133) (Sat.Literal.pos 44) (lex_9_133_prefix s) (positive_select s 133) (lex_9_133_image s)

theorem lex_9_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.pos 4047)] :=
  (lex_9_133_gate s).prop _ (List.Mem.head _)

theorem lex_9_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.neg 133), (Sat.Literal.pos 44)] :=
  (lex_9_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.pos 133), (Sat.Literal.neg 44)] :=
  (lex_9_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.neg 133), (Sat.Literal.neg 44), (Sat.Literal.pos 4048)] :=
  (lex_9_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4047), (Sat.Literal.pos 133), (Sat.Literal.pos 44), (Sat.Literal.pos 4048)] :=
  (lex_9_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4048) = lexBefore s permutation9 132 := by
  exact (positive_lex_of_descriptor s 4048 permutation9 133 (by rfl)).trans ((lex_skipped s permutation9 132 133 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation9 132) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation9 132 by rw [image9_eq]; rfl))

theorem lex_9_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4049) (Sat.Literal.pos 4048) (Sat.Literal.pos 132) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation9 132 (assignment s)
    (Sat.Literal.pos 4049) (Sat.Literal.pos 4048) (Sat.Literal.pos 132) (Sat.Literal.pos 36) (positive_of_descriptor s 4049 (.lex permutation9 132) (by rfl)) (lex_9_132_prefix s) (positive_select s 132) (lex_9_132_image s)

theorem lex_9_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.pos 132), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation9 132 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4048) (Sat.Literal.pos 132) (Sat.Literal.pos 36) (lex_9_132_prefix s) (positive_select s 132) (lex_9_132_image s)

theorem lex_9_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.pos 4048)] :=
  (lex_9_132_gate s).prop _ (List.Mem.head _)

theorem lex_9_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.neg 132), (Sat.Literal.pos 36)] :=
  (lex_9_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.pos 132), (Sat.Literal.neg 36)] :=
  (lex_9_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.neg 132), (Sat.Literal.neg 36), (Sat.Literal.pos 4049)] :=
  (lex_9_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4048), (Sat.Literal.pos 132), (Sat.Literal.pos 36), (Sat.Literal.pos 4049)] :=
  (lex_9_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4049) = lexBefore s permutation9 131 := by
  exact (positive_lex_of_descriptor s 4049 permutation9 132 (by rfl)).trans ((lex_skipped s permutation9 131 132 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation9 131) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation9 131 by rw [image9_eq]; rfl))

theorem lex_9_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4050) (Sat.Literal.pos 4049) (Sat.Literal.pos 131) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation9 131 (assignment s)
    (Sat.Literal.pos 4050) (Sat.Literal.pos 4049) (Sat.Literal.pos 131) (Sat.Literal.pos 28) (positive_of_descriptor s 4050 (.lex permutation9 131) (by rfl)) (lex_9_131_prefix s) (positive_select s 131) (lex_9_131_image s)

theorem lex_9_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.pos 131), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation9 131 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4049) (Sat.Literal.pos 131) (Sat.Literal.pos 28) (lex_9_131_prefix s) (positive_select s 131) (lex_9_131_image s)

theorem lex_9_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.pos 4049)] :=
  (lex_9_131_gate s).prop _ (List.Mem.head _)

theorem lex_9_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.neg 131), (Sat.Literal.pos 28)] :=
  (lex_9_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.pos 131), (Sat.Literal.neg 28)] :=
  (lex_9_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.neg 131), (Sat.Literal.neg 28), (Sat.Literal.pos 4050)] :=
  (lex_9_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4049), (Sat.Literal.pos 131), (Sat.Literal.pos 28), (Sat.Literal.pos 4050)] :=
  (lex_9_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4050) = lexBefore s permutation9 130 := by
  exact (positive_lex_of_descriptor s 4050 permutation9 131 (by rfl)).trans ((lex_skipped s permutation9 130 131 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation9 130) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation9 130 by rw [image9_eq]; rfl))

theorem lex_9_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4051) (Sat.Literal.pos 4050) (Sat.Literal.pos 130) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation9 130 (assignment s)
    (Sat.Literal.pos 4051) (Sat.Literal.pos 4050) (Sat.Literal.pos 130) (Sat.Literal.pos 20) (positive_of_descriptor s 4051 (.lex permutation9 130) (by rfl)) (lex_9_130_prefix s) (positive_select s 130) (lex_9_130_image s)

theorem lex_9_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.pos 130), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation9 130 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4050) (Sat.Literal.pos 130) (Sat.Literal.pos 20) (lex_9_130_prefix s) (positive_select s 130) (lex_9_130_image s)

theorem lex_9_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.pos 4050)] :=
  (lex_9_130_gate s).prop _ (List.Mem.head _)

theorem lex_9_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.neg 130), (Sat.Literal.pos 20)] :=
  (lex_9_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.pos 130), (Sat.Literal.neg 20)] :=
  (lex_9_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.neg 130), (Sat.Literal.neg 20), (Sat.Literal.pos 4051)] :=
  (lex_9_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4050), (Sat.Literal.pos 130), (Sat.Literal.pos 20), (Sat.Literal.pos 4051)] :=
  (lex_9_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4051) = lexBefore s permutation9 129 := by
  exact (positive_lex_of_descriptor s 4051 permutation9 130 (by rfl)).trans ((lex_skipped s permutation9 129 130 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation9 129) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation9 129 by rw [image9_eq]; rfl))

theorem lex_9_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4052) (Sat.Literal.pos 4051) (Sat.Literal.pos 129) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation9 129 (assignment s)
    (Sat.Literal.pos 4052) (Sat.Literal.pos 4051) (Sat.Literal.pos 129) (Sat.Literal.pos 12) (positive_of_descriptor s 4052 (.lex permutation9 129) (by rfl)) (lex_9_129_prefix s) (positive_select s 129) (lex_9_129_image s)

theorem lex_9_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.pos 129), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation9 129 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4051) (Sat.Literal.pos 129) (Sat.Literal.pos 12) (lex_9_129_prefix s) (positive_select s 129) (lex_9_129_image s)

theorem lex_9_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.pos 4051)] :=
  (lex_9_129_gate s).prop _ (List.Mem.head _)

theorem lex_9_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.neg 129), (Sat.Literal.pos 12)] :=
  (lex_9_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.pos 129), (Sat.Literal.neg 12)] :=
  (lex_9_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.neg 129), (Sat.Literal.neg 12), (Sat.Literal.pos 4052)] :=
  (lex_9_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4051), (Sat.Literal.pos 129), (Sat.Literal.pos 12), (Sat.Literal.pos 4052)] :=
  (lex_9_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4052) = lexBefore s permutation9 128 := by
  exact (positive_lex_of_descriptor s 4052 permutation9 129 (by rfl)).trans ((lex_skipped s permutation9 128 129 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation9 128) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation9 128 by rw [image9_eq]; rfl))

theorem lex_9_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4053) (Sat.Literal.pos 4052) (Sat.Literal.pos 128) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation9 128 (assignment s)
    (Sat.Literal.pos 4053) (Sat.Literal.pos 4052) (Sat.Literal.pos 128) (Sat.Literal.pos 4) (positive_of_descriptor s 4053 (.lex permutation9 128) (by rfl)) (lex_9_128_prefix s) (positive_select s 128) (lex_9_128_image s)

theorem lex_9_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.pos 128), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation9 128 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4052) (Sat.Literal.pos 128) (Sat.Literal.pos 4) (lex_9_128_prefix s) (positive_select s 128) (lex_9_128_image s)

theorem lex_9_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.pos 4052)] :=
  (lex_9_128_gate s).prop _ (List.Mem.head _)

theorem lex_9_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.neg 128), (Sat.Literal.pos 4)] :=
  (lex_9_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.pos 128), (Sat.Literal.neg 4)] :=
  (lex_9_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.neg 128), (Sat.Literal.neg 4), (Sat.Literal.pos 4053)] :=
  (lex_9_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4052), (Sat.Literal.pos 128), (Sat.Literal.pos 4), (Sat.Literal.pos 4053)] :=
  (lex_9_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4053) = lexBefore s permutation9 127 := by
  exact (positive_lex_of_descriptor s 4053 permutation9 128 (by rfl)).trans ((lex_skipped s permutation9 127 128 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation9 127) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation9 127 by rw [image9_eq]; rfl))

theorem lex_9_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4054) (Sat.Literal.pos 4053) (Sat.Literal.pos 127) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation9 127 (assignment s)
    (Sat.Literal.pos 4054) (Sat.Literal.pos 4053) (Sat.Literal.pos 127) (Sat.Literal.pos 251) (positive_of_descriptor s 4054 (.lex permutation9 127) (by rfl)) (lex_9_127_prefix s) (positive_select s 127) (lex_9_127_image s)

theorem lex_9_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.pos 127), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation9 127 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4053) (Sat.Literal.pos 127) (Sat.Literal.pos 251) (lex_9_127_prefix s) (positive_select s 127) (lex_9_127_image s)

theorem lex_9_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.pos 4053)] :=
  (lex_9_127_gate s).prop _ (List.Mem.head _)

theorem lex_9_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.neg 127), (Sat.Literal.pos 251)] :=
  (lex_9_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.pos 127), (Sat.Literal.neg 251)] :=
  (lex_9_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.neg 127), (Sat.Literal.neg 251), (Sat.Literal.pos 4054)] :=
  (lex_9_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4053), (Sat.Literal.pos 127), (Sat.Literal.pos 251), (Sat.Literal.pos 4054)] :=
  (lex_9_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4054) = lexBefore s permutation9 126 := by
  exact (positive_lex_of_descriptor s 4054 permutation9 127 (by rfl)).trans ((lex_skipped s permutation9 126 127 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation9 126) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation9 126 by rw [image9_eq]; rfl))

theorem lex_9_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4055) (Sat.Literal.pos 4054) (Sat.Literal.pos 126) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation9 126 (assignment s)
    (Sat.Literal.pos 4055) (Sat.Literal.pos 4054) (Sat.Literal.pos 126) (Sat.Literal.pos 243) (positive_of_descriptor s 4055 (.lex permutation9 126) (by rfl)) (lex_9_126_prefix s) (positive_select s 126) (lex_9_126_image s)

theorem lex_9_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.pos 126), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation9 126 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4054) (Sat.Literal.pos 126) (Sat.Literal.pos 243) (lex_9_126_prefix s) (positive_select s 126) (lex_9_126_image s)

theorem lex_9_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.pos 4054)] :=
  (lex_9_126_gate s).prop _ (List.Mem.head _)

theorem lex_9_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.neg 126), (Sat.Literal.pos 243)] :=
  (lex_9_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.pos 126), (Sat.Literal.neg 243)] :=
  (lex_9_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.neg 126), (Sat.Literal.neg 243), (Sat.Literal.pos 4055)] :=
  (lex_9_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4054), (Sat.Literal.pos 126), (Sat.Literal.pos 243), (Sat.Literal.pos 4055)] :=
  (lex_9_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4055) = lexBefore s permutation9 125 := by
  exact (positive_lex_of_descriptor s 4055 permutation9 126 (by rfl)).trans ((lex_skipped s permutation9 125 126 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation9 125) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation9 125 by rw [image9_eq]; rfl))

theorem lex_9_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4056) (Sat.Literal.pos 4055) (Sat.Literal.pos 125) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation9 125 (assignment s)
    (Sat.Literal.pos 4056) (Sat.Literal.pos 4055) (Sat.Literal.pos 125) (Sat.Literal.pos 235) (positive_of_descriptor s 4056 (.lex permutation9 125) (by rfl)) (lex_9_125_prefix s) (positive_select s 125) (lex_9_125_image s)

theorem lex_9_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.pos 125), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation9 125 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4055) (Sat.Literal.pos 125) (Sat.Literal.pos 235) (lex_9_125_prefix s) (positive_select s 125) (lex_9_125_image s)

theorem lex_9_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.pos 4055)] :=
  (lex_9_125_gate s).prop _ (List.Mem.head _)

theorem lex_9_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.neg 125), (Sat.Literal.pos 235)] :=
  (lex_9_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.pos 125), (Sat.Literal.neg 235)] :=
  (lex_9_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.neg 125), (Sat.Literal.neg 235), (Sat.Literal.pos 4056)] :=
  (lex_9_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4055), (Sat.Literal.pos 125), (Sat.Literal.pos 235), (Sat.Literal.pos 4056)] :=
  (lex_9_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4056) = lexBefore s permutation9 124 := by
  exact (positive_lex_of_descriptor s 4056 permutation9 125 (by rfl)).trans ((lex_skipped s permutation9 124 125 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation9 124) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation9 124 by rw [image9_eq]; rfl))

theorem lex_9_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4057) (Sat.Literal.pos 4056) (Sat.Literal.pos 124) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation9 124 (assignment s)
    (Sat.Literal.pos 4057) (Sat.Literal.pos 4056) (Sat.Literal.pos 124) (Sat.Literal.pos 227) (positive_of_descriptor s 4057 (.lex permutation9 124) (by rfl)) (lex_9_124_prefix s) (positive_select s 124) (lex_9_124_image s)

theorem lex_9_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.pos 124), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation9 124 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4056) (Sat.Literal.pos 124) (Sat.Literal.pos 227) (lex_9_124_prefix s) (positive_select s 124) (lex_9_124_image s)

theorem lex_9_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.pos 4056)] :=
  (lex_9_124_gate s).prop _ (List.Mem.head _)

theorem lex_9_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.neg 124), (Sat.Literal.pos 227)] :=
  (lex_9_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.pos 124), (Sat.Literal.neg 227)] :=
  (lex_9_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.neg 124), (Sat.Literal.neg 227), (Sat.Literal.pos 4057)] :=
  (lex_9_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4056), (Sat.Literal.pos 124), (Sat.Literal.pos 227), (Sat.Literal.pos 4057)] :=
  (lex_9_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4057) = lexBefore s permutation9 123 := by
  exact (positive_lex_of_descriptor s 4057 permutation9 124 (by rfl)).trans ((lex_skipped s permutation9 123 124 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation9 123) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation9 123 by rw [image9_eq]; rfl))

theorem lex_9_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4058) (Sat.Literal.pos 4057) (Sat.Literal.pos 123) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation9 123 (assignment s)
    (Sat.Literal.pos 4058) (Sat.Literal.pos 4057) (Sat.Literal.pos 123) (Sat.Literal.pos 219) (positive_of_descriptor s 4058 (.lex permutation9 123) (by rfl)) (lex_9_123_prefix s) (positive_select s 123) (lex_9_123_image s)

theorem lex_9_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.pos 123), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation9 123 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4057) (Sat.Literal.pos 123) (Sat.Literal.pos 219) (lex_9_123_prefix s) (positive_select s 123) (lex_9_123_image s)

theorem lex_9_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.pos 4057)] :=
  (lex_9_123_gate s).prop _ (List.Mem.head _)

theorem lex_9_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.neg 123), (Sat.Literal.pos 219)] :=
  (lex_9_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.pos 123), (Sat.Literal.neg 219)] :=
  (lex_9_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.neg 123), (Sat.Literal.neg 219), (Sat.Literal.pos 4058)] :=
  (lex_9_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4057), (Sat.Literal.pos 123), (Sat.Literal.pos 219), (Sat.Literal.pos 4058)] :=
  (lex_9_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4058) = lexBefore s permutation9 122 := by
  exact (positive_lex_of_descriptor s 4058 permutation9 123 (by rfl)).trans ((lex_skipped s permutation9 122 123 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation9 122) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation9 122 by rw [image9_eq]; rfl))

theorem lex_9_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4059) (Sat.Literal.pos 4058) (Sat.Literal.pos 122) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation9 122 (assignment s)
    (Sat.Literal.pos 4059) (Sat.Literal.pos 4058) (Sat.Literal.pos 122) (Sat.Literal.pos 211) (positive_of_descriptor s 4059 (.lex permutation9 122) (by rfl)) (lex_9_122_prefix s) (positive_select s 122) (lex_9_122_image s)

theorem lex_9_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.pos 122), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation9 122 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4058) (Sat.Literal.pos 122) (Sat.Literal.pos 211) (lex_9_122_prefix s) (positive_select s 122) (lex_9_122_image s)

theorem lex_9_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.pos 4058)] :=
  (lex_9_122_gate s).prop _ (List.Mem.head _)

theorem lex_9_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.neg 122), (Sat.Literal.pos 211)] :=
  (lex_9_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.pos 122), (Sat.Literal.neg 211)] :=
  (lex_9_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.neg 122), (Sat.Literal.neg 211), (Sat.Literal.pos 4059)] :=
  (lex_9_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4058), (Sat.Literal.pos 122), (Sat.Literal.pos 211), (Sat.Literal.pos 4059)] :=
  (lex_9_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4059) = lexBefore s permutation9 121 := by
  exact (positive_lex_of_descriptor s 4059 permutation9 122 (by rfl)).trans ((lex_skipped s permutation9 121 122 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation9 121) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation9 121 by rw [image9_eq]; rfl))

theorem lex_9_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4060) (Sat.Literal.pos 4059) (Sat.Literal.pos 121) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation9 121 (assignment s)
    (Sat.Literal.pos 4060) (Sat.Literal.pos 4059) (Sat.Literal.pos 121) (Sat.Literal.pos 203) (positive_of_descriptor s 4060 (.lex permutation9 121) (by rfl)) (lex_9_121_prefix s) (positive_select s 121) (lex_9_121_image s)

theorem lex_9_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.pos 121), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation9 121 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4059) (Sat.Literal.pos 121) (Sat.Literal.pos 203) (lex_9_121_prefix s) (positive_select s 121) (lex_9_121_image s)

theorem lex_9_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.pos 4059)] :=
  (lex_9_121_gate s).prop _ (List.Mem.head _)

theorem lex_9_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.neg 121), (Sat.Literal.pos 203)] :=
  (lex_9_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.pos 121), (Sat.Literal.neg 203)] :=
  (lex_9_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.neg 121), (Sat.Literal.neg 203), (Sat.Literal.pos 4060)] :=
  (lex_9_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4059), (Sat.Literal.pos 121), (Sat.Literal.pos 203), (Sat.Literal.pos 4060)] :=
  (lex_9_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4060) = lexBefore s permutation9 120 := by
  exact (positive_lex_of_descriptor s 4060 permutation9 121 (by rfl)).trans ((lex_skipped s permutation9 120 121 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation9 120) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation9 120 by rw [image9_eq]; rfl))

theorem lex_9_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4061) (Sat.Literal.pos 4060) (Sat.Literal.pos 120) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation9 120 (assignment s)
    (Sat.Literal.pos 4061) (Sat.Literal.pos 4060) (Sat.Literal.pos 120) (Sat.Literal.pos 195) (positive_of_descriptor s 4061 (.lex permutation9 120) (by rfl)) (lex_9_120_prefix s) (positive_select s 120) (lex_9_120_image s)

theorem lex_9_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.pos 120), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation9 120 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4060) (Sat.Literal.pos 120) (Sat.Literal.pos 195) (lex_9_120_prefix s) (positive_select s 120) (lex_9_120_image s)

theorem lex_9_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.pos 4060)] :=
  (lex_9_120_gate s).prop _ (List.Mem.head _)

theorem lex_9_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.neg 120), (Sat.Literal.pos 195)] :=
  (lex_9_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.pos 120), (Sat.Literal.neg 195)] :=
  (lex_9_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.neg 120), (Sat.Literal.neg 195), (Sat.Literal.pos 4061)] :=
  (lex_9_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4060), (Sat.Literal.pos 120), (Sat.Literal.pos 195), (Sat.Literal.pos 4061)] :=
  (lex_9_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4061) = lexBefore s permutation9 119 := by
  exact (positive_lex_of_descriptor s 4061 permutation9 120 (by rfl)).trans ((lex_skipped s permutation9 119 120 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation9 119) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation9 119 by rw [image9_eq]; rfl))

theorem lex_9_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4062) (Sat.Literal.pos 4061) (Sat.Literal.pos 119) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation9 119 (assignment s)
    (Sat.Literal.pos 4062) (Sat.Literal.pos 4061) (Sat.Literal.pos 119) (Sat.Literal.pos 187) (positive_of_descriptor s 4062 (.lex permutation9 119) (by rfl)) (lex_9_119_prefix s) (positive_select s 119) (lex_9_119_image s)

theorem lex_9_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.pos 119), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation9 119 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4061) (Sat.Literal.pos 119) (Sat.Literal.pos 187) (lex_9_119_prefix s) (positive_select s 119) (lex_9_119_image s)

theorem lex_9_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.pos 4061)] :=
  (lex_9_119_gate s).prop _ (List.Mem.head _)

theorem lex_9_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.neg 119), (Sat.Literal.pos 187)] :=
  (lex_9_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.pos 119), (Sat.Literal.neg 187)] :=
  (lex_9_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.neg 119), (Sat.Literal.neg 187), (Sat.Literal.pos 4062)] :=
  (lex_9_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4061), (Sat.Literal.pos 119), (Sat.Literal.pos 187), (Sat.Literal.pos 4062)] :=
  (lex_9_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4062) = lexBefore s permutation9 118 := by
  exact (positive_lex_of_descriptor s 4062 permutation9 119 (by rfl)).trans ((lex_skipped s permutation9 118 119 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation9 118) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation9 118 by rw [image9_eq]; rfl))

theorem lex_9_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4063) (Sat.Literal.pos 4062) (Sat.Literal.pos 118) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation9 118 (assignment s)
    (Sat.Literal.pos 4063) (Sat.Literal.pos 4062) (Sat.Literal.pos 118) (Sat.Literal.pos 179) (positive_of_descriptor s 4063 (.lex permutation9 118) (by rfl)) (lex_9_118_prefix s) (positive_select s 118) (lex_9_118_image s)

theorem lex_9_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.pos 118), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation9 118 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4062) (Sat.Literal.pos 118) (Sat.Literal.pos 179) (lex_9_118_prefix s) (positive_select s 118) (lex_9_118_image s)

theorem lex_9_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.pos 4062)] :=
  (lex_9_118_gate s).prop _ (List.Mem.head _)

theorem lex_9_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.neg 118), (Sat.Literal.pos 179)] :=
  (lex_9_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.pos 118), (Sat.Literal.neg 179)] :=
  (lex_9_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.neg 118), (Sat.Literal.neg 179), (Sat.Literal.pos 4063)] :=
  (lex_9_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4062), (Sat.Literal.pos 118), (Sat.Literal.pos 179), (Sat.Literal.pos 4063)] :=
  (lex_9_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4063) = lexBefore s permutation9 117 := by
  exact (positive_lex_of_descriptor s 4063 permutation9 118 (by rfl)).trans ((lex_skipped s permutation9 117 118 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation9 117) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation9 117 by rw [image9_eq]; rfl))

theorem lex_9_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4064) (Sat.Literal.pos 4063) (Sat.Literal.pos 117) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation9 117 (assignment s)
    (Sat.Literal.pos 4064) (Sat.Literal.pos 4063) (Sat.Literal.pos 117) (Sat.Literal.pos 171) (positive_of_descriptor s 4064 (.lex permutation9 117) (by rfl)) (lex_9_117_prefix s) (positive_select s 117) (lex_9_117_image s)

theorem lex_9_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.pos 117), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation9 117 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4063) (Sat.Literal.pos 117) (Sat.Literal.pos 171) (lex_9_117_prefix s) (positive_select s 117) (lex_9_117_image s)

theorem lex_9_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.pos 4063)] :=
  (lex_9_117_gate s).prop _ (List.Mem.head _)

theorem lex_9_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.neg 117), (Sat.Literal.pos 171)] :=
  (lex_9_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.pos 117), (Sat.Literal.neg 171)] :=
  (lex_9_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.neg 117), (Sat.Literal.neg 171), (Sat.Literal.pos 4064)] :=
  (lex_9_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4063), (Sat.Literal.pos 117), (Sat.Literal.pos 171), (Sat.Literal.pos 4064)] :=
  (lex_9_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4064) = lexBefore s permutation9 116 := by
  exact (positive_lex_of_descriptor s 4064 permutation9 117 (by rfl)).trans ((lex_skipped s permutation9 116 117 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation9 116) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation9 116 by rw [image9_eq]; rfl))

theorem lex_9_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4065) (Sat.Literal.pos 4064) (Sat.Literal.pos 116) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation9 116 (assignment s)
    (Sat.Literal.pos 4065) (Sat.Literal.pos 4064) (Sat.Literal.pos 116) (Sat.Literal.pos 163) (positive_of_descriptor s 4065 (.lex permutation9 116) (by rfl)) (lex_9_116_prefix s) (positive_select s 116) (lex_9_116_image s)

theorem lex_9_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.pos 116), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation9 116 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4064) (Sat.Literal.pos 116) (Sat.Literal.pos 163) (lex_9_116_prefix s) (positive_select s 116) (lex_9_116_image s)

theorem lex_9_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.pos 4064)] :=
  (lex_9_116_gate s).prop _ (List.Mem.head _)

theorem lex_9_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.neg 116), (Sat.Literal.pos 163)] :=
  (lex_9_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.pos 116), (Sat.Literal.neg 163)] :=
  (lex_9_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.neg 116), (Sat.Literal.neg 163), (Sat.Literal.pos 4065)] :=
  (lex_9_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4064), (Sat.Literal.pos 116), (Sat.Literal.pos 163), (Sat.Literal.pos 4065)] :=
  (lex_9_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4065) = lexBefore s permutation9 115 := by
  exact (positive_lex_of_descriptor s 4065 permutation9 116 (by rfl)).trans ((lex_skipped s permutation9 115 116 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation9 115) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation9 115 by rw [image9_eq]; rfl))

theorem lex_9_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4066) (Sat.Literal.pos 4065) (Sat.Literal.pos 115) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation9 115 (assignment s)
    (Sat.Literal.pos 4066) (Sat.Literal.pos 4065) (Sat.Literal.pos 115) (Sat.Literal.pos 155) (positive_of_descriptor s 4066 (.lex permutation9 115) (by rfl)) (lex_9_115_prefix s) (positive_select s 115) (lex_9_115_image s)

theorem lex_9_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.pos 115), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation9 115 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4065) (Sat.Literal.pos 115) (Sat.Literal.pos 155) (lex_9_115_prefix s) (positive_select s 115) (lex_9_115_image s)

theorem lex_9_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.pos 4065)] :=
  (lex_9_115_gate s).prop _ (List.Mem.head _)

theorem lex_9_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.neg 115), (Sat.Literal.pos 155)] :=
  (lex_9_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.pos 115), (Sat.Literal.neg 155)] :=
  (lex_9_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.neg 115), (Sat.Literal.neg 155), (Sat.Literal.pos 4066)] :=
  (lex_9_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4065), (Sat.Literal.pos 115), (Sat.Literal.pos 155), (Sat.Literal.pos 4066)] :=
  (lex_9_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4066) = lexBefore s permutation9 114 := by
  exact (positive_lex_of_descriptor s 4066 permutation9 115 (by rfl)).trans ((lex_skipped s permutation9 114 115 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation9 114) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation9 114 by rw [image9_eq]; rfl))

theorem lex_9_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4067) (Sat.Literal.pos 4066) (Sat.Literal.pos 114) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation9 114 (assignment s)
    (Sat.Literal.pos 4067) (Sat.Literal.pos 4066) (Sat.Literal.pos 114) (Sat.Literal.pos 147) (positive_of_descriptor s 4067 (.lex permutation9 114) (by rfl)) (lex_9_114_prefix s) (positive_select s 114) (lex_9_114_image s)

theorem lex_9_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.pos 114), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation9 114 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4066) (Sat.Literal.pos 114) (Sat.Literal.pos 147) (lex_9_114_prefix s) (positive_select s 114) (lex_9_114_image s)

theorem lex_9_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.pos 4066)] :=
  (lex_9_114_gate s).prop _ (List.Mem.head _)

theorem lex_9_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.neg 114), (Sat.Literal.pos 147)] :=
  (lex_9_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.pos 114), (Sat.Literal.neg 147)] :=
  (lex_9_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.neg 114), (Sat.Literal.neg 147), (Sat.Literal.pos 4067)] :=
  (lex_9_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4066), (Sat.Literal.pos 114), (Sat.Literal.pos 147), (Sat.Literal.pos 4067)] :=
  (lex_9_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4067) = lexBefore s permutation9 113 := by
  exact (positive_lex_of_descriptor s 4067 permutation9 114 (by rfl)).trans ((lex_skipped s permutation9 113 114 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation9 113) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation9 113 by rw [image9_eq]; rfl))

theorem lex_9_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4068) (Sat.Literal.pos 4067) (Sat.Literal.pos 113) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation9 113 (assignment s)
    (Sat.Literal.pos 4068) (Sat.Literal.pos 4067) (Sat.Literal.pos 113) (Sat.Literal.pos 139) (positive_of_descriptor s 4068 (.lex permutation9 113) (by rfl)) (lex_9_113_prefix s) (positive_select s 113) (lex_9_113_image s)

theorem lex_9_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.pos 113), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation9 113 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4067) (Sat.Literal.pos 113) (Sat.Literal.pos 139) (lex_9_113_prefix s) (positive_select s 113) (lex_9_113_image s)

theorem lex_9_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.pos 4067)] :=
  (lex_9_113_gate s).prop _ (List.Mem.head _)

theorem lex_9_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.neg 113), (Sat.Literal.pos 139)] :=
  (lex_9_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.pos 113), (Sat.Literal.neg 139)] :=
  (lex_9_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.neg 113), (Sat.Literal.neg 139), (Sat.Literal.pos 4068)] :=
  (lex_9_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4067), (Sat.Literal.pos 113), (Sat.Literal.pos 139), (Sat.Literal.pos 4068)] :=
  (lex_9_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4068) = lexBefore s permutation9 112 := by
  exact (positive_lex_of_descriptor s 4068 permutation9 113 (by rfl)).trans ((lex_skipped s permutation9 112 113 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation9 112) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation9 112 by rw [image9_eq]; rfl))

theorem lex_9_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4069) (Sat.Literal.pos 4068) (Sat.Literal.pos 112) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation9 112 (assignment s)
    (Sat.Literal.pos 4069) (Sat.Literal.pos 4068) (Sat.Literal.pos 112) (Sat.Literal.pos 131) (positive_of_descriptor s 4069 (.lex permutation9 112) (by rfl)) (lex_9_112_prefix s) (positive_select s 112) (lex_9_112_image s)

theorem lex_9_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.pos 112), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation9 112 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4068) (Sat.Literal.pos 112) (Sat.Literal.pos 131) (lex_9_112_prefix s) (positive_select s 112) (lex_9_112_image s)

theorem lex_9_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.pos 4068)] :=
  (lex_9_112_gate s).prop _ (List.Mem.head _)

theorem lex_9_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.neg 112), (Sat.Literal.pos 131)] :=
  (lex_9_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.pos 112), (Sat.Literal.neg 131)] :=
  (lex_9_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.neg 112), (Sat.Literal.neg 131), (Sat.Literal.pos 4069)] :=
  (lex_9_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4068), (Sat.Literal.pos 112), (Sat.Literal.pos 131), (Sat.Literal.pos 4069)] :=
  (lex_9_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4069) = lexBefore s permutation9 111 := by
  exact (positive_lex_of_descriptor s 4069 permutation9 112 (by rfl)).trans ((lex_skipped s permutation9 111 112 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation9 111) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation9 111 by rw [image9_eq]; rfl))

theorem lex_9_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4070) (Sat.Literal.pos 4069) (Sat.Literal.pos 111) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation9 111 (assignment s)
    (Sat.Literal.pos 4070) (Sat.Literal.pos 4069) (Sat.Literal.pos 111) (Sat.Literal.pos 123) (positive_of_descriptor s 4070 (.lex permutation9 111) (by rfl)) (lex_9_111_prefix s) (positive_select s 111) (lex_9_111_image s)

theorem lex_9_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.pos 111), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation9 111 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4069) (Sat.Literal.pos 111) (Sat.Literal.pos 123) (lex_9_111_prefix s) (positive_select s 111) (lex_9_111_image s)

theorem lex_9_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.pos 4069)] :=
  (lex_9_111_gate s).prop _ (List.Mem.head _)

theorem lex_9_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.neg 111), (Sat.Literal.pos 123)] :=
  (lex_9_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.pos 111), (Sat.Literal.neg 123)] :=
  (lex_9_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.neg 111), (Sat.Literal.neg 123), (Sat.Literal.pos 4070)] :=
  (lex_9_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4069), (Sat.Literal.pos 111), (Sat.Literal.pos 123), (Sat.Literal.pos 4070)] :=
  (lex_9_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4070) = lexBefore s permutation9 110 := by
  exact (positive_lex_of_descriptor s 4070 permutation9 111 (by rfl)).trans ((lex_skipped s permutation9 110 111 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation9 110) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation9 110 by rw [image9_eq]; rfl))

theorem lex_9_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4071) (Sat.Literal.pos 4070) (Sat.Literal.pos 110) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation9 110 (assignment s)
    (Sat.Literal.pos 4071) (Sat.Literal.pos 4070) (Sat.Literal.pos 110) (Sat.Literal.pos 115) (positive_of_descriptor s 4071 (.lex permutation9 110) (by rfl)) (lex_9_110_prefix s) (positive_select s 110) (lex_9_110_image s)

theorem lex_9_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.pos 110), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation9 110 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4070) (Sat.Literal.pos 110) (Sat.Literal.pos 115) (lex_9_110_prefix s) (positive_select s 110) (lex_9_110_image s)

theorem lex_9_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.pos 4070)] :=
  (lex_9_110_gate s).prop _ (List.Mem.head _)

theorem lex_9_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.neg 110), (Sat.Literal.pos 115)] :=
  (lex_9_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.pos 110), (Sat.Literal.neg 115)] :=
  (lex_9_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.neg 110), (Sat.Literal.neg 115), (Sat.Literal.pos 4071)] :=
  (lex_9_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4070), (Sat.Literal.pos 110), (Sat.Literal.pos 115), (Sat.Literal.pos 4071)] :=
  (lex_9_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4071) = lexBefore s permutation9 109 := by
  exact (positive_lex_of_descriptor s 4071 permutation9 110 (by rfl)).trans ((lex_skipped s permutation9 109 110 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation9 109) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation9 109 by rw [image9_eq]; rfl))

theorem lex_9_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4072) (Sat.Literal.pos 4071) (Sat.Literal.pos 109) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation9 109 (assignment s)
    (Sat.Literal.pos 4072) (Sat.Literal.pos 4071) (Sat.Literal.pos 109) (Sat.Literal.pos 107) (positive_of_descriptor s 4072 (.lex permutation9 109) (by rfl)) (lex_9_109_prefix s) (positive_select s 109) (lex_9_109_image s)

theorem lex_9_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.pos 109), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation9 109 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4071) (Sat.Literal.pos 109) (Sat.Literal.pos 107) (lex_9_109_prefix s) (positive_select s 109) (lex_9_109_image s)

theorem lex_9_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.pos 4071)] :=
  (lex_9_109_gate s).prop _ (List.Mem.head _)

theorem lex_9_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.neg 109), (Sat.Literal.pos 107)] :=
  (lex_9_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.pos 109), (Sat.Literal.neg 107)] :=
  (lex_9_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.neg 109), (Sat.Literal.neg 107), (Sat.Literal.pos 4072)] :=
  (lex_9_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4071), (Sat.Literal.pos 109), (Sat.Literal.pos 107), (Sat.Literal.pos 4072)] :=
  (lex_9_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4072) = lexBefore s permutation9 108 := by
  exact (positive_lex_of_descriptor s 4072 permutation9 109 (by rfl)).trans ((lex_skipped s permutation9 108 109 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation9 108) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation9 108 by rw [image9_eq]; rfl))

theorem lex_9_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4073) (Sat.Literal.pos 4072) (Sat.Literal.pos 108) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation9 108 (assignment s)
    (Sat.Literal.pos 4073) (Sat.Literal.pos 4072) (Sat.Literal.pos 108) (Sat.Literal.pos 99) (positive_of_descriptor s 4073 (.lex permutation9 108) (by rfl)) (lex_9_108_prefix s) (positive_select s 108) (lex_9_108_image s)

theorem lex_9_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.pos 108), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation9 108 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4072) (Sat.Literal.pos 108) (Sat.Literal.pos 99) (lex_9_108_prefix s) (positive_select s 108) (lex_9_108_image s)

theorem lex_9_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.pos 4072)] :=
  (lex_9_108_gate s).prop _ (List.Mem.head _)

theorem lex_9_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.neg 108), (Sat.Literal.pos 99)] :=
  (lex_9_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.pos 108), (Sat.Literal.neg 99)] :=
  (lex_9_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.neg 108), (Sat.Literal.neg 99), (Sat.Literal.pos 4073)] :=
  (lex_9_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4072), (Sat.Literal.pos 108), (Sat.Literal.pos 99), (Sat.Literal.pos 4073)] :=
  (lex_9_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4073) = lexBefore s permutation9 107 := by
  exact (positive_lex_of_descriptor s 4073 permutation9 108 (by rfl)).trans ((lex_skipped s permutation9 107 108 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation9 107) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation9 107 by rw [image9_eq]; rfl))

theorem lex_9_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4074) (Sat.Literal.pos 4073) (Sat.Literal.pos 107) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation9 107 (assignment s)
    (Sat.Literal.pos 4074) (Sat.Literal.pos 4073) (Sat.Literal.pos 107) (Sat.Literal.pos 91) (positive_of_descriptor s 4074 (.lex permutation9 107) (by rfl)) (lex_9_107_prefix s) (positive_select s 107) (lex_9_107_image s)

theorem lex_9_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.pos 107), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation9 107 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4073) (Sat.Literal.pos 107) (Sat.Literal.pos 91) (lex_9_107_prefix s) (positive_select s 107) (lex_9_107_image s)

theorem lex_9_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.pos 4073)] :=
  (lex_9_107_gate s).prop _ (List.Mem.head _)

theorem lex_9_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.neg 107), (Sat.Literal.pos 91)] :=
  (lex_9_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.pos 107), (Sat.Literal.neg 91)] :=
  (lex_9_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.neg 107), (Sat.Literal.neg 91), (Sat.Literal.pos 4074)] :=
  (lex_9_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4073), (Sat.Literal.pos 107), (Sat.Literal.pos 91), (Sat.Literal.pos 4074)] :=
  (lex_9_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4074) = lexBefore s permutation9 106 := by
  exact (positive_lex_of_descriptor s 4074 permutation9 107 (by rfl)).trans ((lex_skipped s permutation9 106 107 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation9 106) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation9 106 by rw [image9_eq]; rfl))

theorem lex_9_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4075) (Sat.Literal.pos 4074) (Sat.Literal.pos 106) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation9 106 (assignment s)
    (Sat.Literal.pos 4075) (Sat.Literal.pos 4074) (Sat.Literal.pos 106) (Sat.Literal.pos 83) (positive_of_descriptor s 4075 (.lex permutation9 106) (by rfl)) (lex_9_106_prefix s) (positive_select s 106) (lex_9_106_image s)

theorem lex_9_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.pos 106), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation9 106 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4074) (Sat.Literal.pos 106) (Sat.Literal.pos 83) (lex_9_106_prefix s) (positive_select s 106) (lex_9_106_image s)

theorem lex_9_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.pos 4074)] :=
  (lex_9_106_gate s).prop _ (List.Mem.head _)

theorem lex_9_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.neg 106), (Sat.Literal.pos 83)] :=
  (lex_9_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.pos 106), (Sat.Literal.neg 83)] :=
  (lex_9_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.neg 106), (Sat.Literal.neg 83), (Sat.Literal.pos 4075)] :=
  (lex_9_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4074), (Sat.Literal.pos 106), (Sat.Literal.pos 83), (Sat.Literal.pos 4075)] :=
  (lex_9_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4075) = lexBefore s permutation9 105 := by
  exact (positive_lex_of_descriptor s 4075 permutation9 106 (by rfl)).trans ((lex_skipped s permutation9 105 106 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation9 105) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation9 105 by rw [image9_eq]; rfl))

theorem lex_9_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4076) (Sat.Literal.pos 4075) (Sat.Literal.pos 105) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation9 105 (assignment s)
    (Sat.Literal.pos 4076) (Sat.Literal.pos 4075) (Sat.Literal.pos 105) (Sat.Literal.pos 75) (positive_of_descriptor s 4076 (.lex permutation9 105) (by rfl)) (lex_9_105_prefix s) (positive_select s 105) (lex_9_105_image s)

theorem lex_9_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.pos 105), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation9 105 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4075) (Sat.Literal.pos 105) (Sat.Literal.pos 75) (lex_9_105_prefix s) (positive_select s 105) (lex_9_105_image s)

theorem lex_9_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.pos 4075)] :=
  (lex_9_105_gate s).prop _ (List.Mem.head _)

theorem lex_9_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.neg 105), (Sat.Literal.pos 75)] :=
  (lex_9_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.pos 105), (Sat.Literal.neg 75)] :=
  (lex_9_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.neg 105), (Sat.Literal.neg 75), (Sat.Literal.pos 4076)] :=
  (lex_9_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4075), (Sat.Literal.pos 105), (Sat.Literal.pos 75), (Sat.Literal.pos 4076)] :=
  (lex_9_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4076) = lexBefore s permutation9 104 := by
  exact (positive_lex_of_descriptor s 4076 permutation9 105 (by rfl)).trans ((lex_skipped s permutation9 104 105 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation9 104) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation9 104 by rw [image9_eq]; rfl))

theorem lex_9_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4077) (Sat.Literal.pos 4076) (Sat.Literal.pos 104) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation9 104 (assignment s)
    (Sat.Literal.pos 4077) (Sat.Literal.pos 4076) (Sat.Literal.pos 104) (Sat.Literal.pos 67) (positive_of_descriptor s 4077 (.lex permutation9 104) (by rfl)) (lex_9_104_prefix s) (positive_select s 104) (lex_9_104_image s)

theorem lex_9_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.pos 104), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation9 104 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4076) (Sat.Literal.pos 104) (Sat.Literal.pos 67) (lex_9_104_prefix s) (positive_select s 104) (lex_9_104_image s)

theorem lex_9_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.pos 4076)] :=
  (lex_9_104_gate s).prop _ (List.Mem.head _)

theorem lex_9_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.neg 104), (Sat.Literal.pos 67)] :=
  (lex_9_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.pos 104), (Sat.Literal.neg 67)] :=
  (lex_9_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.neg 104), (Sat.Literal.neg 67), (Sat.Literal.pos 4077)] :=
  (lex_9_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4076), (Sat.Literal.pos 104), (Sat.Literal.pos 67), (Sat.Literal.pos 4077)] :=
  (lex_9_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4077) = lexBefore s permutation9 103 := by
  exact (positive_lex_of_descriptor s 4077 permutation9 104 (by rfl)).trans ((lex_skipped s permutation9 103 104 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation9 103) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation9 103 by rw [image9_eq]; rfl))

theorem lex_9_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4078) (Sat.Literal.pos 4077) (Sat.Literal.pos 103) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation9 103 (assignment s)
    (Sat.Literal.pos 4078) (Sat.Literal.pos 4077) (Sat.Literal.pos 103) (Sat.Literal.pos 59) (positive_of_descriptor s 4078 (.lex permutation9 103) (by rfl)) (lex_9_103_prefix s) (positive_select s 103) (lex_9_103_image s)

theorem lex_9_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.pos 103), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation9 103 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4077) (Sat.Literal.pos 103) (Sat.Literal.pos 59) (lex_9_103_prefix s) (positive_select s 103) (lex_9_103_image s)

theorem lex_9_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.pos 4077)] :=
  (lex_9_103_gate s).prop _ (List.Mem.head _)

theorem lex_9_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.neg 103), (Sat.Literal.pos 59)] :=
  (lex_9_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.pos 103), (Sat.Literal.neg 59)] :=
  (lex_9_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.neg 103), (Sat.Literal.neg 59), (Sat.Literal.pos 4078)] :=
  (lex_9_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4077), (Sat.Literal.pos 103), (Sat.Literal.pos 59), (Sat.Literal.pos 4078)] :=
  (lex_9_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4078) = lexBefore s permutation9 102 := by
  exact (positive_lex_of_descriptor s 4078 permutation9 103 (by rfl)).trans ((lex_skipped s permutation9 102 103 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation9 102) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation9 102 by rw [image9_eq]; rfl))

theorem lex_9_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4079) (Sat.Literal.pos 4078) (Sat.Literal.pos 102) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation9 102 (assignment s)
    (Sat.Literal.pos 4079) (Sat.Literal.pos 4078) (Sat.Literal.pos 102) (Sat.Literal.pos 51) (positive_of_descriptor s 4079 (.lex permutation9 102) (by rfl)) (lex_9_102_prefix s) (positive_select s 102) (lex_9_102_image s)

theorem lex_9_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.pos 102), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation9 102 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4078) (Sat.Literal.pos 102) (Sat.Literal.pos 51) (lex_9_102_prefix s) (positive_select s 102) (lex_9_102_image s)

theorem lex_9_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.pos 4078)] :=
  (lex_9_102_gate s).prop _ (List.Mem.head _)

theorem lex_9_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.neg 102), (Sat.Literal.pos 51)] :=
  (lex_9_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.pos 102), (Sat.Literal.neg 51)] :=
  (lex_9_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.neg 102), (Sat.Literal.neg 51), (Sat.Literal.pos 4079)] :=
  (lex_9_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4078), (Sat.Literal.pos 102), (Sat.Literal.pos 51), (Sat.Literal.pos 4079)] :=
  (lex_9_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4079) = lexBefore s permutation9 101 := by
  exact (positive_lex_of_descriptor s 4079 permutation9 102 (by rfl)).trans ((lex_skipped s permutation9 101 102 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation9 101) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation9 101 by rw [image9_eq]; rfl))

theorem lex_9_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4080) (Sat.Literal.pos 4079) (Sat.Literal.pos 101) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation9 101 (assignment s)
    (Sat.Literal.pos 4080) (Sat.Literal.pos 4079) (Sat.Literal.pos 101) (Sat.Literal.pos 43) (positive_of_descriptor s 4080 (.lex permutation9 101) (by rfl)) (lex_9_101_prefix s) (positive_select s 101) (lex_9_101_image s)

theorem lex_9_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.pos 101), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation9 101 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4079) (Sat.Literal.pos 101) (Sat.Literal.pos 43) (lex_9_101_prefix s) (positive_select s 101) (lex_9_101_image s)

theorem lex_9_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.pos 4079)] :=
  (lex_9_101_gate s).prop _ (List.Mem.head _)

theorem lex_9_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.neg 101), (Sat.Literal.pos 43)] :=
  (lex_9_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.pos 101), (Sat.Literal.neg 43)] :=
  (lex_9_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.neg 101), (Sat.Literal.neg 43), (Sat.Literal.pos 4080)] :=
  (lex_9_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4079), (Sat.Literal.pos 101), (Sat.Literal.pos 43), (Sat.Literal.pos 4080)] :=
  (lex_9_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4080) = lexBefore s permutation9 100 := by
  exact (positive_lex_of_descriptor s 4080 permutation9 101 (by rfl)).trans ((lex_skipped s permutation9 100 101 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation9 100) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation9 100 by rw [image9_eq]; rfl))

theorem lex_9_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4081) (Sat.Literal.pos 4080) (Sat.Literal.pos 100) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation9 100 (assignment s)
    (Sat.Literal.pos 4081) (Sat.Literal.pos 4080) (Sat.Literal.pos 100) (Sat.Literal.pos 35) (positive_of_descriptor s 4081 (.lex permutation9 100) (by rfl)) (lex_9_100_prefix s) (positive_select s 100) (lex_9_100_image s)

theorem lex_9_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.pos 100), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation9 100 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4080) (Sat.Literal.pos 100) (Sat.Literal.pos 35) (lex_9_100_prefix s) (positive_select s 100) (lex_9_100_image s)

theorem lex_9_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.pos 4080)] :=
  (lex_9_100_gate s).prop _ (List.Mem.head _)

theorem lex_9_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.neg 100), (Sat.Literal.pos 35)] :=
  (lex_9_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.pos 100), (Sat.Literal.neg 35)] :=
  (lex_9_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.neg 100), (Sat.Literal.neg 35), (Sat.Literal.pos 4081)] :=
  (lex_9_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4080), (Sat.Literal.pos 100), (Sat.Literal.pos 35), (Sat.Literal.pos 4081)] :=
  (lex_9_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4081) = lexBefore s permutation9 99 := by
  exact (positive_lex_of_descriptor s 4081 permutation9 100 (by rfl)).trans ((lex_skipped s permutation9 99 100 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation9 99) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation9 99 by rw [image9_eq]; rfl))

theorem lex_9_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4082) (Sat.Literal.pos 4081) (Sat.Literal.pos 99) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation9 99 (assignment s)
    (Sat.Literal.pos 4082) (Sat.Literal.pos 4081) (Sat.Literal.pos 99) (Sat.Literal.pos 27) (positive_of_descriptor s 4082 (.lex permutation9 99) (by rfl)) (lex_9_99_prefix s) (positive_select s 99) (lex_9_99_image s)

theorem lex_9_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.pos 99), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation9 99 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4081) (Sat.Literal.pos 99) (Sat.Literal.pos 27) (lex_9_99_prefix s) (positive_select s 99) (lex_9_99_image s)

theorem lex_9_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.pos 4081)] :=
  (lex_9_99_gate s).prop _ (List.Mem.head _)

theorem lex_9_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.neg 99), (Sat.Literal.pos 27)] :=
  (lex_9_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.pos 99), (Sat.Literal.neg 27)] :=
  (lex_9_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.neg 99), (Sat.Literal.neg 27), (Sat.Literal.pos 4082)] :=
  (lex_9_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4081), (Sat.Literal.pos 99), (Sat.Literal.pos 27), (Sat.Literal.pos 4082)] :=
  (lex_9_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4082) = lexBefore s permutation9 98 := by
  exact (positive_lex_of_descriptor s 4082 permutation9 99 (by rfl)).trans ((lex_skipped s permutation9 98 99 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation9 98) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation9 98 by rw [image9_eq]; rfl))

theorem lex_9_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4083) (Sat.Literal.pos 4082) (Sat.Literal.pos 98) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation9 98 (assignment s)
    (Sat.Literal.pos 4083) (Sat.Literal.pos 4082) (Sat.Literal.pos 98) (Sat.Literal.pos 19) (positive_of_descriptor s 4083 (.lex permutation9 98) (by rfl)) (lex_9_98_prefix s) (positive_select s 98) (lex_9_98_image s)

theorem lex_9_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.pos 98), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation9 98 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4082) (Sat.Literal.pos 98) (Sat.Literal.pos 19) (lex_9_98_prefix s) (positive_select s 98) (lex_9_98_image s)

theorem lex_9_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.pos 4082)] :=
  (lex_9_98_gate s).prop _ (List.Mem.head _)

theorem lex_9_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.neg 98), (Sat.Literal.pos 19)] :=
  (lex_9_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.pos 98), (Sat.Literal.neg 19)] :=
  (lex_9_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.neg 98), (Sat.Literal.neg 19), (Sat.Literal.pos 4083)] :=
  (lex_9_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4082), (Sat.Literal.pos 98), (Sat.Literal.pos 19), (Sat.Literal.pos 4083)] :=
  (lex_9_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4083) = lexBefore s permutation9 97 := by
  exact (positive_lex_of_descriptor s 4083 permutation9 98 (by rfl)).trans ((lex_skipped s permutation9 97 98 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation9 97) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation9 97 by rw [image9_eq]; rfl))

theorem lex_9_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4084) (Sat.Literal.pos 4083) (Sat.Literal.pos 97) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation9 97 (assignment s)
    (Sat.Literal.pos 4084) (Sat.Literal.pos 4083) (Sat.Literal.pos 97) (Sat.Literal.pos 11) (positive_of_descriptor s 4084 (.lex permutation9 97) (by rfl)) (lex_9_97_prefix s) (positive_select s 97) (lex_9_97_image s)

theorem lex_9_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.pos 97), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation9 97 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4083) (Sat.Literal.pos 97) (Sat.Literal.pos 11) (lex_9_97_prefix s) (positive_select s 97) (lex_9_97_image s)

theorem lex_9_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.pos 4083)] :=
  (lex_9_97_gate s).prop _ (List.Mem.head _)

theorem lex_9_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.neg 97), (Sat.Literal.pos 11)] :=
  (lex_9_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.pos 97), (Sat.Literal.neg 11)] :=
  (lex_9_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.neg 97), (Sat.Literal.neg 11), (Sat.Literal.pos 4084)] :=
  (lex_9_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4083), (Sat.Literal.pos 97), (Sat.Literal.pos 11), (Sat.Literal.pos 4084)] :=
  (lex_9_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4084) = lexBefore s permutation9 96 := by
  exact (positive_lex_of_descriptor s 4084 permutation9 97 (by rfl)).trans ((lex_skipped s permutation9 96 97 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation9 96) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation9 96 by rw [image9_eq]; rfl))

theorem lex_9_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4085) (Sat.Literal.pos 4084) (Sat.Literal.pos 96) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation9 96 (assignment s)
    (Sat.Literal.pos 4085) (Sat.Literal.pos 4084) (Sat.Literal.pos 96) (Sat.Literal.pos 3) (positive_of_descriptor s 4085 (.lex permutation9 96) (by rfl)) (lex_9_96_prefix s) (positive_select s 96) (lex_9_96_image s)

theorem lex_9_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.pos 96), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation9 96 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4084) (Sat.Literal.pos 96) (Sat.Literal.pos 3) (lex_9_96_prefix s) (positive_select s 96) (lex_9_96_image s)

theorem lex_9_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.pos 4084)] :=
  (lex_9_96_gate s).prop _ (List.Mem.head _)

theorem lex_9_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.neg 96), (Sat.Literal.pos 3)] :=
  (lex_9_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.pos 96), (Sat.Literal.neg 3)] :=
  (lex_9_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.neg 96), (Sat.Literal.neg 3), (Sat.Literal.pos 4085)] :=
  (lex_9_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4084), (Sat.Literal.pos 96), (Sat.Literal.pos 3), (Sat.Literal.pos 4085)] :=
  (lex_9_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4085) = lexBefore s permutation9 95 := by
  exact (positive_lex_of_descriptor s 4085 permutation9 96 (by rfl)).trans ((lex_skipped s permutation9 95 96 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation9 95) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation9 95 by rw [image9_eq]; rfl))

theorem lex_9_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4086) (Sat.Literal.pos 4085) (Sat.Literal.pos 95) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation9 95 (assignment s)
    (Sat.Literal.pos 4086) (Sat.Literal.pos 4085) (Sat.Literal.pos 95) (Sat.Literal.pos 250) (positive_of_descriptor s 4086 (.lex permutation9 95) (by rfl)) (lex_9_95_prefix s) (positive_select s 95) (lex_9_95_image s)

theorem lex_9_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.pos 95), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation9 95 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4085) (Sat.Literal.pos 95) (Sat.Literal.pos 250) (lex_9_95_prefix s) (positive_select s 95) (lex_9_95_image s)

theorem lex_9_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.pos 4085)] :=
  (lex_9_95_gate s).prop _ (List.Mem.head _)

theorem lex_9_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.neg 95), (Sat.Literal.pos 250)] :=
  (lex_9_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.pos 95), (Sat.Literal.neg 250)] :=
  (lex_9_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.neg 95), (Sat.Literal.neg 250), (Sat.Literal.pos 4086)] :=
  (lex_9_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4085), (Sat.Literal.pos 95), (Sat.Literal.pos 250), (Sat.Literal.pos 4086)] :=
  (lex_9_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4086) = lexBefore s permutation9 94 := by
  exact (positive_lex_of_descriptor s 4086 permutation9 95 (by rfl)).trans ((lex_skipped s permutation9 94 95 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation9 94) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation9 94 by rw [image9_eq]; rfl))

theorem lex_9_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4087) (Sat.Literal.pos 4086) (Sat.Literal.pos 94) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation9 94 (assignment s)
    (Sat.Literal.pos 4087) (Sat.Literal.pos 4086) (Sat.Literal.pos 94) (Sat.Literal.pos 242) (positive_of_descriptor s 4087 (.lex permutation9 94) (by rfl)) (lex_9_94_prefix s) (positive_select s 94) (lex_9_94_image s)

theorem lex_9_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.pos 94), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation9 94 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4086) (Sat.Literal.pos 94) (Sat.Literal.pos 242) (lex_9_94_prefix s) (positive_select s 94) (lex_9_94_image s)

theorem lex_9_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.pos 4086)] :=
  (lex_9_94_gate s).prop _ (List.Mem.head _)

theorem lex_9_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.neg 94), (Sat.Literal.pos 242)] :=
  (lex_9_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.pos 94), (Sat.Literal.neg 242)] :=
  (lex_9_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.neg 94), (Sat.Literal.neg 242), (Sat.Literal.pos 4087)] :=
  (lex_9_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4086), (Sat.Literal.pos 94), (Sat.Literal.pos 242), (Sat.Literal.pos 4087)] :=
  (lex_9_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4087) = lexBefore s permutation9 93 := by
  exact (positive_lex_of_descriptor s 4087 permutation9 94 (by rfl)).trans ((lex_skipped s permutation9 93 94 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation9 93) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation9 93 by rw [image9_eq]; rfl))

theorem lex_9_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4088) (Sat.Literal.pos 4087) (Sat.Literal.pos 93) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation9 93 (assignment s)
    (Sat.Literal.pos 4088) (Sat.Literal.pos 4087) (Sat.Literal.pos 93) (Sat.Literal.pos 234) (positive_of_descriptor s 4088 (.lex permutation9 93) (by rfl)) (lex_9_93_prefix s) (positive_select s 93) (lex_9_93_image s)

theorem lex_9_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.pos 93), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation9 93 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4087) (Sat.Literal.pos 93) (Sat.Literal.pos 234) (lex_9_93_prefix s) (positive_select s 93) (lex_9_93_image s)

theorem lex_9_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.pos 4087)] :=
  (lex_9_93_gate s).prop _ (List.Mem.head _)

theorem lex_9_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.neg 93), (Sat.Literal.pos 234)] :=
  (lex_9_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.pos 93), (Sat.Literal.neg 234)] :=
  (lex_9_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.neg 93), (Sat.Literal.neg 234), (Sat.Literal.pos 4088)] :=
  (lex_9_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4087), (Sat.Literal.pos 93), (Sat.Literal.pos 234), (Sat.Literal.pos 4088)] :=
  (lex_9_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4088) = lexBefore s permutation9 92 := by
  exact (positive_lex_of_descriptor s 4088 permutation9 93 (by rfl)).trans ((lex_skipped s permutation9 92 93 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation9 92) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation9 92 by rw [image9_eq]; rfl))

theorem lex_9_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4089) (Sat.Literal.pos 4088) (Sat.Literal.pos 92) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation9 92 (assignment s)
    (Sat.Literal.pos 4089) (Sat.Literal.pos 4088) (Sat.Literal.pos 92) (Sat.Literal.pos 226) (positive_of_descriptor s 4089 (.lex permutation9 92) (by rfl)) (lex_9_92_prefix s) (positive_select s 92) (lex_9_92_image s)

theorem lex_9_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.pos 92), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation9 92 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4088) (Sat.Literal.pos 92) (Sat.Literal.pos 226) (lex_9_92_prefix s) (positive_select s 92) (lex_9_92_image s)

theorem lex_9_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.pos 4088)] :=
  (lex_9_92_gate s).prop _ (List.Mem.head _)

theorem lex_9_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.neg 92), (Sat.Literal.pos 226)] :=
  (lex_9_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.pos 92), (Sat.Literal.neg 226)] :=
  (lex_9_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.neg 92), (Sat.Literal.neg 226), (Sat.Literal.pos 4089)] :=
  (lex_9_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4088), (Sat.Literal.pos 92), (Sat.Literal.pos 226), (Sat.Literal.pos 4089)] :=
  (lex_9_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4089) = lexBefore s permutation9 91 := by
  exact (positive_lex_of_descriptor s 4089 permutation9 92 (by rfl)).trans ((lex_skipped s permutation9 91 92 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation9 91) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation9 91 by rw [image9_eq]; rfl))

theorem lex_9_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4090) (Sat.Literal.pos 4089) (Sat.Literal.pos 91) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation9 91 (assignment s)
    (Sat.Literal.pos 4090) (Sat.Literal.pos 4089) (Sat.Literal.pos 91) (Sat.Literal.pos 218) (positive_of_descriptor s 4090 (.lex permutation9 91) (by rfl)) (lex_9_91_prefix s) (positive_select s 91) (lex_9_91_image s)

theorem lex_9_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.pos 91), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation9 91 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4089) (Sat.Literal.pos 91) (Sat.Literal.pos 218) (lex_9_91_prefix s) (positive_select s 91) (lex_9_91_image s)

theorem lex_9_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.pos 4089)] :=
  (lex_9_91_gate s).prop _ (List.Mem.head _)

theorem lex_9_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.neg 91), (Sat.Literal.pos 218)] :=
  (lex_9_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.pos 91), (Sat.Literal.neg 218)] :=
  (lex_9_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.neg 91), (Sat.Literal.neg 218), (Sat.Literal.pos 4090)] :=
  (lex_9_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4089), (Sat.Literal.pos 91), (Sat.Literal.pos 218), (Sat.Literal.pos 4090)] :=
  (lex_9_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4090) = lexBefore s permutation9 90 := by
  exact (positive_lex_of_descriptor s 4090 permutation9 91 (by rfl)).trans ((lex_skipped s permutation9 90 91 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation9 90) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation9 90 by rw [image9_eq]; rfl))

theorem lex_9_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4091) (Sat.Literal.pos 4090) (Sat.Literal.pos 90) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation9 90 (assignment s)
    (Sat.Literal.pos 4091) (Sat.Literal.pos 4090) (Sat.Literal.pos 90) (Sat.Literal.pos 210) (positive_of_descriptor s 4091 (.lex permutation9 90) (by rfl)) (lex_9_90_prefix s) (positive_select s 90) (lex_9_90_image s)

theorem lex_9_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.pos 90), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation9 90 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4090) (Sat.Literal.pos 90) (Sat.Literal.pos 210) (lex_9_90_prefix s) (positive_select s 90) (lex_9_90_image s)

theorem lex_9_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.pos 4090)] :=
  (lex_9_90_gate s).prop _ (List.Mem.head _)

theorem lex_9_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.neg 90), (Sat.Literal.pos 210)] :=
  (lex_9_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.pos 90), (Sat.Literal.neg 210)] :=
  (lex_9_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.neg 90), (Sat.Literal.neg 210), (Sat.Literal.pos 4091)] :=
  (lex_9_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4090), (Sat.Literal.pos 90), (Sat.Literal.pos 210), (Sat.Literal.pos 4091)] :=
  (lex_9_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4091) = lexBefore s permutation9 89 := by
  exact (positive_lex_of_descriptor s 4091 permutation9 90 (by rfl)).trans ((lex_skipped s permutation9 89 90 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation9 89) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation9 89 by rw [image9_eq]; rfl))

theorem lex_9_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4092) (Sat.Literal.pos 4091) (Sat.Literal.pos 89) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation9 89 (assignment s)
    (Sat.Literal.pos 4092) (Sat.Literal.pos 4091) (Sat.Literal.pos 89) (Sat.Literal.pos 202) (positive_of_descriptor s 4092 (.lex permutation9 89) (by rfl)) (lex_9_89_prefix s) (positive_select s 89) (lex_9_89_image s)

theorem lex_9_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.pos 89), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation9 89 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4091) (Sat.Literal.pos 89) (Sat.Literal.pos 202) (lex_9_89_prefix s) (positive_select s 89) (lex_9_89_image s)

theorem lex_9_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.pos 4091)] :=
  (lex_9_89_gate s).prop _ (List.Mem.head _)

theorem lex_9_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.neg 89), (Sat.Literal.pos 202)] :=
  (lex_9_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.pos 89), (Sat.Literal.neg 202)] :=
  (lex_9_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.neg 89), (Sat.Literal.neg 202), (Sat.Literal.pos 4092)] :=
  (lex_9_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4091), (Sat.Literal.pos 89), (Sat.Literal.pos 202), (Sat.Literal.pos 4092)] :=
  (lex_9_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4092) = lexBefore s permutation9 88 := by
  exact (positive_lex_of_descriptor s 4092 permutation9 89 (by rfl)).trans ((lex_skipped s permutation9 88 89 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation9 88) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation9 88 by rw [image9_eq]; rfl))

theorem lex_9_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4093) (Sat.Literal.pos 4092) (Sat.Literal.pos 88) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation9 88 (assignment s)
    (Sat.Literal.pos 4093) (Sat.Literal.pos 4092) (Sat.Literal.pos 88) (Sat.Literal.pos 194) (positive_of_descriptor s 4093 (.lex permutation9 88) (by rfl)) (lex_9_88_prefix s) (positive_select s 88) (lex_9_88_image s)

theorem lex_9_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.pos 88), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation9 88 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4092) (Sat.Literal.pos 88) (Sat.Literal.pos 194) (lex_9_88_prefix s) (positive_select s 88) (lex_9_88_image s)

theorem lex_9_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.pos 4092)] :=
  (lex_9_88_gate s).prop _ (List.Mem.head _)

theorem lex_9_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.neg 88), (Sat.Literal.pos 194)] :=
  (lex_9_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.pos 88), (Sat.Literal.neg 194)] :=
  (lex_9_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.neg 88), (Sat.Literal.neg 194), (Sat.Literal.pos 4093)] :=
  (lex_9_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4092), (Sat.Literal.pos 88), (Sat.Literal.pos 194), (Sat.Literal.pos 4093)] :=
  (lex_9_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4093) = lexBefore s permutation9 87 := by
  exact (positive_lex_of_descriptor s 4093 permutation9 88 (by rfl)).trans ((lex_skipped s permutation9 87 88 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation9 87) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation9 87 by rw [image9_eq]; rfl))

theorem lex_9_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4094) (Sat.Literal.pos 4093) (Sat.Literal.pos 87) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation9 87 (assignment s)
    (Sat.Literal.pos 4094) (Sat.Literal.pos 4093) (Sat.Literal.pos 87) (Sat.Literal.pos 186) (positive_of_descriptor s 4094 (.lex permutation9 87) (by rfl)) (lex_9_87_prefix s) (positive_select s 87) (lex_9_87_image s)

theorem lex_9_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.pos 87), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation9 87 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4093) (Sat.Literal.pos 87) (Sat.Literal.pos 186) (lex_9_87_prefix s) (positive_select s 87) (lex_9_87_image s)

theorem lex_9_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.pos 4093)] :=
  (lex_9_87_gate s).prop _ (List.Mem.head _)

theorem lex_9_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.neg 87), (Sat.Literal.pos 186)] :=
  (lex_9_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.pos 87), (Sat.Literal.neg 186)] :=
  (lex_9_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.neg 87), (Sat.Literal.neg 186), (Sat.Literal.pos 4094)] :=
  (lex_9_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4093), (Sat.Literal.pos 87), (Sat.Literal.pos 186), (Sat.Literal.pos 4094)] :=
  (lex_9_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4094) = lexBefore s permutation9 86 := by
  exact (positive_lex_of_descriptor s 4094 permutation9 87 (by rfl)).trans ((lex_skipped s permutation9 86 87 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation9 86) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation9 86 by rw [image9_eq]; rfl))

theorem lex_9_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4095) (Sat.Literal.pos 4094) (Sat.Literal.pos 86) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation9 86 (assignment s)
    (Sat.Literal.pos 4095) (Sat.Literal.pos 4094) (Sat.Literal.pos 86) (Sat.Literal.pos 178) (positive_of_descriptor s 4095 (.lex permutation9 86) (by rfl)) (lex_9_86_prefix s) (positive_select s 86) (lex_9_86_image s)

theorem lex_9_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.pos 86), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation9 86 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4094) (Sat.Literal.pos 86) (Sat.Literal.pos 178) (lex_9_86_prefix s) (positive_select s 86) (lex_9_86_image s)

theorem lex_9_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.pos 4094)] :=
  (lex_9_86_gate s).prop _ (List.Mem.head _)

theorem lex_9_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.neg 86), (Sat.Literal.pos 178)] :=
  (lex_9_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.pos 86), (Sat.Literal.neg 178)] :=
  (lex_9_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.neg 86), (Sat.Literal.neg 178), (Sat.Literal.pos 4095)] :=
  (lex_9_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4094), (Sat.Literal.pos 86), (Sat.Literal.pos 178), (Sat.Literal.pos 4095)] :=
  (lex_9_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4095) = lexBefore s permutation9 85 := by
  exact (positive_lex_of_descriptor s 4095 permutation9 86 (by rfl)).trans ((lex_skipped s permutation9 85 86 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation9 85) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation9 85 by rw [image9_eq]; rfl))

theorem lex_9_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4096) (Sat.Literal.pos 4095) (Sat.Literal.pos 85) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation9 85 (assignment s)
    (Sat.Literal.pos 4096) (Sat.Literal.pos 4095) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (positive_of_descriptor s 4096 (.lex permutation9 85) (by rfl)) (lex_9_85_prefix s) (positive_select s 85) (lex_9_85_image s)

theorem lex_9_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation9 85 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4095) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (lex_9_85_prefix s) (positive_select s 85) (lex_9_85_image s)

theorem lex_9_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.pos 4095)] :=
  (lex_9_85_gate s).prop _ (List.Mem.head _)

theorem lex_9_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.neg 85), (Sat.Literal.pos 170)] :=
  (lex_9_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] :=
  (lex_9_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.neg 85), (Sat.Literal.neg 170), (Sat.Literal.pos 4096)] :=
  (lex_9_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4095), (Sat.Literal.pos 85), (Sat.Literal.pos 170), (Sat.Literal.pos 4096)] :=
  (lex_9_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4096) = lexBefore s permutation9 84 := by
  exact (positive_lex_of_descriptor s 4096 permutation9 85 (by rfl)).trans ((lex_skipped s permutation9 84 85 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation9 84) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation9 84 by rw [image9_eq]; rfl))

theorem lex_9_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4097) (Sat.Literal.pos 4096) (Sat.Literal.pos 84) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation9 84 (assignment s)
    (Sat.Literal.pos 4097) (Sat.Literal.pos 4096) (Sat.Literal.pos 84) (Sat.Literal.pos 162) (positive_of_descriptor s 4097 (.lex permutation9 84) (by rfl)) (lex_9_84_prefix s) (positive_select s 84) (lex_9_84_image s)

theorem lex_9_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.pos 84), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation9 84 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4096) (Sat.Literal.pos 84) (Sat.Literal.pos 162) (lex_9_84_prefix s) (positive_select s 84) (lex_9_84_image s)

theorem lex_9_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.pos 4096)] :=
  (lex_9_84_gate s).prop _ (List.Mem.head _)

theorem lex_9_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.neg 84), (Sat.Literal.pos 162)] :=
  (lex_9_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.pos 84), (Sat.Literal.neg 162)] :=
  (lex_9_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.neg 84), (Sat.Literal.neg 162), (Sat.Literal.pos 4097)] :=
  (lex_9_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4096), (Sat.Literal.pos 84), (Sat.Literal.pos 162), (Sat.Literal.pos 4097)] :=
  (lex_9_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4097) = lexBefore s permutation9 83 := by
  exact (positive_lex_of_descriptor s 4097 permutation9 84 (by rfl)).trans ((lex_skipped s permutation9 83 84 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation9 83) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation9 83 by rw [image9_eq]; rfl))

theorem lex_9_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4098) (Sat.Literal.pos 4097) (Sat.Literal.pos 83) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation9 83 (assignment s)
    (Sat.Literal.pos 4098) (Sat.Literal.pos 4097) (Sat.Literal.pos 83) (Sat.Literal.pos 154) (positive_of_descriptor s 4098 (.lex permutation9 83) (by rfl)) (lex_9_83_prefix s) (positive_select s 83) (lex_9_83_image s)

theorem lex_9_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.pos 83), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation9 83 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4097) (Sat.Literal.pos 83) (Sat.Literal.pos 154) (lex_9_83_prefix s) (positive_select s 83) (lex_9_83_image s)

theorem lex_9_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.pos 4097)] :=
  (lex_9_83_gate s).prop _ (List.Mem.head _)

theorem lex_9_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.neg 83), (Sat.Literal.pos 154)] :=
  (lex_9_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.pos 83), (Sat.Literal.neg 154)] :=
  (lex_9_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.neg 83), (Sat.Literal.neg 154), (Sat.Literal.pos 4098)] :=
  (lex_9_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4097), (Sat.Literal.pos 83), (Sat.Literal.pos 154), (Sat.Literal.pos 4098)] :=
  (lex_9_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4098) = lexBefore s permutation9 82 := by
  exact (positive_lex_of_descriptor s 4098 permutation9 83 (by rfl)).trans ((lex_skipped s permutation9 82 83 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation9 82) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation9 82 by rw [image9_eq]; rfl))

theorem lex_9_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4099) (Sat.Literal.pos 4098) (Sat.Literal.pos 82) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation9 82 (assignment s)
    (Sat.Literal.pos 4099) (Sat.Literal.pos 4098) (Sat.Literal.pos 82) (Sat.Literal.pos 146) (positive_of_descriptor s 4099 (.lex permutation9 82) (by rfl)) (lex_9_82_prefix s) (positive_select s 82) (lex_9_82_image s)

theorem lex_9_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.pos 82), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation9 82 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4098) (Sat.Literal.pos 82) (Sat.Literal.pos 146) (lex_9_82_prefix s) (positive_select s 82) (lex_9_82_image s)

theorem lex_9_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.pos 4098)] :=
  (lex_9_82_gate s).prop _ (List.Mem.head _)

theorem lex_9_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.neg 82), (Sat.Literal.pos 146)] :=
  (lex_9_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.pos 82), (Sat.Literal.neg 146)] :=
  (lex_9_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.neg 82), (Sat.Literal.neg 146), (Sat.Literal.pos 4099)] :=
  (lex_9_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4098), (Sat.Literal.pos 82), (Sat.Literal.pos 146), (Sat.Literal.pos 4099)] :=
  (lex_9_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4099) = lexBefore s permutation9 81 := by
  exact (positive_lex_of_descriptor s 4099 permutation9 82 (by rfl)).trans ((lex_skipped s permutation9 81 82 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation9 81) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation9 81 by rw [image9_eq]; rfl))

theorem lex_9_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4100) (Sat.Literal.pos 4099) (Sat.Literal.pos 81) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation9 81 (assignment s)
    (Sat.Literal.pos 4100) (Sat.Literal.pos 4099) (Sat.Literal.pos 81) (Sat.Literal.pos 138) (positive_of_descriptor s 4100 (.lex permutation9 81) (by rfl)) (lex_9_81_prefix s) (positive_select s 81) (lex_9_81_image s)

theorem lex_9_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.pos 81), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation9 81 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4099) (Sat.Literal.pos 81) (Sat.Literal.pos 138) (lex_9_81_prefix s) (positive_select s 81) (lex_9_81_image s)

theorem lex_9_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.pos 4099)] :=
  (lex_9_81_gate s).prop _ (List.Mem.head _)

theorem lex_9_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.neg 81), (Sat.Literal.pos 138)] :=
  (lex_9_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.pos 81), (Sat.Literal.neg 138)] :=
  (lex_9_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.neg 81), (Sat.Literal.neg 138), (Sat.Literal.pos 4100)] :=
  (lex_9_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4099), (Sat.Literal.pos 81), (Sat.Literal.pos 138), (Sat.Literal.pos 4100)] :=
  (lex_9_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4100) = lexBefore s permutation9 80 := by
  exact (positive_lex_of_descriptor s 4100 permutation9 81 (by rfl)).trans ((lex_skipped s permutation9 80 81 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation9 80) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation9 80 by rw [image9_eq]; rfl))

theorem lex_9_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4101) (Sat.Literal.pos 4100) (Sat.Literal.pos 80) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation9 80 (assignment s)
    (Sat.Literal.pos 4101) (Sat.Literal.pos 4100) (Sat.Literal.pos 80) (Sat.Literal.pos 130) (positive_of_descriptor s 4101 (.lex permutation9 80) (by rfl)) (lex_9_80_prefix s) (positive_select s 80) (lex_9_80_image s)

theorem lex_9_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.pos 80), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation9 80 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4100) (Sat.Literal.pos 80) (Sat.Literal.pos 130) (lex_9_80_prefix s) (positive_select s 80) (lex_9_80_image s)

theorem lex_9_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.pos 4100)] :=
  (lex_9_80_gate s).prop _ (List.Mem.head _)

theorem lex_9_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.neg 80), (Sat.Literal.pos 130)] :=
  (lex_9_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.pos 80), (Sat.Literal.neg 130)] :=
  (lex_9_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.neg 80), (Sat.Literal.neg 130), (Sat.Literal.pos 4101)] :=
  (lex_9_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4100), (Sat.Literal.pos 80), (Sat.Literal.pos 130), (Sat.Literal.pos 4101)] :=
  (lex_9_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4101) = lexBefore s permutation9 79 := by
  exact (positive_lex_of_descriptor s 4101 permutation9 80 (by rfl)).trans ((lex_skipped s permutation9 79 80 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation9 79) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation9 79 by rw [image9_eq]; rfl))

theorem lex_9_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4102) (Sat.Literal.pos 4101) (Sat.Literal.pos 79) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation9 79 (assignment s)
    (Sat.Literal.pos 4102) (Sat.Literal.pos 4101) (Sat.Literal.pos 79) (Sat.Literal.pos 122) (positive_of_descriptor s 4102 (.lex permutation9 79) (by rfl)) (lex_9_79_prefix s) (positive_select s 79) (lex_9_79_image s)

theorem lex_9_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.pos 79), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation9 79 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4101) (Sat.Literal.pos 79) (Sat.Literal.pos 122) (lex_9_79_prefix s) (positive_select s 79) (lex_9_79_image s)

theorem lex_9_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.pos 4101)] :=
  (lex_9_79_gate s).prop _ (List.Mem.head _)

theorem lex_9_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.neg 79), (Sat.Literal.pos 122)] :=
  (lex_9_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.pos 79), (Sat.Literal.neg 122)] :=
  (lex_9_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.neg 79), (Sat.Literal.neg 122), (Sat.Literal.pos 4102)] :=
  (lex_9_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4101), (Sat.Literal.pos 79), (Sat.Literal.pos 122), (Sat.Literal.pos 4102)] :=
  (lex_9_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4102) = lexBefore s permutation9 78 := by
  exact (positive_lex_of_descriptor s 4102 permutation9 79 (by rfl)).trans ((lex_skipped s permutation9 78 79 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation9 78) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation9 78 by rw [image9_eq]; rfl))

theorem lex_9_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4103) (Sat.Literal.pos 4102) (Sat.Literal.pos 78) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation9 78 (assignment s)
    (Sat.Literal.pos 4103) (Sat.Literal.pos 4102) (Sat.Literal.pos 78) (Sat.Literal.pos 114) (positive_of_descriptor s 4103 (.lex permutation9 78) (by rfl)) (lex_9_78_prefix s) (positive_select s 78) (lex_9_78_image s)

theorem lex_9_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.pos 78), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation9 78 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4102) (Sat.Literal.pos 78) (Sat.Literal.pos 114) (lex_9_78_prefix s) (positive_select s 78) (lex_9_78_image s)

theorem lex_9_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.pos 4102)] :=
  (lex_9_78_gate s).prop _ (List.Mem.head _)

theorem lex_9_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.neg 78), (Sat.Literal.pos 114)] :=
  (lex_9_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.pos 78), (Sat.Literal.neg 114)] :=
  (lex_9_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.neg 78), (Sat.Literal.neg 114), (Sat.Literal.pos 4103)] :=
  (lex_9_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4102), (Sat.Literal.pos 78), (Sat.Literal.pos 114), (Sat.Literal.pos 4103)] :=
  (lex_9_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4103) = lexBefore s permutation9 77 := by
  exact (positive_lex_of_descriptor s 4103 permutation9 78 (by rfl)).trans ((lex_skipped s permutation9 77 78 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation9 77) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation9 77 by rw [image9_eq]; rfl))

theorem lex_9_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4104) (Sat.Literal.pos 4103) (Sat.Literal.pos 77) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation9 77 (assignment s)
    (Sat.Literal.pos 4104) (Sat.Literal.pos 4103) (Sat.Literal.pos 77) (Sat.Literal.pos 106) (positive_of_descriptor s 4104 (.lex permutation9 77) (by rfl)) (lex_9_77_prefix s) (positive_select s 77) (lex_9_77_image s)

theorem lex_9_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.pos 77), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation9 77 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4103) (Sat.Literal.pos 77) (Sat.Literal.pos 106) (lex_9_77_prefix s) (positive_select s 77) (lex_9_77_image s)

theorem lex_9_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.pos 4103)] :=
  (lex_9_77_gate s).prop _ (List.Mem.head _)

theorem lex_9_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.neg 77), (Sat.Literal.pos 106)] :=
  (lex_9_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.pos 77), (Sat.Literal.neg 106)] :=
  (lex_9_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.neg 77), (Sat.Literal.neg 106), (Sat.Literal.pos 4104)] :=
  (lex_9_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4103), (Sat.Literal.pos 77), (Sat.Literal.pos 106), (Sat.Literal.pos 4104)] :=
  (lex_9_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4104) = lexBefore s permutation9 76 := by
  exact (positive_lex_of_descriptor s 4104 permutation9 77 (by rfl)).trans ((lex_skipped s permutation9 76 77 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation9 76) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation9 76 by rw [image9_eq]; rfl))

theorem lex_9_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4105) (Sat.Literal.pos 4104) (Sat.Literal.pos 76) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation9 76 (assignment s)
    (Sat.Literal.pos 4105) (Sat.Literal.pos 4104) (Sat.Literal.pos 76) (Sat.Literal.pos 98) (positive_of_descriptor s 4105 (.lex permutation9 76) (by rfl)) (lex_9_76_prefix s) (positive_select s 76) (lex_9_76_image s)

theorem lex_9_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.pos 76), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation9 76 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4104) (Sat.Literal.pos 76) (Sat.Literal.pos 98) (lex_9_76_prefix s) (positive_select s 76) (lex_9_76_image s)

theorem lex_9_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.pos 4104)] :=
  (lex_9_76_gate s).prop _ (List.Mem.head _)

theorem lex_9_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.neg 76), (Sat.Literal.pos 98)] :=
  (lex_9_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.pos 76), (Sat.Literal.neg 98)] :=
  (lex_9_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.neg 76), (Sat.Literal.neg 98), (Sat.Literal.pos 4105)] :=
  (lex_9_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4104), (Sat.Literal.pos 76), (Sat.Literal.pos 98), (Sat.Literal.pos 4105)] :=
  (lex_9_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4105) = lexBefore s permutation9 75 := by
  exact (positive_lex_of_descriptor s 4105 permutation9 76 (by rfl)).trans ((lex_skipped s permutation9 75 76 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation9 75) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation9 75 by rw [image9_eq]; rfl))

theorem lex_9_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4106) (Sat.Literal.pos 4105) (Sat.Literal.pos 75) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation9 75 (assignment s)
    (Sat.Literal.pos 4106) (Sat.Literal.pos 4105) (Sat.Literal.pos 75) (Sat.Literal.pos 90) (positive_of_descriptor s 4106 (.lex permutation9 75) (by rfl)) (lex_9_75_prefix s) (positive_select s 75) (lex_9_75_image s)

theorem lex_9_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.pos 75), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation9 75 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4105) (Sat.Literal.pos 75) (Sat.Literal.pos 90) (lex_9_75_prefix s) (positive_select s 75) (lex_9_75_image s)

theorem lex_9_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.pos 4105)] :=
  (lex_9_75_gate s).prop _ (List.Mem.head _)

theorem lex_9_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.neg 75), (Sat.Literal.pos 90)] :=
  (lex_9_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.pos 75), (Sat.Literal.neg 90)] :=
  (lex_9_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.neg 75), (Sat.Literal.neg 90), (Sat.Literal.pos 4106)] :=
  (lex_9_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4105), (Sat.Literal.pos 75), (Sat.Literal.pos 90), (Sat.Literal.pos 4106)] :=
  (lex_9_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4106) = lexBefore s permutation9 74 := by
  exact (positive_lex_of_descriptor s 4106 permutation9 75 (by rfl)).trans ((lex_skipped s permutation9 74 75 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation9 74) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation9 74 by rw [image9_eq]; rfl))

theorem lex_9_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4107) (Sat.Literal.pos 4106) (Sat.Literal.pos 74) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation9 74 (assignment s)
    (Sat.Literal.pos 4107) (Sat.Literal.pos 4106) (Sat.Literal.pos 74) (Sat.Literal.pos 82) (positive_of_descriptor s 4107 (.lex permutation9 74) (by rfl)) (lex_9_74_prefix s) (positive_select s 74) (lex_9_74_image s)

theorem lex_9_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.pos 74), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation9 74 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4106) (Sat.Literal.pos 74) (Sat.Literal.pos 82) (lex_9_74_prefix s) (positive_select s 74) (lex_9_74_image s)

theorem lex_9_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.pos 4106)] :=
  (lex_9_74_gate s).prop _ (List.Mem.head _)

theorem lex_9_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.neg 74), (Sat.Literal.pos 82)] :=
  (lex_9_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.pos 74), (Sat.Literal.neg 82)] :=
  (lex_9_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.neg 74), (Sat.Literal.neg 82), (Sat.Literal.pos 4107)] :=
  (lex_9_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4106), (Sat.Literal.pos 74), (Sat.Literal.pos 82), (Sat.Literal.pos 4107)] :=
  (lex_9_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4107) = lexBefore s permutation9 73 := by
  exact (positive_lex_of_descriptor s 4107 permutation9 74 (by rfl)).trans ((lex_skipped s permutation9 73 74 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation9 73) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation9 73 by rw [image9_eq]; rfl))

theorem lex_9_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4108) (Sat.Literal.pos 4107) (Sat.Literal.pos 73) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation9 73 (assignment s)
    (Sat.Literal.pos 4108) (Sat.Literal.pos 4107) (Sat.Literal.pos 73) (Sat.Literal.pos 74) (positive_of_descriptor s 4108 (.lex permutation9 73) (by rfl)) (lex_9_73_prefix s) (positive_select s 73) (lex_9_73_image s)

theorem lex_9_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.pos 73), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation9 73 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4107) (Sat.Literal.pos 73) (Sat.Literal.pos 74) (lex_9_73_prefix s) (positive_select s 73) (lex_9_73_image s)

theorem lex_9_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.pos 4107)] :=
  (lex_9_73_gate s).prop _ (List.Mem.head _)

theorem lex_9_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.neg 73), (Sat.Literal.pos 74)] :=
  (lex_9_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.pos 73), (Sat.Literal.neg 74)] :=
  (lex_9_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.neg 73), (Sat.Literal.neg 74), (Sat.Literal.pos 4108)] :=
  (lex_9_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4107), (Sat.Literal.pos 73), (Sat.Literal.pos 74), (Sat.Literal.pos 4108)] :=
  (lex_9_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4108) = lexBefore s permutation9 72 := by
  exact (positive_lex_of_descriptor s 4108 permutation9 73 (by rfl)).trans ((lex_skipped s permutation9 72 73 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation9 72) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation9 72 by rw [image9_eq]; rfl))

theorem lex_9_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4109) (Sat.Literal.pos 4108) (Sat.Literal.pos 72) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation9 72 (assignment s)
    (Sat.Literal.pos 4109) (Sat.Literal.pos 4108) (Sat.Literal.pos 72) (Sat.Literal.pos 66) (positive_of_descriptor s 4109 (.lex permutation9 72) (by rfl)) (lex_9_72_prefix s) (positive_select s 72) (lex_9_72_image s)

theorem lex_9_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.pos 72), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation9 72 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4108) (Sat.Literal.pos 72) (Sat.Literal.pos 66) (lex_9_72_prefix s) (positive_select s 72) (lex_9_72_image s)

theorem lex_9_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.pos 4108)] :=
  (lex_9_72_gate s).prop _ (List.Mem.head _)

theorem lex_9_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.neg 72), (Sat.Literal.pos 66)] :=
  (lex_9_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.pos 72), (Sat.Literal.neg 66)] :=
  (lex_9_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.neg 72), (Sat.Literal.neg 66), (Sat.Literal.pos 4109)] :=
  (lex_9_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4108), (Sat.Literal.pos 72), (Sat.Literal.pos 66), (Sat.Literal.pos 4109)] :=
  (lex_9_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4109) = lexBefore s permutation9 71 := by
  exact (positive_lex_of_descriptor s 4109 permutation9 72 (by rfl)).trans ((lex_skipped s permutation9 71 72 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation9 71) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation9 71 by rw [image9_eq]; rfl))

theorem lex_9_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4110) (Sat.Literal.pos 4109) (Sat.Literal.pos 71) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation9 71 (assignment s)
    (Sat.Literal.pos 4110) (Sat.Literal.pos 4109) (Sat.Literal.pos 71) (Sat.Literal.pos 58) (positive_of_descriptor s 4110 (.lex permutation9 71) (by rfl)) (lex_9_71_prefix s) (positive_select s 71) (lex_9_71_image s)

theorem lex_9_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.pos 71), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation9 71 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4109) (Sat.Literal.pos 71) (Sat.Literal.pos 58) (lex_9_71_prefix s) (positive_select s 71) (lex_9_71_image s)

theorem lex_9_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.pos 4109)] :=
  (lex_9_71_gate s).prop _ (List.Mem.head _)

theorem lex_9_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.neg 71), (Sat.Literal.pos 58)] :=
  (lex_9_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.pos 71), (Sat.Literal.neg 58)] :=
  (lex_9_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.neg 71), (Sat.Literal.neg 58), (Sat.Literal.pos 4110)] :=
  (lex_9_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4109), (Sat.Literal.pos 71), (Sat.Literal.pos 58), (Sat.Literal.pos 4110)] :=
  (lex_9_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4110) = lexBefore s permutation9 70 := by
  exact (positive_lex_of_descriptor s 4110 permutation9 71 (by rfl)).trans ((lex_skipped s permutation9 70 71 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation9 70) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation9 70 by rw [image9_eq]; rfl))

theorem lex_9_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4111) (Sat.Literal.pos 4110) (Sat.Literal.pos 70) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation9 70 (assignment s)
    (Sat.Literal.pos 4111) (Sat.Literal.pos 4110) (Sat.Literal.pos 70) (Sat.Literal.pos 50) (positive_of_descriptor s 4111 (.lex permutation9 70) (by rfl)) (lex_9_70_prefix s) (positive_select s 70) (lex_9_70_image s)

theorem lex_9_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.pos 70), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation9 70 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4110) (Sat.Literal.pos 70) (Sat.Literal.pos 50) (lex_9_70_prefix s) (positive_select s 70) (lex_9_70_image s)

theorem lex_9_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.pos 4110)] :=
  (lex_9_70_gate s).prop _ (List.Mem.head _)

theorem lex_9_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.neg 70), (Sat.Literal.pos 50)] :=
  (lex_9_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.pos 70), (Sat.Literal.neg 50)] :=
  (lex_9_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.neg 70), (Sat.Literal.neg 50), (Sat.Literal.pos 4111)] :=
  (lex_9_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4110), (Sat.Literal.pos 70), (Sat.Literal.pos 50), (Sat.Literal.pos 4111)] :=
  (lex_9_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4111) = lexBefore s permutation9 69 := by
  exact (positive_lex_of_descriptor s 4111 permutation9 70 (by rfl)).trans ((lex_skipped s permutation9 69 70 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation9 69) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation9 69 by rw [image9_eq]; rfl))

theorem lex_9_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4112) (Sat.Literal.pos 4111) (Sat.Literal.pos 69) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation9 69 (assignment s)
    (Sat.Literal.pos 4112) (Sat.Literal.pos 4111) (Sat.Literal.pos 69) (Sat.Literal.pos 42) (positive_of_descriptor s 4112 (.lex permutation9 69) (by rfl)) (lex_9_69_prefix s) (positive_select s 69) (lex_9_69_image s)

theorem lex_9_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.pos 69), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation9 69 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4111) (Sat.Literal.pos 69) (Sat.Literal.pos 42) (lex_9_69_prefix s) (positive_select s 69) (lex_9_69_image s)

theorem lex_9_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.pos 4111)] :=
  (lex_9_69_gate s).prop _ (List.Mem.head _)

theorem lex_9_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.neg 69), (Sat.Literal.pos 42)] :=
  (lex_9_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.pos 69), (Sat.Literal.neg 42)] :=
  (lex_9_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.neg 69), (Sat.Literal.neg 42), (Sat.Literal.pos 4112)] :=
  (lex_9_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4111), (Sat.Literal.pos 69), (Sat.Literal.pos 42), (Sat.Literal.pos 4112)] :=
  (lex_9_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4112) = lexBefore s permutation9 68 := by
  exact (positive_lex_of_descriptor s 4112 permutation9 69 (by rfl)).trans ((lex_skipped s permutation9 68 69 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation9 68) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation9 68 by rw [image9_eq]; rfl))

theorem lex_9_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4113) (Sat.Literal.pos 4112) (Sat.Literal.pos 68) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation9 68 (assignment s)
    (Sat.Literal.pos 4113) (Sat.Literal.pos 4112) (Sat.Literal.pos 68) (Sat.Literal.pos 34) (positive_of_descriptor s 4113 (.lex permutation9 68) (by rfl)) (lex_9_68_prefix s) (positive_select s 68) (lex_9_68_image s)

theorem lex_9_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.pos 68), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation9 68 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4112) (Sat.Literal.pos 68) (Sat.Literal.pos 34) (lex_9_68_prefix s) (positive_select s 68) (lex_9_68_image s)

theorem lex_9_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.pos 4112)] :=
  (lex_9_68_gate s).prop _ (List.Mem.head _)

theorem lex_9_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.neg 68), (Sat.Literal.pos 34)] :=
  (lex_9_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.pos 68), (Sat.Literal.neg 34)] :=
  (lex_9_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.neg 68), (Sat.Literal.neg 34), (Sat.Literal.pos 4113)] :=
  (lex_9_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4112), (Sat.Literal.pos 68), (Sat.Literal.pos 34), (Sat.Literal.pos 4113)] :=
  (lex_9_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4113) = lexBefore s permutation9 67 := by
  exact (positive_lex_of_descriptor s 4113 permutation9 68 (by rfl)).trans ((lex_skipped s permutation9 67 68 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation9 67) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation9 67 by rw [image9_eq]; rfl))

theorem lex_9_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4114) (Sat.Literal.pos 4113) (Sat.Literal.pos 67) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation9 67 (assignment s)
    (Sat.Literal.pos 4114) (Sat.Literal.pos 4113) (Sat.Literal.pos 67) (Sat.Literal.pos 26) (positive_of_descriptor s 4114 (.lex permutation9 67) (by rfl)) (lex_9_67_prefix s) (positive_select s 67) (lex_9_67_image s)

theorem lex_9_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.pos 67), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation9 67 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4113) (Sat.Literal.pos 67) (Sat.Literal.pos 26) (lex_9_67_prefix s) (positive_select s 67) (lex_9_67_image s)

theorem lex_9_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.pos 4113)] :=
  (lex_9_67_gate s).prop _ (List.Mem.head _)

theorem lex_9_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.neg 67), (Sat.Literal.pos 26)] :=
  (lex_9_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.pos 67), (Sat.Literal.neg 26)] :=
  (lex_9_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.neg 67), (Sat.Literal.neg 26), (Sat.Literal.pos 4114)] :=
  (lex_9_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4113), (Sat.Literal.pos 67), (Sat.Literal.pos 26), (Sat.Literal.pos 4114)] :=
  (lex_9_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4114) = lexBefore s permutation9 66 := by
  exact (positive_lex_of_descriptor s 4114 permutation9 67 (by rfl)).trans ((lex_skipped s permutation9 66 67 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation9 66) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation9 66 by rw [image9_eq]; rfl))

theorem lex_9_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4115) (Sat.Literal.pos 4114) (Sat.Literal.pos 66) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation9 66 (assignment s)
    (Sat.Literal.pos 4115) (Sat.Literal.pos 4114) (Sat.Literal.pos 66) (Sat.Literal.pos 18) (positive_of_descriptor s 4115 (.lex permutation9 66) (by rfl)) (lex_9_66_prefix s) (positive_select s 66) (lex_9_66_image s)

theorem lex_9_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.pos 66), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation9 66 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4114) (Sat.Literal.pos 66) (Sat.Literal.pos 18) (lex_9_66_prefix s) (positive_select s 66) (lex_9_66_image s)

theorem lex_9_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.pos 4114)] :=
  (lex_9_66_gate s).prop _ (List.Mem.head _)

theorem lex_9_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.neg 66), (Sat.Literal.pos 18)] :=
  (lex_9_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.pos 66), (Sat.Literal.neg 18)] :=
  (lex_9_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.neg 66), (Sat.Literal.neg 18), (Sat.Literal.pos 4115)] :=
  (lex_9_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4114), (Sat.Literal.pos 66), (Sat.Literal.pos 18), (Sat.Literal.pos 4115)] :=
  (lex_9_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4115) = lexBefore s permutation9 65 := by
  exact (positive_lex_of_descriptor s 4115 permutation9 66 (by rfl)).trans ((lex_skipped s permutation9 65 66 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation9 65) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation9 65 by rw [image9_eq]; rfl))

theorem lex_9_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4116) (Sat.Literal.pos 4115) (Sat.Literal.pos 65) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation9 65 (assignment s)
    (Sat.Literal.pos 4116) (Sat.Literal.pos 4115) (Sat.Literal.pos 65) (Sat.Literal.pos 10) (positive_of_descriptor s 4116 (.lex permutation9 65) (by rfl)) (lex_9_65_prefix s) (positive_select s 65) (lex_9_65_image s)

theorem lex_9_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.pos 65), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation9 65 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4115) (Sat.Literal.pos 65) (Sat.Literal.pos 10) (lex_9_65_prefix s) (positive_select s 65) (lex_9_65_image s)

theorem lex_9_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.pos 4115)] :=
  (lex_9_65_gate s).prop _ (List.Mem.head _)

theorem lex_9_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.neg 65), (Sat.Literal.pos 10)] :=
  (lex_9_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.pos 65), (Sat.Literal.neg 10)] :=
  (lex_9_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.neg 65), (Sat.Literal.neg 10), (Sat.Literal.pos 4116)] :=
  (lex_9_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4115), (Sat.Literal.pos 65), (Sat.Literal.pos 10), (Sat.Literal.pos 4116)] :=
  (lex_9_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4116) = lexBefore s permutation9 64 := by
  exact (positive_lex_of_descriptor s 4116 permutation9 65 (by rfl)).trans ((lex_skipped s permutation9 64 65 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation9 64) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation9 64 by rw [image9_eq]; rfl))

theorem lex_9_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4117) (Sat.Literal.pos 4116) (Sat.Literal.pos 64) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation9 64 (assignment s)
    (Sat.Literal.pos 4117) (Sat.Literal.pos 4116) (Sat.Literal.pos 64) (Sat.Literal.pos 2) (positive_of_descriptor s 4117 (.lex permutation9 64) (by rfl)) (lex_9_64_prefix s) (positive_select s 64) (lex_9_64_image s)

theorem lex_9_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.pos 64), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation9 64 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4116) (Sat.Literal.pos 64) (Sat.Literal.pos 2) (lex_9_64_prefix s) (positive_select s 64) (lex_9_64_image s)

theorem lex_9_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.pos 4116)] :=
  (lex_9_64_gate s).prop _ (List.Mem.head _)

theorem lex_9_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.neg 64), (Sat.Literal.pos 2)] :=
  (lex_9_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.pos 64), (Sat.Literal.neg 2)] :=
  (lex_9_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.neg 64), (Sat.Literal.neg 2), (Sat.Literal.pos 4117)] :=
  (lex_9_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4116), (Sat.Literal.pos 64), (Sat.Literal.pos 2), (Sat.Literal.pos 4117)] :=
  (lex_9_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4117) = lexBefore s permutation9 63 := by
  exact (positive_lex_of_descriptor s 4117 permutation9 64 (by rfl)).trans ((lex_skipped s permutation9 63 64 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation9 63) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation9 63 by rw [image9_eq]; rfl))

theorem lex_9_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4118) (Sat.Literal.pos 4117) (Sat.Literal.pos 63) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation9 63 (assignment s)
    (Sat.Literal.pos 4118) (Sat.Literal.pos 4117) (Sat.Literal.pos 63) (Sat.Literal.pos 249) (positive_of_descriptor s 4118 (.lex permutation9 63) (by rfl)) (lex_9_63_prefix s) (positive_select s 63) (lex_9_63_image s)

theorem lex_9_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.pos 63), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation9 63 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4117) (Sat.Literal.pos 63) (Sat.Literal.pos 249) (lex_9_63_prefix s) (positive_select s 63) (lex_9_63_image s)

theorem lex_9_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.pos 4117)] :=
  (lex_9_63_gate s).prop _ (List.Mem.head _)

theorem lex_9_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.neg 63), (Sat.Literal.pos 249)] :=
  (lex_9_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.pos 63), (Sat.Literal.neg 249)] :=
  (lex_9_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.neg 63), (Sat.Literal.neg 249), (Sat.Literal.pos 4118)] :=
  (lex_9_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4117), (Sat.Literal.pos 63), (Sat.Literal.pos 249), (Sat.Literal.pos 4118)] :=
  (lex_9_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4118) = lexBefore s permutation9 62 := by
  exact (positive_lex_of_descriptor s 4118 permutation9 63 (by rfl)).trans ((lex_skipped s permutation9 62 63 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation9 62) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation9 62 by rw [image9_eq]; rfl))

theorem lex_9_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4119) (Sat.Literal.pos 4118) (Sat.Literal.pos 62) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation9 62 (assignment s)
    (Sat.Literal.pos 4119) (Sat.Literal.pos 4118) (Sat.Literal.pos 62) (Sat.Literal.pos 241) (positive_of_descriptor s 4119 (.lex permutation9 62) (by rfl)) (lex_9_62_prefix s) (positive_select s 62) (lex_9_62_image s)

theorem lex_9_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.pos 62), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation9 62 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4118) (Sat.Literal.pos 62) (Sat.Literal.pos 241) (lex_9_62_prefix s) (positive_select s 62) (lex_9_62_image s)

theorem lex_9_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.pos 4118)] :=
  (lex_9_62_gate s).prop _ (List.Mem.head _)

theorem lex_9_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.neg 62), (Sat.Literal.pos 241)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.pos 62), (Sat.Literal.neg 241)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.neg 62), (Sat.Literal.neg 241), (Sat.Literal.pos 4119)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4118), (Sat.Literal.pos 62), (Sat.Literal.pos 241), (Sat.Literal.pos 4119)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4119) = lexBefore s permutation9 61 := by
  exact (positive_lex_of_descriptor s 4119 permutation9 62 (by rfl)).trans ((lex_skipped s permutation9 61 62 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation9 61) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation9 61 by rw [image9_eq]; rfl))

theorem lex_9_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4120) (Sat.Literal.pos 4119) (Sat.Literal.pos 61) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation9 61 (assignment s)
    (Sat.Literal.pos 4120) (Sat.Literal.pos 4119) (Sat.Literal.pos 61) (Sat.Literal.pos 233) (positive_of_descriptor s 4120 (.lex permutation9 61) (by rfl)) (lex_9_61_prefix s) (positive_select s 61) (lex_9_61_image s)

theorem lex_9_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.pos 61), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation9 61 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4119) (Sat.Literal.pos 61) (Sat.Literal.pos 233) (lex_9_61_prefix s) (positive_select s 61) (lex_9_61_image s)

theorem lex_9_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.pos 4119)] :=
  (lex_9_61_gate s).prop _ (List.Mem.head _)

theorem lex_9_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.neg 61), (Sat.Literal.pos 233)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.pos 61), (Sat.Literal.neg 233)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.neg 61), (Sat.Literal.neg 233), (Sat.Literal.pos 4120)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4119), (Sat.Literal.pos 61), (Sat.Literal.pos 233), (Sat.Literal.pos 4120)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4120) = lexBefore s permutation9 60 := by
  exact (positive_lex_of_descriptor s 4120 permutation9 61 (by rfl)).trans ((lex_skipped s permutation9 60 61 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation9 60) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation9 60 by rw [image9_eq]; rfl))

theorem lex_9_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4121) (Sat.Literal.pos 4120) (Sat.Literal.pos 60) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation9 60 (assignment s)
    (Sat.Literal.pos 4121) (Sat.Literal.pos 4120) (Sat.Literal.pos 60) (Sat.Literal.pos 225) (positive_of_descriptor s 4121 (.lex permutation9 60) (by rfl)) (lex_9_60_prefix s) (positive_select s 60) (lex_9_60_image s)

theorem lex_9_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.pos 60), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation9 60 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4120) (Sat.Literal.pos 60) (Sat.Literal.pos 225) (lex_9_60_prefix s) (positive_select s 60) (lex_9_60_image s)

theorem lex_9_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.pos 4120)] :=
  (lex_9_60_gate s).prop _ (List.Mem.head _)

theorem lex_9_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.neg 60), (Sat.Literal.pos 225)] :=
  (lex_9_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.pos 60), (Sat.Literal.neg 225)] :=
  (lex_9_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.neg 60), (Sat.Literal.neg 225), (Sat.Literal.pos 4121)] :=
  (lex_9_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4120), (Sat.Literal.pos 60), (Sat.Literal.pos 225), (Sat.Literal.pos 4121)] :=
  (lex_9_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4121) = lexBefore s permutation9 59 := by
  exact (positive_lex_of_descriptor s 4121 permutation9 60 (by rfl)).trans ((lex_skipped s permutation9 59 60 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation9 59) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation9 59 by rw [image9_eq]; rfl))

theorem lex_9_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4122) (Sat.Literal.pos 4121) (Sat.Literal.pos 59) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation9 59 (assignment s)
    (Sat.Literal.pos 4122) (Sat.Literal.pos 4121) (Sat.Literal.pos 59) (Sat.Literal.pos 217) (positive_of_descriptor s 4122 (.lex permutation9 59) (by rfl)) (lex_9_59_prefix s) (positive_select s 59) (lex_9_59_image s)

theorem lex_9_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.pos 59), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation9 59 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4121) (Sat.Literal.pos 59) (Sat.Literal.pos 217) (lex_9_59_prefix s) (positive_select s 59) (lex_9_59_image s)

theorem lex_9_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.pos 4121)] :=
  (lex_9_59_gate s).prop _ (List.Mem.head _)

theorem lex_9_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.neg 59), (Sat.Literal.pos 217)] :=
  (lex_9_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.pos 59), (Sat.Literal.neg 217)] :=
  (lex_9_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.neg 59), (Sat.Literal.neg 217), (Sat.Literal.pos 4122)] :=
  (lex_9_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4121), (Sat.Literal.pos 59), (Sat.Literal.pos 217), (Sat.Literal.pos 4122)] :=
  (lex_9_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4122) = lexBefore s permutation9 58 := by
  exact (positive_lex_of_descriptor s 4122 permutation9 59 (by rfl)).trans ((lex_skipped s permutation9 58 59 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation9 58) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation9 58 by rw [image9_eq]; rfl))

theorem lex_9_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4123) (Sat.Literal.pos 4122) (Sat.Literal.pos 58) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation9 58 (assignment s)
    (Sat.Literal.pos 4123) (Sat.Literal.pos 4122) (Sat.Literal.pos 58) (Sat.Literal.pos 209) (positive_of_descriptor s 4123 (.lex permutation9 58) (by rfl)) (lex_9_58_prefix s) (positive_select s 58) (lex_9_58_image s)

theorem lex_9_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.pos 58), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation9 58 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4122) (Sat.Literal.pos 58) (Sat.Literal.pos 209) (lex_9_58_prefix s) (positive_select s 58) (lex_9_58_image s)

theorem lex_9_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.pos 4122)] :=
  (lex_9_58_gate s).prop _ (List.Mem.head _)

theorem lex_9_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.neg 58), (Sat.Literal.pos 209)] :=
  (lex_9_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.pos 58), (Sat.Literal.neg 209)] :=
  (lex_9_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.neg 58), (Sat.Literal.neg 209), (Sat.Literal.pos 4123)] :=
  (lex_9_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4122), (Sat.Literal.pos 58), (Sat.Literal.pos 209), (Sat.Literal.pos 4123)] :=
  (lex_9_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4123) = lexBefore s permutation9 57 := by
  exact (positive_lex_of_descriptor s 4123 permutation9 58 (by rfl)).trans ((lex_skipped s permutation9 57 58 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation9 57) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation9 57 by rw [image9_eq]; rfl))

theorem lex_9_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4124) (Sat.Literal.pos 4123) (Sat.Literal.pos 57) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation9 57 (assignment s)
    (Sat.Literal.pos 4124) (Sat.Literal.pos 4123) (Sat.Literal.pos 57) (Sat.Literal.pos 201) (positive_of_descriptor s 4124 (.lex permutation9 57) (by rfl)) (lex_9_57_prefix s) (positive_select s 57) (lex_9_57_image s)

theorem lex_9_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.pos 57), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation9 57 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4123) (Sat.Literal.pos 57) (Sat.Literal.pos 201) (lex_9_57_prefix s) (positive_select s 57) (lex_9_57_image s)

theorem lex_9_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.pos 4123)] :=
  (lex_9_57_gate s).prop _ (List.Mem.head _)

theorem lex_9_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.neg 57), (Sat.Literal.pos 201)] :=
  (lex_9_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.pos 57), (Sat.Literal.neg 201)] :=
  (lex_9_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.neg 57), (Sat.Literal.neg 201), (Sat.Literal.pos 4124)] :=
  (lex_9_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4123), (Sat.Literal.pos 57), (Sat.Literal.pos 201), (Sat.Literal.pos 4124)] :=
  (lex_9_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_9_156_gate

end Crown.CertificateData
