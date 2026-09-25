import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_13_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5024) = lexBefore s permutation13 156 := by
  exact (positive_lex_of_descriptor s 5024 permutation13 157 (by rfl)).trans ((lex_skipped s permutation13 156 157 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation13 156) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation13 156 by rw [image13_eq]; rfl))

theorem lex_13_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5025) (Sat.Literal.pos 5024) (Sat.Literal.pos 156) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation13 156 (assignment s)
    (Sat.Literal.pos 5025) (Sat.Literal.pos 5024) (Sat.Literal.pos 156) (Sat.Literal.pos 78) (positive_of_descriptor s 5025 (.lex permutation13 156) (by rfl)) (lex_13_156_prefix s) (positive_select s 156) (lex_13_156_image s)

theorem lex_13_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.pos 156), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation13 156 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5024) (Sat.Literal.pos 156) (Sat.Literal.pos 78) (lex_13_156_prefix s) (positive_select s 156) (lex_13_156_image s)

theorem lex_13_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.pos 5024)] :=
  (lex_13_156_gate s).prop _ (List.Mem.head _)

theorem lex_13_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.neg 156), (Sat.Literal.pos 78)] :=
  (lex_13_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.pos 156), (Sat.Literal.neg 78)] :=
  (lex_13_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.neg 156), (Sat.Literal.neg 78), (Sat.Literal.pos 5025)] :=
  (lex_13_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.pos 156), (Sat.Literal.pos 78), (Sat.Literal.pos 5025)] :=
  (lex_13_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5025) = lexBefore s permutation13 155 := by
  exact (positive_lex_of_descriptor s 5025 permutation13 156 (by rfl)).trans ((lex_skipped s permutation13 155 156 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation13 155) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation13 155 by rw [image13_eq]; rfl))

theorem lex_13_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5026) (Sat.Literal.pos 5025) (Sat.Literal.pos 155) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation13 155 (assignment s)
    (Sat.Literal.pos 5026) (Sat.Literal.pos 5025) (Sat.Literal.pos 155) (Sat.Literal.pos 205) (positive_of_descriptor s 5026 (.lex permutation13 155) (by rfl)) (lex_13_155_prefix s) (positive_select s 155) (lex_13_155_image s)

theorem lex_13_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.pos 155), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation13 155 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5025) (Sat.Literal.pos 155) (Sat.Literal.pos 205) (lex_13_155_prefix s) (positive_select s 155) (lex_13_155_image s)

theorem lex_13_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.pos 5025)] :=
  (lex_13_155_gate s).prop _ (List.Mem.head _)

theorem lex_13_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.neg 155), (Sat.Literal.pos 205)] :=
  (lex_13_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.pos 155), (Sat.Literal.neg 205)] :=
  (lex_13_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.neg 155), (Sat.Literal.neg 205), (Sat.Literal.pos 5026)] :=
  (lex_13_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5025), (Sat.Literal.pos 155), (Sat.Literal.pos 205), (Sat.Literal.pos 5026)] :=
  (lex_13_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5026) = lexBefore s permutation13 154 := by
  exact (positive_lex_of_descriptor s 5026 permutation13 155 (by rfl)).trans ((lex_skipped s permutation13 154 155 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation13 154) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation13 154 by rw [image13_eq]; rfl))

theorem lex_13_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5027) (Sat.Literal.pos 5026) (Sat.Literal.pos 154) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation13 154 (assignment s)
    (Sat.Literal.pos 5027) (Sat.Literal.pos 5026) (Sat.Literal.pos 154) (Sat.Literal.pos 77) (positive_of_descriptor s 5027 (.lex permutation13 154) (by rfl)) (lex_13_154_prefix s) (positive_select s 154) (lex_13_154_image s)

theorem lex_13_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.pos 154), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation13 154 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5026) (Sat.Literal.pos 154) (Sat.Literal.pos 77) (lex_13_154_prefix s) (positive_select s 154) (lex_13_154_image s)

theorem lex_13_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.pos 5026)] :=
  (lex_13_154_gate s).prop _ (List.Mem.head _)

theorem lex_13_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.neg 154), (Sat.Literal.pos 77)] :=
  (lex_13_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.pos 154), (Sat.Literal.neg 77)] :=
  (lex_13_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.neg 154), (Sat.Literal.neg 77), (Sat.Literal.pos 5027)] :=
  (lex_13_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5026), (Sat.Literal.pos 154), (Sat.Literal.pos 77), (Sat.Literal.pos 5027)] :=
  (lex_13_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5027) = lexBefore s permutation13 153 := by
  exact (positive_lex_of_descriptor s 5027 permutation13 154 (by rfl)).trans ((lex_skipped s permutation13 153 154 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation13 153) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation13 153 by rw [image13_eq]; rfl))

theorem lex_13_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5028) (Sat.Literal.pos 5027) (Sat.Literal.pos 153) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation13 153 (assignment s)
    (Sat.Literal.pos 5028) (Sat.Literal.pos 5027) (Sat.Literal.pos 153) (Sat.Literal.pos 204) (positive_of_descriptor s 5028 (.lex permutation13 153) (by rfl)) (lex_13_153_prefix s) (positive_select s 153) (lex_13_153_image s)

theorem lex_13_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.pos 153), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation13 153 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5027) (Sat.Literal.pos 153) (Sat.Literal.pos 204) (lex_13_153_prefix s) (positive_select s 153) (lex_13_153_image s)

theorem lex_13_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.pos 5027)] :=
  (lex_13_153_gate s).prop _ (List.Mem.head _)

theorem lex_13_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.neg 153), (Sat.Literal.pos 204)] :=
  (lex_13_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.pos 153), (Sat.Literal.neg 204)] :=
  (lex_13_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.neg 153), (Sat.Literal.neg 204), (Sat.Literal.pos 5028)] :=
  (lex_13_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5027), (Sat.Literal.pos 153), (Sat.Literal.pos 204), (Sat.Literal.pos 5028)] :=
  (lex_13_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5028) = lexBefore s permutation13 152 := by
  exact (positive_lex_of_descriptor s 5028 permutation13 153 (by rfl)).trans ((lex_skipped s permutation13 152 153 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation13 152) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation13 152 by rw [image13_eq]; rfl))

theorem lex_13_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5029) (Sat.Literal.pos 5028) (Sat.Literal.pos 152) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation13 152 (assignment s)
    (Sat.Literal.pos 5029) (Sat.Literal.pos 5028) (Sat.Literal.pos 152) (Sat.Literal.pos 76) (positive_of_descriptor s 5029 (.lex permutation13 152) (by rfl)) (lex_13_152_prefix s) (positive_select s 152) (lex_13_152_image s)

theorem lex_13_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.pos 152), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation13 152 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5028) (Sat.Literal.pos 152) (Sat.Literal.pos 76) (lex_13_152_prefix s) (positive_select s 152) (lex_13_152_image s)

theorem lex_13_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.pos 5028)] :=
  (lex_13_152_gate s).prop _ (List.Mem.head _)

theorem lex_13_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.neg 152), (Sat.Literal.pos 76)] :=
  (lex_13_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.pos 152), (Sat.Literal.neg 76)] :=
  (lex_13_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.neg 152), (Sat.Literal.neg 76), (Sat.Literal.pos 5029)] :=
  (lex_13_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5028), (Sat.Literal.pos 152), (Sat.Literal.pos 76), (Sat.Literal.pos 5029)] :=
  (lex_13_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5029) = lexBefore s permutation13 151 := by
  exact (positive_lex_of_descriptor s 5029 permutation13 152 (by rfl)).trans ((lex_skipped s permutation13 151 152 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation13 151) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation13 151 by rw [image13_eq]; rfl))

theorem lex_13_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5030) (Sat.Literal.pos 5029) (Sat.Literal.pos 151) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation13 151 (assignment s)
    (Sat.Literal.pos 5030) (Sat.Literal.pos 5029) (Sat.Literal.pos 151) (Sat.Literal.pos 203) (positive_of_descriptor s 5030 (.lex permutation13 151) (by rfl)) (lex_13_151_prefix s) (positive_select s 151) (lex_13_151_image s)

theorem lex_13_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.pos 151), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation13 151 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5029) (Sat.Literal.pos 151) (Sat.Literal.pos 203) (lex_13_151_prefix s) (positive_select s 151) (lex_13_151_image s)

theorem lex_13_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.pos 5029)] :=
  (lex_13_151_gate s).prop _ (List.Mem.head _)

theorem lex_13_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.neg 151), (Sat.Literal.pos 203)] :=
  (lex_13_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.pos 151), (Sat.Literal.neg 203)] :=
  (lex_13_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.neg 151), (Sat.Literal.neg 203), (Sat.Literal.pos 5030)] :=
  (lex_13_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5029), (Sat.Literal.pos 151), (Sat.Literal.pos 203), (Sat.Literal.pos 5030)] :=
  (lex_13_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5030) = lexBefore s permutation13 150 := by
  exact (positive_lex_of_descriptor s 5030 permutation13 151 (by rfl)).trans ((lex_skipped s permutation13 150 151 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation13 150) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation13 150 by rw [image13_eq]; rfl))

theorem lex_13_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5031) (Sat.Literal.pos 5030) (Sat.Literal.pos 150) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation13 150 (assignment s)
    (Sat.Literal.pos 5031) (Sat.Literal.pos 5030) (Sat.Literal.pos 150) (Sat.Literal.pos 75) (positive_of_descriptor s 5031 (.lex permutation13 150) (by rfl)) (lex_13_150_prefix s) (positive_select s 150) (lex_13_150_image s)

theorem lex_13_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.pos 150), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation13 150 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5030) (Sat.Literal.pos 150) (Sat.Literal.pos 75) (lex_13_150_prefix s) (positive_select s 150) (lex_13_150_image s)

theorem lex_13_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.pos 5030)] :=
  (lex_13_150_gate s).prop _ (List.Mem.head _)

theorem lex_13_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.neg 150), (Sat.Literal.pos 75)] :=
  (lex_13_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.pos 150), (Sat.Literal.neg 75)] :=
  (lex_13_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.neg 150), (Sat.Literal.neg 75), (Sat.Literal.pos 5031)] :=
  (lex_13_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5030), (Sat.Literal.pos 150), (Sat.Literal.pos 75), (Sat.Literal.pos 5031)] :=
  (lex_13_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5031) = lexBefore s permutation13 149 := by
  exact (positive_lex_of_descriptor s 5031 permutation13 150 (by rfl)).trans ((lex_skipped s permutation13 149 150 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation13 149) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation13 149 by rw [image13_eq]; rfl))

theorem lex_13_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5032) (Sat.Literal.pos 5031) (Sat.Literal.pos 149) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation13 149 (assignment s)
    (Sat.Literal.pos 5032) (Sat.Literal.pos 5031) (Sat.Literal.pos 149) (Sat.Literal.pos 202) (positive_of_descriptor s 5032 (.lex permutation13 149) (by rfl)) (lex_13_149_prefix s) (positive_select s 149) (lex_13_149_image s)

theorem lex_13_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.pos 149), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation13 149 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5031) (Sat.Literal.pos 149) (Sat.Literal.pos 202) (lex_13_149_prefix s) (positive_select s 149) (lex_13_149_image s)

theorem lex_13_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.pos 5031)] :=
  (lex_13_149_gate s).prop _ (List.Mem.head _)

theorem lex_13_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.neg 149), (Sat.Literal.pos 202)] :=
  (lex_13_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.pos 149), (Sat.Literal.neg 202)] :=
  (lex_13_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.neg 149), (Sat.Literal.neg 202), (Sat.Literal.pos 5032)] :=
  (lex_13_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5031), (Sat.Literal.pos 149), (Sat.Literal.pos 202), (Sat.Literal.pos 5032)] :=
  (lex_13_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5032) = lexBefore s permutation13 148 := by
  exact (positive_lex_of_descriptor s 5032 permutation13 149 (by rfl)).trans ((lex_skipped s permutation13 148 149 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation13 148) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation13 148 by rw [image13_eq]; rfl))

theorem lex_13_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5033) (Sat.Literal.pos 5032) (Sat.Literal.pos 148) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation13 148 (assignment s)
    (Sat.Literal.pos 5033) (Sat.Literal.pos 5032) (Sat.Literal.pos 148) (Sat.Literal.pos 74) (positive_of_descriptor s 5033 (.lex permutation13 148) (by rfl)) (lex_13_148_prefix s) (positive_select s 148) (lex_13_148_image s)

theorem lex_13_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.pos 148), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation13 148 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5032) (Sat.Literal.pos 148) (Sat.Literal.pos 74) (lex_13_148_prefix s) (positive_select s 148) (lex_13_148_image s)

theorem lex_13_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.pos 5032)] :=
  (lex_13_148_gate s).prop _ (List.Mem.head _)

theorem lex_13_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.neg 148), (Sat.Literal.pos 74)] :=
  (lex_13_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.pos 148), (Sat.Literal.neg 74)] :=
  (lex_13_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.neg 148), (Sat.Literal.neg 74), (Sat.Literal.pos 5033)] :=
  (lex_13_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5032), (Sat.Literal.pos 148), (Sat.Literal.pos 74), (Sat.Literal.pos 5033)] :=
  (lex_13_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5033) = lexBefore s permutation13 147 := by
  exact (positive_lex_of_descriptor s 5033 permutation13 148 (by rfl)).trans ((lex_skipped s permutation13 147 148 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation13 147) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation13 147 by rw [image13_eq]; rfl))

theorem lex_13_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5034) (Sat.Literal.pos 5033) (Sat.Literal.pos 147) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation13 147 (assignment s)
    (Sat.Literal.pos 5034) (Sat.Literal.pos 5033) (Sat.Literal.pos 147) (Sat.Literal.pos 201) (positive_of_descriptor s 5034 (.lex permutation13 147) (by rfl)) (lex_13_147_prefix s) (positive_select s 147) (lex_13_147_image s)

theorem lex_13_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.pos 147), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation13 147 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5033) (Sat.Literal.pos 147) (Sat.Literal.pos 201) (lex_13_147_prefix s) (positive_select s 147) (lex_13_147_image s)

theorem lex_13_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.pos 5033)] :=
  (lex_13_147_gate s).prop _ (List.Mem.head _)

theorem lex_13_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.neg 147), (Sat.Literal.pos 201)] :=
  (lex_13_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.pos 147), (Sat.Literal.neg 201)] :=
  (lex_13_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.neg 147), (Sat.Literal.neg 201), (Sat.Literal.pos 5034)] :=
  (lex_13_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5033), (Sat.Literal.pos 147), (Sat.Literal.pos 201), (Sat.Literal.pos 5034)] :=
  (lex_13_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5034) = lexBefore s permutation13 146 := by
  exact (positive_lex_of_descriptor s 5034 permutation13 147 (by rfl)).trans ((lex_skipped s permutation13 146 147 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation13 146) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation13 146 by rw [image13_eq]; rfl))

theorem lex_13_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5035) (Sat.Literal.pos 5034) (Sat.Literal.pos 146) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation13 146 (assignment s)
    (Sat.Literal.pos 5035) (Sat.Literal.pos 5034) (Sat.Literal.pos 146) (Sat.Literal.pos 73) (positive_of_descriptor s 5035 (.lex permutation13 146) (by rfl)) (lex_13_146_prefix s) (positive_select s 146) (lex_13_146_image s)

theorem lex_13_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.pos 146), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation13 146 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5034) (Sat.Literal.pos 146) (Sat.Literal.pos 73) (lex_13_146_prefix s) (positive_select s 146) (lex_13_146_image s)

theorem lex_13_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.pos 5034)] :=
  (lex_13_146_gate s).prop _ (List.Mem.head _)

theorem lex_13_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.neg 146), (Sat.Literal.pos 73)] :=
  (lex_13_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.pos 146), (Sat.Literal.neg 73)] :=
  (lex_13_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.neg 146), (Sat.Literal.neg 73), (Sat.Literal.pos 5035)] :=
  (lex_13_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5034), (Sat.Literal.pos 146), (Sat.Literal.pos 73), (Sat.Literal.pos 5035)] :=
  (lex_13_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5035) = lexBefore s permutation13 145 := by
  exact (positive_lex_of_descriptor s 5035 permutation13 146 (by rfl)).trans ((lex_skipped s permutation13 145 146 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation13 145) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation13 145 by rw [image13_eq]; rfl))

theorem lex_13_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5036) (Sat.Literal.pos 5035) (Sat.Literal.pos 145) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation13 145 (assignment s)
    (Sat.Literal.pos 5036) (Sat.Literal.pos 5035) (Sat.Literal.pos 145) (Sat.Literal.pos 200) (positive_of_descriptor s 5036 (.lex permutation13 145) (by rfl)) (lex_13_145_prefix s) (positive_select s 145) (lex_13_145_image s)

theorem lex_13_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.pos 145), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation13 145 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5035) (Sat.Literal.pos 145) (Sat.Literal.pos 200) (lex_13_145_prefix s) (positive_select s 145) (lex_13_145_image s)

theorem lex_13_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.pos 5035)] :=
  (lex_13_145_gate s).prop _ (List.Mem.head _)

theorem lex_13_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.neg 145), (Sat.Literal.pos 200)] :=
  (lex_13_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.pos 145), (Sat.Literal.neg 200)] :=
  (lex_13_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.neg 145), (Sat.Literal.neg 200), (Sat.Literal.pos 5036)] :=
  (lex_13_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5035), (Sat.Literal.pos 145), (Sat.Literal.pos 200), (Sat.Literal.pos 5036)] :=
  (lex_13_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5036) = lexBefore s permutation13 144 := by
  exact (positive_lex_of_descriptor s 5036 permutation13 145 (by rfl)).trans ((lex_skipped s permutation13 144 145 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation13 144) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation13 144 by rw [image13_eq]; rfl))

theorem lex_13_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5037) (Sat.Literal.pos 5036) (Sat.Literal.pos 144) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation13 144 (assignment s)
    (Sat.Literal.pos 5037) (Sat.Literal.pos 5036) (Sat.Literal.pos 144) (Sat.Literal.pos 72) (positive_of_descriptor s 5037 (.lex permutation13 144) (by rfl)) (lex_13_144_prefix s) (positive_select s 144) (lex_13_144_image s)

theorem lex_13_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.pos 144), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation13 144 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5036) (Sat.Literal.pos 144) (Sat.Literal.pos 72) (lex_13_144_prefix s) (positive_select s 144) (lex_13_144_image s)

theorem lex_13_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.pos 5036)] :=
  (lex_13_144_gate s).prop _ (List.Mem.head _)

theorem lex_13_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.neg 144), (Sat.Literal.pos 72)] :=
  (lex_13_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.pos 144), (Sat.Literal.neg 72)] :=
  (lex_13_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.neg 144), (Sat.Literal.neg 72), (Sat.Literal.pos 5037)] :=
  (lex_13_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5036), (Sat.Literal.pos 144), (Sat.Literal.pos 72), (Sat.Literal.pos 5037)] :=
  (lex_13_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5037) = lexBefore s permutation13 143 := by
  exact (positive_lex_of_descriptor s 5037 permutation13 144 (by rfl)).trans ((lex_skipped s permutation13 143 144 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation13 143) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation13 143 by rw [image13_eq]; rfl))

theorem lex_13_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5038) (Sat.Literal.pos 5037) (Sat.Literal.pos 143) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation13 143 (assignment s)
    (Sat.Literal.pos 5038) (Sat.Literal.pos 5037) (Sat.Literal.pos 143) (Sat.Literal.pos 199) (positive_of_descriptor s 5038 (.lex permutation13 143) (by rfl)) (lex_13_143_prefix s) (positive_select s 143) (lex_13_143_image s)

theorem lex_13_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.pos 143), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation13 143 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5037) (Sat.Literal.pos 143) (Sat.Literal.pos 199) (lex_13_143_prefix s) (positive_select s 143) (lex_13_143_image s)

theorem lex_13_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.pos 5037)] :=
  (lex_13_143_gate s).prop _ (List.Mem.head _)

theorem lex_13_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.neg 143), (Sat.Literal.pos 199)] :=
  (lex_13_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.pos 143), (Sat.Literal.neg 199)] :=
  (lex_13_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.neg 143), (Sat.Literal.neg 199), (Sat.Literal.pos 5038)] :=
  (lex_13_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5037), (Sat.Literal.pos 143), (Sat.Literal.pos 199), (Sat.Literal.pos 5038)] :=
  (lex_13_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5038) = lexBefore s permutation13 142 := by
  exact (positive_lex_of_descriptor s 5038 permutation13 143 (by rfl)).trans ((lex_skipped s permutation13 142 143 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation13 142) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation13 142 by rw [image13_eq]; rfl))

theorem lex_13_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5039) (Sat.Literal.pos 5038) (Sat.Literal.pos 142) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation13 142 (assignment s)
    (Sat.Literal.pos 5039) (Sat.Literal.pos 5038) (Sat.Literal.pos 142) (Sat.Literal.pos 71) (positive_of_descriptor s 5039 (.lex permutation13 142) (by rfl)) (lex_13_142_prefix s) (positive_select s 142) (lex_13_142_image s)

theorem lex_13_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.pos 142), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation13 142 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5038) (Sat.Literal.pos 142) (Sat.Literal.pos 71) (lex_13_142_prefix s) (positive_select s 142) (lex_13_142_image s)

theorem lex_13_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.pos 5038)] :=
  (lex_13_142_gate s).prop _ (List.Mem.head _)

theorem lex_13_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.neg 142), (Sat.Literal.pos 71)] :=
  (lex_13_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.pos 142), (Sat.Literal.neg 71)] :=
  (lex_13_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.neg 142), (Sat.Literal.neg 71), (Sat.Literal.pos 5039)] :=
  (lex_13_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5038), (Sat.Literal.pos 142), (Sat.Literal.pos 71), (Sat.Literal.pos 5039)] :=
  (lex_13_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5039) = lexBefore s permutation13 141 := by
  exact (positive_lex_of_descriptor s 5039 permutation13 142 (by rfl)).trans ((lex_skipped s permutation13 141 142 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation13 141) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation13 141 by rw [image13_eq]; rfl))

theorem lex_13_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5040) (Sat.Literal.pos 5039) (Sat.Literal.pos 141) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation13 141 (assignment s)
    (Sat.Literal.pos 5040) (Sat.Literal.pos 5039) (Sat.Literal.pos 141) (Sat.Literal.pos 198) (positive_of_descriptor s 5040 (.lex permutation13 141) (by rfl)) (lex_13_141_prefix s) (positive_select s 141) (lex_13_141_image s)

theorem lex_13_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.pos 141), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation13 141 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5039) (Sat.Literal.pos 141) (Sat.Literal.pos 198) (lex_13_141_prefix s) (positive_select s 141) (lex_13_141_image s)

theorem lex_13_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.pos 5039)] :=
  (lex_13_141_gate s).prop _ (List.Mem.head _)

theorem lex_13_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.neg 141), (Sat.Literal.pos 198)] :=
  (lex_13_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.pos 141), (Sat.Literal.neg 198)] :=
  (lex_13_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.neg 141), (Sat.Literal.neg 198), (Sat.Literal.pos 5040)] :=
  (lex_13_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5039), (Sat.Literal.pos 141), (Sat.Literal.pos 198), (Sat.Literal.pos 5040)] :=
  (lex_13_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5040) = lexBefore s permutation13 140 := by
  exact (positive_lex_of_descriptor s 5040 permutation13 141 (by rfl)).trans ((lex_skipped s permutation13 140 141 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation13 140) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation13 140 by rw [image13_eq]; rfl))

theorem lex_13_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5041) (Sat.Literal.pos 5040) (Sat.Literal.pos 140) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation13 140 (assignment s)
    (Sat.Literal.pos 5041) (Sat.Literal.pos 5040) (Sat.Literal.pos 140) (Sat.Literal.pos 70) (positive_of_descriptor s 5041 (.lex permutation13 140) (by rfl)) (lex_13_140_prefix s) (positive_select s 140) (lex_13_140_image s)

theorem lex_13_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.pos 140), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation13 140 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5040) (Sat.Literal.pos 140) (Sat.Literal.pos 70) (lex_13_140_prefix s) (positive_select s 140) (lex_13_140_image s)

theorem lex_13_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.pos 5040)] :=
  (lex_13_140_gate s).prop _ (List.Mem.head _)

theorem lex_13_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.neg 140), (Sat.Literal.pos 70)] :=
  (lex_13_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.pos 140), (Sat.Literal.neg 70)] :=
  (lex_13_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.neg 140), (Sat.Literal.neg 70), (Sat.Literal.pos 5041)] :=
  (lex_13_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5040), (Sat.Literal.pos 140), (Sat.Literal.pos 70), (Sat.Literal.pos 5041)] :=
  (lex_13_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5041) = lexBefore s permutation13 139 := by
  exact (positive_lex_of_descriptor s 5041 permutation13 140 (by rfl)).trans ((lex_skipped s permutation13 139 140 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation13 139) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation13 139 by rw [image13_eq]; rfl))

theorem lex_13_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5042) (Sat.Literal.pos 5041) (Sat.Literal.pos 139) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation13 139 (assignment s)
    (Sat.Literal.pos 5042) (Sat.Literal.pos 5041) (Sat.Literal.pos 139) (Sat.Literal.pos 197) (positive_of_descriptor s 5042 (.lex permutation13 139) (by rfl)) (lex_13_139_prefix s) (positive_select s 139) (lex_13_139_image s)

theorem lex_13_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.pos 139), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation13 139 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5041) (Sat.Literal.pos 139) (Sat.Literal.pos 197) (lex_13_139_prefix s) (positive_select s 139) (lex_13_139_image s)

theorem lex_13_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.pos 5041)] :=
  (lex_13_139_gate s).prop _ (List.Mem.head _)

theorem lex_13_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.neg 139), (Sat.Literal.pos 197)] :=
  (lex_13_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.pos 139), (Sat.Literal.neg 197)] :=
  (lex_13_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.neg 139), (Sat.Literal.neg 197), (Sat.Literal.pos 5042)] :=
  (lex_13_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5041), (Sat.Literal.pos 139), (Sat.Literal.pos 197), (Sat.Literal.pos 5042)] :=
  (lex_13_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5042) = lexBefore s permutation13 138 := by
  exact (positive_lex_of_descriptor s 5042 permutation13 139 (by rfl)).trans ((lex_skipped s permutation13 138 139 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation13 138) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation13 138 by rw [image13_eq]; rfl))

theorem lex_13_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5043) (Sat.Literal.pos 5042) (Sat.Literal.pos 138) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation13 138 (assignment s)
    (Sat.Literal.pos 5043) (Sat.Literal.pos 5042) (Sat.Literal.pos 138) (Sat.Literal.pos 69) (positive_of_descriptor s 5043 (.lex permutation13 138) (by rfl)) (lex_13_138_prefix s) (positive_select s 138) (lex_13_138_image s)

theorem lex_13_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.pos 138), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation13 138 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5042) (Sat.Literal.pos 138) (Sat.Literal.pos 69) (lex_13_138_prefix s) (positive_select s 138) (lex_13_138_image s)

theorem lex_13_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.pos 5042)] :=
  (lex_13_138_gate s).prop _ (List.Mem.head _)

theorem lex_13_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.neg 138), (Sat.Literal.pos 69)] :=
  (lex_13_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.pos 138), (Sat.Literal.neg 69)] :=
  (lex_13_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.neg 138), (Sat.Literal.neg 69), (Sat.Literal.pos 5043)] :=
  (lex_13_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5042), (Sat.Literal.pos 138), (Sat.Literal.pos 69), (Sat.Literal.pos 5043)] :=
  (lex_13_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5043) = lexBefore s permutation13 137 := by
  exact (positive_lex_of_descriptor s 5043 permutation13 138 (by rfl)).trans ((lex_skipped s permutation13 137 138 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation13 137) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation13 137 by rw [image13_eq]; rfl))

theorem lex_13_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5044) (Sat.Literal.pos 5043) (Sat.Literal.pos 137) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation13 137 (assignment s)
    (Sat.Literal.pos 5044) (Sat.Literal.pos 5043) (Sat.Literal.pos 137) (Sat.Literal.pos 196) (positive_of_descriptor s 5044 (.lex permutation13 137) (by rfl)) (lex_13_137_prefix s) (positive_select s 137) (lex_13_137_image s)

theorem lex_13_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.pos 137), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation13 137 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5043) (Sat.Literal.pos 137) (Sat.Literal.pos 196) (lex_13_137_prefix s) (positive_select s 137) (lex_13_137_image s)

theorem lex_13_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.pos 5043)] :=
  (lex_13_137_gate s).prop _ (List.Mem.head _)

theorem lex_13_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.neg 137), (Sat.Literal.pos 196)] :=
  (lex_13_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.pos 137), (Sat.Literal.neg 196)] :=
  (lex_13_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.neg 137), (Sat.Literal.neg 196), (Sat.Literal.pos 5044)] :=
  (lex_13_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5043), (Sat.Literal.pos 137), (Sat.Literal.pos 196), (Sat.Literal.pos 5044)] :=
  (lex_13_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5044) = lexBefore s permutation13 136 := by
  exact (positive_lex_of_descriptor s 5044 permutation13 137 (by rfl)).trans ((lex_skipped s permutation13 136 137 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation13 136) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation13 136 by rw [image13_eq]; rfl))

theorem lex_13_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5045) (Sat.Literal.pos 5044) (Sat.Literal.pos 136) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation13 136 (assignment s)
    (Sat.Literal.pos 5045) (Sat.Literal.pos 5044) (Sat.Literal.pos 136) (Sat.Literal.pos 68) (positive_of_descriptor s 5045 (.lex permutation13 136) (by rfl)) (lex_13_136_prefix s) (positive_select s 136) (lex_13_136_image s)

theorem lex_13_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.pos 136), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation13 136 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5044) (Sat.Literal.pos 136) (Sat.Literal.pos 68) (lex_13_136_prefix s) (positive_select s 136) (lex_13_136_image s)

theorem lex_13_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.pos 5044)] :=
  (lex_13_136_gate s).prop _ (List.Mem.head _)

theorem lex_13_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.neg 136), (Sat.Literal.pos 68)] :=
  (lex_13_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.pos 136), (Sat.Literal.neg 68)] :=
  (lex_13_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.neg 136), (Sat.Literal.neg 68), (Sat.Literal.pos 5045)] :=
  (lex_13_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5044), (Sat.Literal.pos 136), (Sat.Literal.pos 68), (Sat.Literal.pos 5045)] :=
  (lex_13_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5045) = lexBefore s permutation13 135 := by
  exact (positive_lex_of_descriptor s 5045 permutation13 136 (by rfl)).trans ((lex_skipped s permutation13 135 136 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation13 135) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation13 135 by rw [image13_eq]; rfl))

theorem lex_13_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5046) (Sat.Literal.pos 5045) (Sat.Literal.pos 135) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation13 135 (assignment s)
    (Sat.Literal.pos 5046) (Sat.Literal.pos 5045) (Sat.Literal.pos 135) (Sat.Literal.pos 195) (positive_of_descriptor s 5046 (.lex permutation13 135) (by rfl)) (lex_13_135_prefix s) (positive_select s 135) (lex_13_135_image s)

theorem lex_13_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.pos 135), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation13 135 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5045) (Sat.Literal.pos 135) (Sat.Literal.pos 195) (lex_13_135_prefix s) (positive_select s 135) (lex_13_135_image s)

theorem lex_13_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.pos 5045)] :=
  (lex_13_135_gate s).prop _ (List.Mem.head _)

theorem lex_13_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.neg 135), (Sat.Literal.pos 195)] :=
  (lex_13_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.pos 135), (Sat.Literal.neg 195)] :=
  (lex_13_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.neg 135), (Sat.Literal.neg 195), (Sat.Literal.pos 5046)] :=
  (lex_13_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5045), (Sat.Literal.pos 135), (Sat.Literal.pos 195), (Sat.Literal.pos 5046)] :=
  (lex_13_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5046) = lexBefore s permutation13 134 := by
  exact (positive_lex_of_descriptor s 5046 permutation13 135 (by rfl)).trans ((lex_skipped s permutation13 134 135 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation13 134) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation13 134 by rw [image13_eq]; rfl))

theorem lex_13_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5047) (Sat.Literal.pos 5046) (Sat.Literal.pos 134) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation13 134 (assignment s)
    (Sat.Literal.pos 5047) (Sat.Literal.pos 5046) (Sat.Literal.pos 134) (Sat.Literal.pos 67) (positive_of_descriptor s 5047 (.lex permutation13 134) (by rfl)) (lex_13_134_prefix s) (positive_select s 134) (lex_13_134_image s)

theorem lex_13_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.pos 134), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation13 134 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5046) (Sat.Literal.pos 134) (Sat.Literal.pos 67) (lex_13_134_prefix s) (positive_select s 134) (lex_13_134_image s)

theorem lex_13_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.pos 5046)] :=
  (lex_13_134_gate s).prop _ (List.Mem.head _)

theorem lex_13_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.neg 134), (Sat.Literal.pos 67)] :=
  (lex_13_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.pos 134), (Sat.Literal.neg 67)] :=
  (lex_13_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.neg 134), (Sat.Literal.neg 67), (Sat.Literal.pos 5047)] :=
  (lex_13_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5046), (Sat.Literal.pos 134), (Sat.Literal.pos 67), (Sat.Literal.pos 5047)] :=
  (lex_13_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5047) = lexBefore s permutation13 133 := by
  exact (positive_lex_of_descriptor s 5047 permutation13 134 (by rfl)).trans ((lex_skipped s permutation13 133 134 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation13 133) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation13 133 by rw [image13_eq]; rfl))

theorem lex_13_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5048) (Sat.Literal.pos 5047) (Sat.Literal.pos 133) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation13 133 (assignment s)
    (Sat.Literal.pos 5048) (Sat.Literal.pos 5047) (Sat.Literal.pos 133) (Sat.Literal.pos 194) (positive_of_descriptor s 5048 (.lex permutation13 133) (by rfl)) (lex_13_133_prefix s) (positive_select s 133) (lex_13_133_image s)

theorem lex_13_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.pos 133), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation13 133 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5047) (Sat.Literal.pos 133) (Sat.Literal.pos 194) (lex_13_133_prefix s) (positive_select s 133) (lex_13_133_image s)

theorem lex_13_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.pos 5047)] :=
  (lex_13_133_gate s).prop _ (List.Mem.head _)

theorem lex_13_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.neg 133), (Sat.Literal.pos 194)] :=
  (lex_13_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.pos 133), (Sat.Literal.neg 194)] :=
  (lex_13_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.neg 133), (Sat.Literal.neg 194), (Sat.Literal.pos 5048)] :=
  (lex_13_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5047), (Sat.Literal.pos 133), (Sat.Literal.pos 194), (Sat.Literal.pos 5048)] :=
  (lex_13_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5048) = lexBefore s permutation13 132 := by
  exact (positive_lex_of_descriptor s 5048 permutation13 133 (by rfl)).trans ((lex_skipped s permutation13 132 133 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation13 132) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation13 132 by rw [image13_eq]; rfl))

theorem lex_13_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5049) (Sat.Literal.pos 5048) (Sat.Literal.pos 132) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation13 132 (assignment s)
    (Sat.Literal.pos 5049) (Sat.Literal.pos 5048) (Sat.Literal.pos 132) (Sat.Literal.pos 66) (positive_of_descriptor s 5049 (.lex permutation13 132) (by rfl)) (lex_13_132_prefix s) (positive_select s 132) (lex_13_132_image s)

theorem lex_13_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.pos 132), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation13 132 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5048) (Sat.Literal.pos 132) (Sat.Literal.pos 66) (lex_13_132_prefix s) (positive_select s 132) (lex_13_132_image s)

theorem lex_13_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.pos 5048)] :=
  (lex_13_132_gate s).prop _ (List.Mem.head _)

theorem lex_13_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.neg 132), (Sat.Literal.pos 66)] :=
  (lex_13_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.pos 132), (Sat.Literal.neg 66)] :=
  (lex_13_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.neg 132), (Sat.Literal.neg 66), (Sat.Literal.pos 5049)] :=
  (lex_13_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5048), (Sat.Literal.pos 132), (Sat.Literal.pos 66), (Sat.Literal.pos 5049)] :=
  (lex_13_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5049) = lexBefore s permutation13 131 := by
  exact (positive_lex_of_descriptor s 5049 permutation13 132 (by rfl)).trans ((lex_skipped s permutation13 131 132 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation13 131) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation13 131 by rw [image13_eq]; rfl))

theorem lex_13_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5050) (Sat.Literal.pos 5049) (Sat.Literal.pos 131) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation13 131 (assignment s)
    (Sat.Literal.pos 5050) (Sat.Literal.pos 5049) (Sat.Literal.pos 131) (Sat.Literal.pos 193) (positive_of_descriptor s 5050 (.lex permutation13 131) (by rfl)) (lex_13_131_prefix s) (positive_select s 131) (lex_13_131_image s)

theorem lex_13_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.pos 131), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation13 131 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5049) (Sat.Literal.pos 131) (Sat.Literal.pos 193) (lex_13_131_prefix s) (positive_select s 131) (lex_13_131_image s)

theorem lex_13_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.pos 5049)] :=
  (lex_13_131_gate s).prop _ (List.Mem.head _)

theorem lex_13_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.neg 131), (Sat.Literal.pos 193)] :=
  (lex_13_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.pos 131), (Sat.Literal.neg 193)] :=
  (lex_13_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.neg 131), (Sat.Literal.neg 193), (Sat.Literal.pos 5050)] :=
  (lex_13_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5049), (Sat.Literal.pos 131), (Sat.Literal.pos 193), (Sat.Literal.pos 5050)] :=
  (lex_13_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5050) = lexBefore s permutation13 130 := by
  exact (positive_lex_of_descriptor s 5050 permutation13 131 (by rfl)).trans ((lex_skipped s permutation13 130 131 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation13 130) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation13 130 by rw [image13_eq]; rfl))

theorem lex_13_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5051) (Sat.Literal.pos 5050) (Sat.Literal.pos 130) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation13 130 (assignment s)
    (Sat.Literal.pos 5051) (Sat.Literal.pos 5050) (Sat.Literal.pos 130) (Sat.Literal.pos 65) (positive_of_descriptor s 5051 (.lex permutation13 130) (by rfl)) (lex_13_130_prefix s) (positive_select s 130) (lex_13_130_image s)

theorem lex_13_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.pos 130), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation13 130 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5050) (Sat.Literal.pos 130) (Sat.Literal.pos 65) (lex_13_130_prefix s) (positive_select s 130) (lex_13_130_image s)

theorem lex_13_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.pos 5050)] :=
  (lex_13_130_gate s).prop _ (List.Mem.head _)

theorem lex_13_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.neg 130), (Sat.Literal.pos 65)] :=
  (lex_13_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.pos 130), (Sat.Literal.neg 65)] :=
  (lex_13_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.neg 130), (Sat.Literal.neg 65), (Sat.Literal.pos 5051)] :=
  (lex_13_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5050), (Sat.Literal.pos 130), (Sat.Literal.pos 65), (Sat.Literal.pos 5051)] :=
  (lex_13_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5051) = lexBefore s permutation13 129 := by
  exact (positive_lex_of_descriptor s 5051 permutation13 130 (by rfl)).trans ((lex_skipped s permutation13 129 130 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation13 129) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation13 129 by rw [image13_eq]; rfl))

theorem lex_13_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5052) (Sat.Literal.pos 5051) (Sat.Literal.pos 129) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation13 129 (assignment s)
    (Sat.Literal.pos 5052) (Sat.Literal.pos 5051) (Sat.Literal.pos 129) (Sat.Literal.pos 192) (positive_of_descriptor s 5052 (.lex permutation13 129) (by rfl)) (lex_13_129_prefix s) (positive_select s 129) (lex_13_129_image s)

theorem lex_13_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.pos 129), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation13 129 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5051) (Sat.Literal.pos 129) (Sat.Literal.pos 192) (lex_13_129_prefix s) (positive_select s 129) (lex_13_129_image s)

theorem lex_13_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.pos 5051)] :=
  (lex_13_129_gate s).prop _ (List.Mem.head _)

theorem lex_13_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.neg 129), (Sat.Literal.pos 192)] :=
  (lex_13_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.pos 129), (Sat.Literal.neg 192)] :=
  (lex_13_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.neg 129), (Sat.Literal.neg 192), (Sat.Literal.pos 5052)] :=
  (lex_13_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5051), (Sat.Literal.pos 129), (Sat.Literal.pos 192), (Sat.Literal.pos 5052)] :=
  (lex_13_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5052) = lexBefore s permutation13 128 := by
  exact (positive_lex_of_descriptor s 5052 permutation13 129 (by rfl)).trans ((lex_skipped s permutation13 128 129 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation13 128) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation13 128 by rw [image13_eq]; rfl))

theorem lex_13_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5053) (Sat.Literal.pos 5052) (Sat.Literal.pos 128) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation13 128 (assignment s)
    (Sat.Literal.pos 5053) (Sat.Literal.pos 5052) (Sat.Literal.pos 128) (Sat.Literal.pos 64) (positive_of_descriptor s 5053 (.lex permutation13 128) (by rfl)) (lex_13_128_prefix s) (positive_select s 128) (lex_13_128_image s)

theorem lex_13_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.pos 128), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation13 128 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5052) (Sat.Literal.pos 128) (Sat.Literal.pos 64) (lex_13_128_prefix s) (positive_select s 128) (lex_13_128_image s)

theorem lex_13_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.pos 5052)] :=
  (lex_13_128_gate s).prop _ (List.Mem.head _)

theorem lex_13_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.neg 128), (Sat.Literal.pos 64)] :=
  (lex_13_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.pos 128), (Sat.Literal.neg 64)] :=
  (lex_13_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.neg 128), (Sat.Literal.neg 64), (Sat.Literal.pos 5053)] :=
  (lex_13_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5052), (Sat.Literal.pos 128), (Sat.Literal.pos 64), (Sat.Literal.pos 5053)] :=
  (lex_13_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5053) = lexBefore s permutation13 127 := by
  exact (positive_lex_of_descriptor s 5053 permutation13 128 (by rfl)).trans ((lex_skipped s permutation13 127 128 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation13 127) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation13 127 by rw [image13_eq]; rfl))

theorem lex_13_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5054) (Sat.Literal.pos 5053) (Sat.Literal.pos 127) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation13 127 (assignment s)
    (Sat.Literal.pos 5054) (Sat.Literal.pos 5053) (Sat.Literal.pos 127) (Sat.Literal.pos 191) (positive_of_descriptor s 5054 (.lex permutation13 127) (by rfl)) (lex_13_127_prefix s) (positive_select s 127) (lex_13_127_image s)

theorem lex_13_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.pos 127), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation13 127 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5053) (Sat.Literal.pos 127) (Sat.Literal.pos 191) (lex_13_127_prefix s) (positive_select s 127) (lex_13_127_image s)

theorem lex_13_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.pos 5053)] :=
  (lex_13_127_gate s).prop _ (List.Mem.head _)

theorem lex_13_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.neg 127), (Sat.Literal.pos 191)] :=
  (lex_13_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.pos 127), (Sat.Literal.neg 191)] :=
  (lex_13_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.neg 127), (Sat.Literal.neg 191), (Sat.Literal.pos 5054)] :=
  (lex_13_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5053), (Sat.Literal.pos 127), (Sat.Literal.pos 191), (Sat.Literal.pos 5054)] :=
  (lex_13_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5054) = lexBefore s permutation13 126 := by
  exact (positive_lex_of_descriptor s 5054 permutation13 127 (by rfl)).trans ((lex_skipped s permutation13 126 127 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation13 126) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation13 126 by rw [image13_eq]; rfl))

theorem lex_13_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5055) (Sat.Literal.pos 5054) (Sat.Literal.pos 126) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation13 126 (assignment s)
    (Sat.Literal.pos 5055) (Sat.Literal.pos 5054) (Sat.Literal.pos 126) (Sat.Literal.pos 63) (positive_of_descriptor s 5055 (.lex permutation13 126) (by rfl)) (lex_13_126_prefix s) (positive_select s 126) (lex_13_126_image s)

theorem lex_13_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.pos 126), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation13 126 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5054) (Sat.Literal.pos 126) (Sat.Literal.pos 63) (lex_13_126_prefix s) (positive_select s 126) (lex_13_126_image s)

theorem lex_13_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.pos 5054)] :=
  (lex_13_126_gate s).prop _ (List.Mem.head _)

theorem lex_13_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.neg 126), (Sat.Literal.pos 63)] :=
  (lex_13_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.pos 126), (Sat.Literal.neg 63)] :=
  (lex_13_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.neg 126), (Sat.Literal.neg 63), (Sat.Literal.pos 5055)] :=
  (lex_13_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5054), (Sat.Literal.pos 126), (Sat.Literal.pos 63), (Sat.Literal.pos 5055)] :=
  (lex_13_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5055) = lexBefore s permutation13 125 := by
  exact (positive_lex_of_descriptor s 5055 permutation13 126 (by rfl)).trans ((lex_skipped s permutation13 125 126 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation13 125) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation13 125 by rw [image13_eq]; rfl))

theorem lex_13_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5056) (Sat.Literal.pos 5055) (Sat.Literal.pos 125) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation13 125 (assignment s)
    (Sat.Literal.pos 5056) (Sat.Literal.pos 5055) (Sat.Literal.pos 125) (Sat.Literal.pos 190) (positive_of_descriptor s 5056 (.lex permutation13 125) (by rfl)) (lex_13_125_prefix s) (positive_select s 125) (lex_13_125_image s)

theorem lex_13_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.pos 125), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation13 125 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5055) (Sat.Literal.pos 125) (Sat.Literal.pos 190) (lex_13_125_prefix s) (positive_select s 125) (lex_13_125_image s)

theorem lex_13_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.pos 5055)] :=
  (lex_13_125_gate s).prop _ (List.Mem.head _)

theorem lex_13_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.neg 125), (Sat.Literal.pos 190)] :=
  (lex_13_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.pos 125), (Sat.Literal.neg 190)] :=
  (lex_13_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.neg 125), (Sat.Literal.neg 190), (Sat.Literal.pos 5056)] :=
  (lex_13_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5055), (Sat.Literal.pos 125), (Sat.Literal.pos 190), (Sat.Literal.pos 5056)] :=
  (lex_13_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5056) = lexBefore s permutation13 124 := by
  exact (positive_lex_of_descriptor s 5056 permutation13 125 (by rfl)).trans ((lex_skipped s permutation13 124 125 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation13 124) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation13 124 by rw [image13_eq]; rfl))

theorem lex_13_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5057) (Sat.Literal.pos 5056) (Sat.Literal.pos 124) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation13 124 (assignment s)
    (Sat.Literal.pos 5057) (Sat.Literal.pos 5056) (Sat.Literal.pos 124) (Sat.Literal.pos 62) (positive_of_descriptor s 5057 (.lex permutation13 124) (by rfl)) (lex_13_124_prefix s) (positive_select s 124) (lex_13_124_image s)

theorem lex_13_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.pos 124), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation13 124 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5056) (Sat.Literal.pos 124) (Sat.Literal.pos 62) (lex_13_124_prefix s) (positive_select s 124) (lex_13_124_image s)

theorem lex_13_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.pos 5056)] :=
  (lex_13_124_gate s).prop _ (List.Mem.head _)

theorem lex_13_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.neg 124), (Sat.Literal.pos 62)] :=
  (lex_13_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.pos 124), (Sat.Literal.neg 62)] :=
  (lex_13_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.neg 124), (Sat.Literal.neg 62), (Sat.Literal.pos 5057)] :=
  (lex_13_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5056), (Sat.Literal.pos 124), (Sat.Literal.pos 62), (Sat.Literal.pos 5057)] :=
  (lex_13_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5057) = lexBefore s permutation13 123 := by
  exact (positive_lex_of_descriptor s 5057 permutation13 124 (by rfl)).trans ((lex_skipped s permutation13 123 124 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation13 123) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation13 123 by rw [image13_eq]; rfl))

theorem lex_13_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5058) (Sat.Literal.pos 5057) (Sat.Literal.pos 123) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation13 123 (assignment s)
    (Sat.Literal.pos 5058) (Sat.Literal.pos 5057) (Sat.Literal.pos 123) (Sat.Literal.pos 189) (positive_of_descriptor s 5058 (.lex permutation13 123) (by rfl)) (lex_13_123_prefix s) (positive_select s 123) (lex_13_123_image s)

theorem lex_13_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.pos 123), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation13 123 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5057) (Sat.Literal.pos 123) (Sat.Literal.pos 189) (lex_13_123_prefix s) (positive_select s 123) (lex_13_123_image s)

theorem lex_13_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.pos 5057)] :=
  (lex_13_123_gate s).prop _ (List.Mem.head _)

theorem lex_13_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.neg 123), (Sat.Literal.pos 189)] :=
  (lex_13_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.pos 123), (Sat.Literal.neg 189)] :=
  (lex_13_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.neg 123), (Sat.Literal.neg 189), (Sat.Literal.pos 5058)] :=
  (lex_13_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5057), (Sat.Literal.pos 123), (Sat.Literal.pos 189), (Sat.Literal.pos 5058)] :=
  (lex_13_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5058) = lexBefore s permutation13 122 := by
  exact (positive_lex_of_descriptor s 5058 permutation13 123 (by rfl)).trans ((lex_skipped s permutation13 122 123 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation13 122) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation13 122 by rw [image13_eq]; rfl))

theorem lex_13_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5059) (Sat.Literal.pos 5058) (Sat.Literal.pos 122) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation13 122 (assignment s)
    (Sat.Literal.pos 5059) (Sat.Literal.pos 5058) (Sat.Literal.pos 122) (Sat.Literal.pos 61) (positive_of_descriptor s 5059 (.lex permutation13 122) (by rfl)) (lex_13_122_prefix s) (positive_select s 122) (lex_13_122_image s)

theorem lex_13_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.pos 122), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation13 122 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5058) (Sat.Literal.pos 122) (Sat.Literal.pos 61) (lex_13_122_prefix s) (positive_select s 122) (lex_13_122_image s)

theorem lex_13_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.pos 5058)] :=
  (lex_13_122_gate s).prop _ (List.Mem.head _)

theorem lex_13_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.neg 122), (Sat.Literal.pos 61)] :=
  (lex_13_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.pos 122), (Sat.Literal.neg 61)] :=
  (lex_13_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.neg 122), (Sat.Literal.neg 61), (Sat.Literal.pos 5059)] :=
  (lex_13_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5058), (Sat.Literal.pos 122), (Sat.Literal.pos 61), (Sat.Literal.pos 5059)] :=
  (lex_13_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5059) = lexBefore s permutation13 121 := by
  exact (positive_lex_of_descriptor s 5059 permutation13 122 (by rfl)).trans ((lex_skipped s permutation13 121 122 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation13 121) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation13 121 by rw [image13_eq]; rfl))

theorem lex_13_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5060) (Sat.Literal.pos 5059) (Sat.Literal.pos 121) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation13 121 (assignment s)
    (Sat.Literal.pos 5060) (Sat.Literal.pos 5059) (Sat.Literal.pos 121) (Sat.Literal.pos 188) (positive_of_descriptor s 5060 (.lex permutation13 121) (by rfl)) (lex_13_121_prefix s) (positive_select s 121) (lex_13_121_image s)

theorem lex_13_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.pos 121), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation13 121 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5059) (Sat.Literal.pos 121) (Sat.Literal.pos 188) (lex_13_121_prefix s) (positive_select s 121) (lex_13_121_image s)

theorem lex_13_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.pos 5059)] :=
  (lex_13_121_gate s).prop _ (List.Mem.head _)

theorem lex_13_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.neg 121), (Sat.Literal.pos 188)] :=
  (lex_13_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.pos 121), (Sat.Literal.neg 188)] :=
  (lex_13_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.neg 121), (Sat.Literal.neg 188), (Sat.Literal.pos 5060)] :=
  (lex_13_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5059), (Sat.Literal.pos 121), (Sat.Literal.pos 188), (Sat.Literal.pos 5060)] :=
  (lex_13_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5060) = lexBefore s permutation13 120 := by
  exact (positive_lex_of_descriptor s 5060 permutation13 121 (by rfl)).trans ((lex_skipped s permutation13 120 121 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation13 120) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation13 120 by rw [image13_eq]; rfl))

theorem lex_13_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5061) (Sat.Literal.pos 5060) (Sat.Literal.pos 120) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation13 120 (assignment s)
    (Sat.Literal.pos 5061) (Sat.Literal.pos 5060) (Sat.Literal.pos 120) (Sat.Literal.pos 60) (positive_of_descriptor s 5061 (.lex permutation13 120) (by rfl)) (lex_13_120_prefix s) (positive_select s 120) (lex_13_120_image s)

theorem lex_13_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.pos 120), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation13 120 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5060) (Sat.Literal.pos 120) (Sat.Literal.pos 60) (lex_13_120_prefix s) (positive_select s 120) (lex_13_120_image s)

theorem lex_13_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.pos 5060)] :=
  (lex_13_120_gate s).prop _ (List.Mem.head _)

theorem lex_13_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.neg 120), (Sat.Literal.pos 60)] :=
  (lex_13_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.pos 120), (Sat.Literal.neg 60)] :=
  (lex_13_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.neg 120), (Sat.Literal.neg 60), (Sat.Literal.pos 5061)] :=
  (lex_13_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5060), (Sat.Literal.pos 120), (Sat.Literal.pos 60), (Sat.Literal.pos 5061)] :=
  (lex_13_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5061) = lexBefore s permutation13 119 := by
  exact (positive_lex_of_descriptor s 5061 permutation13 120 (by rfl)).trans ((lex_skipped s permutation13 119 120 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation13 119) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation13 119 by rw [image13_eq]; rfl))

theorem lex_13_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5062) (Sat.Literal.pos 5061) (Sat.Literal.pos 119) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation13 119 (assignment s)
    (Sat.Literal.pos 5062) (Sat.Literal.pos 5061) (Sat.Literal.pos 119) (Sat.Literal.pos 187) (positive_of_descriptor s 5062 (.lex permutation13 119) (by rfl)) (lex_13_119_prefix s) (positive_select s 119) (lex_13_119_image s)

theorem lex_13_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.pos 119), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation13 119 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5061) (Sat.Literal.pos 119) (Sat.Literal.pos 187) (lex_13_119_prefix s) (positive_select s 119) (lex_13_119_image s)

theorem lex_13_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.pos 5061)] :=
  (lex_13_119_gate s).prop _ (List.Mem.head _)

theorem lex_13_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.neg 119), (Sat.Literal.pos 187)] :=
  (lex_13_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.pos 119), (Sat.Literal.neg 187)] :=
  (lex_13_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.neg 119), (Sat.Literal.neg 187), (Sat.Literal.pos 5062)] :=
  (lex_13_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5061), (Sat.Literal.pos 119), (Sat.Literal.pos 187), (Sat.Literal.pos 5062)] :=
  (lex_13_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5062) = lexBefore s permutation13 118 := by
  exact (positive_lex_of_descriptor s 5062 permutation13 119 (by rfl)).trans ((lex_skipped s permutation13 118 119 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation13 118) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation13 118 by rw [image13_eq]; rfl))

theorem lex_13_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5063) (Sat.Literal.pos 5062) (Sat.Literal.pos 118) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation13 118 (assignment s)
    (Sat.Literal.pos 5063) (Sat.Literal.pos 5062) (Sat.Literal.pos 118) (Sat.Literal.pos 59) (positive_of_descriptor s 5063 (.lex permutation13 118) (by rfl)) (lex_13_118_prefix s) (positive_select s 118) (lex_13_118_image s)

theorem lex_13_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.pos 118), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation13 118 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5062) (Sat.Literal.pos 118) (Sat.Literal.pos 59) (lex_13_118_prefix s) (positive_select s 118) (lex_13_118_image s)

theorem lex_13_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.pos 5062)] :=
  (lex_13_118_gate s).prop _ (List.Mem.head _)

theorem lex_13_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.neg 118), (Sat.Literal.pos 59)] :=
  (lex_13_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.pos 118), (Sat.Literal.neg 59)] :=
  (lex_13_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.neg 118), (Sat.Literal.neg 59), (Sat.Literal.pos 5063)] :=
  (lex_13_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5062), (Sat.Literal.pos 118), (Sat.Literal.pos 59), (Sat.Literal.pos 5063)] :=
  (lex_13_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5063) = lexBefore s permutation13 117 := by
  exact (positive_lex_of_descriptor s 5063 permutation13 118 (by rfl)).trans ((lex_skipped s permutation13 117 118 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation13 117) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation13 117 by rw [image13_eq]; rfl))

theorem lex_13_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5064) (Sat.Literal.pos 5063) (Sat.Literal.pos 117) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation13 117 (assignment s)
    (Sat.Literal.pos 5064) (Sat.Literal.pos 5063) (Sat.Literal.pos 117) (Sat.Literal.pos 186) (positive_of_descriptor s 5064 (.lex permutation13 117) (by rfl)) (lex_13_117_prefix s) (positive_select s 117) (lex_13_117_image s)

theorem lex_13_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.pos 117), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation13 117 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5063) (Sat.Literal.pos 117) (Sat.Literal.pos 186) (lex_13_117_prefix s) (positive_select s 117) (lex_13_117_image s)

theorem lex_13_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.pos 5063)] :=
  (lex_13_117_gate s).prop _ (List.Mem.head _)

theorem lex_13_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.neg 117), (Sat.Literal.pos 186)] :=
  (lex_13_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.pos 117), (Sat.Literal.neg 186)] :=
  (lex_13_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.neg 117), (Sat.Literal.neg 186), (Sat.Literal.pos 5064)] :=
  (lex_13_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5063), (Sat.Literal.pos 117), (Sat.Literal.pos 186), (Sat.Literal.pos 5064)] :=
  (lex_13_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5064) = lexBefore s permutation13 116 := by
  exact (positive_lex_of_descriptor s 5064 permutation13 117 (by rfl)).trans ((lex_skipped s permutation13 116 117 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation13 116) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation13 116 by rw [image13_eq]; rfl))

theorem lex_13_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5065) (Sat.Literal.pos 5064) (Sat.Literal.pos 116) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation13 116 (assignment s)
    (Sat.Literal.pos 5065) (Sat.Literal.pos 5064) (Sat.Literal.pos 116) (Sat.Literal.pos 58) (positive_of_descriptor s 5065 (.lex permutation13 116) (by rfl)) (lex_13_116_prefix s) (positive_select s 116) (lex_13_116_image s)

theorem lex_13_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.pos 116), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation13 116 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5064) (Sat.Literal.pos 116) (Sat.Literal.pos 58) (lex_13_116_prefix s) (positive_select s 116) (lex_13_116_image s)

theorem lex_13_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.pos 5064)] :=
  (lex_13_116_gate s).prop _ (List.Mem.head _)

theorem lex_13_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.neg 116), (Sat.Literal.pos 58)] :=
  (lex_13_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.pos 116), (Sat.Literal.neg 58)] :=
  (lex_13_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.neg 116), (Sat.Literal.neg 58), (Sat.Literal.pos 5065)] :=
  (lex_13_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5064), (Sat.Literal.pos 116), (Sat.Literal.pos 58), (Sat.Literal.pos 5065)] :=
  (lex_13_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5065) = lexBefore s permutation13 115 := by
  exact (positive_lex_of_descriptor s 5065 permutation13 116 (by rfl)).trans ((lex_skipped s permutation13 115 116 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation13 115) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation13 115 by rw [image13_eq]; rfl))

theorem lex_13_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5066) (Sat.Literal.pos 5065) (Sat.Literal.pos 115) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation13 115 (assignment s)
    (Sat.Literal.pos 5066) (Sat.Literal.pos 5065) (Sat.Literal.pos 115) (Sat.Literal.pos 185) (positive_of_descriptor s 5066 (.lex permutation13 115) (by rfl)) (lex_13_115_prefix s) (positive_select s 115) (lex_13_115_image s)

theorem lex_13_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.pos 115), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation13 115 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5065) (Sat.Literal.pos 115) (Sat.Literal.pos 185) (lex_13_115_prefix s) (positive_select s 115) (lex_13_115_image s)

theorem lex_13_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.pos 5065)] :=
  (lex_13_115_gate s).prop _ (List.Mem.head _)

theorem lex_13_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.neg 115), (Sat.Literal.pos 185)] :=
  (lex_13_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.pos 115), (Sat.Literal.neg 185)] :=
  (lex_13_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.neg 115), (Sat.Literal.neg 185), (Sat.Literal.pos 5066)] :=
  (lex_13_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5065), (Sat.Literal.pos 115), (Sat.Literal.pos 185), (Sat.Literal.pos 5066)] :=
  (lex_13_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5066) = lexBefore s permutation13 114 := by
  exact (positive_lex_of_descriptor s 5066 permutation13 115 (by rfl)).trans ((lex_skipped s permutation13 114 115 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation13 114) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation13 114 by rw [image13_eq]; rfl))

theorem lex_13_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5067) (Sat.Literal.pos 5066) (Sat.Literal.pos 114) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation13 114 (assignment s)
    (Sat.Literal.pos 5067) (Sat.Literal.pos 5066) (Sat.Literal.pos 114) (Sat.Literal.pos 57) (positive_of_descriptor s 5067 (.lex permutation13 114) (by rfl)) (lex_13_114_prefix s) (positive_select s 114) (lex_13_114_image s)

theorem lex_13_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.pos 114), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation13 114 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5066) (Sat.Literal.pos 114) (Sat.Literal.pos 57) (lex_13_114_prefix s) (positive_select s 114) (lex_13_114_image s)

theorem lex_13_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.pos 5066)] :=
  (lex_13_114_gate s).prop _ (List.Mem.head _)

theorem lex_13_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.neg 114), (Sat.Literal.pos 57)] :=
  (lex_13_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.pos 114), (Sat.Literal.neg 57)] :=
  (lex_13_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.neg 114), (Sat.Literal.neg 57), (Sat.Literal.pos 5067)] :=
  (lex_13_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5066), (Sat.Literal.pos 114), (Sat.Literal.pos 57), (Sat.Literal.pos 5067)] :=
  (lex_13_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5067) = lexBefore s permutation13 113 := by
  exact (positive_lex_of_descriptor s 5067 permutation13 114 (by rfl)).trans ((lex_skipped s permutation13 113 114 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation13 113) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation13 113 by rw [image13_eq]; rfl))

theorem lex_13_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5068) (Sat.Literal.pos 5067) (Sat.Literal.pos 113) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation13 113 (assignment s)
    (Sat.Literal.pos 5068) (Sat.Literal.pos 5067) (Sat.Literal.pos 113) (Sat.Literal.pos 184) (positive_of_descriptor s 5068 (.lex permutation13 113) (by rfl)) (lex_13_113_prefix s) (positive_select s 113) (lex_13_113_image s)

theorem lex_13_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.pos 113), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation13 113 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5067) (Sat.Literal.pos 113) (Sat.Literal.pos 184) (lex_13_113_prefix s) (positive_select s 113) (lex_13_113_image s)

theorem lex_13_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.pos 5067)] :=
  (lex_13_113_gate s).prop _ (List.Mem.head _)

theorem lex_13_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.neg 113), (Sat.Literal.pos 184)] :=
  (lex_13_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.pos 113), (Sat.Literal.neg 184)] :=
  (lex_13_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.neg 113), (Sat.Literal.neg 184), (Sat.Literal.pos 5068)] :=
  (lex_13_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5067), (Sat.Literal.pos 113), (Sat.Literal.pos 184), (Sat.Literal.pos 5068)] :=
  (lex_13_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5068) = lexBefore s permutation13 112 := by
  exact (positive_lex_of_descriptor s 5068 permutation13 113 (by rfl)).trans ((lex_skipped s permutation13 112 113 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation13 112) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation13 112 by rw [image13_eq]; rfl))

theorem lex_13_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5069) (Sat.Literal.pos 5068) (Sat.Literal.pos 112) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation13 112 (assignment s)
    (Sat.Literal.pos 5069) (Sat.Literal.pos 5068) (Sat.Literal.pos 112) (Sat.Literal.pos 56) (positive_of_descriptor s 5069 (.lex permutation13 112) (by rfl)) (lex_13_112_prefix s) (positive_select s 112) (lex_13_112_image s)

theorem lex_13_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.pos 112), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation13 112 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5068) (Sat.Literal.pos 112) (Sat.Literal.pos 56) (lex_13_112_prefix s) (positive_select s 112) (lex_13_112_image s)

theorem lex_13_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.pos 5068)] :=
  (lex_13_112_gate s).prop _ (List.Mem.head _)

theorem lex_13_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.neg 112), (Sat.Literal.pos 56)] :=
  (lex_13_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.pos 112), (Sat.Literal.neg 56)] :=
  (lex_13_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.neg 112), (Sat.Literal.neg 56), (Sat.Literal.pos 5069)] :=
  (lex_13_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5068), (Sat.Literal.pos 112), (Sat.Literal.pos 56), (Sat.Literal.pos 5069)] :=
  (lex_13_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5069) = lexBefore s permutation13 111 := by
  exact (positive_lex_of_descriptor s 5069 permutation13 112 (by rfl)).trans ((lex_skipped s permutation13 111 112 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation13 111) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation13 111 by rw [image13_eq]; rfl))

theorem lex_13_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5070) (Sat.Literal.pos 5069) (Sat.Literal.pos 111) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation13 111 (assignment s)
    (Sat.Literal.pos 5070) (Sat.Literal.pos 5069) (Sat.Literal.pos 111) (Sat.Literal.pos 183) (positive_of_descriptor s 5070 (.lex permutation13 111) (by rfl)) (lex_13_111_prefix s) (positive_select s 111) (lex_13_111_image s)

theorem lex_13_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.pos 111), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation13 111 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5069) (Sat.Literal.pos 111) (Sat.Literal.pos 183) (lex_13_111_prefix s) (positive_select s 111) (lex_13_111_image s)

theorem lex_13_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.pos 5069)] :=
  (lex_13_111_gate s).prop _ (List.Mem.head _)

theorem lex_13_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.neg 111), (Sat.Literal.pos 183)] :=
  (lex_13_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.pos 111), (Sat.Literal.neg 183)] :=
  (lex_13_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.neg 111), (Sat.Literal.neg 183), (Sat.Literal.pos 5070)] :=
  (lex_13_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5069), (Sat.Literal.pos 111), (Sat.Literal.pos 183), (Sat.Literal.pos 5070)] :=
  (lex_13_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5070) = lexBefore s permutation13 110 := by
  exact (positive_lex_of_descriptor s 5070 permutation13 111 (by rfl)).trans ((lex_skipped s permutation13 110 111 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation13 110) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation13 110 by rw [image13_eq]; rfl))

theorem lex_13_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5071) (Sat.Literal.pos 5070) (Sat.Literal.pos 110) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation13 110 (assignment s)
    (Sat.Literal.pos 5071) (Sat.Literal.pos 5070) (Sat.Literal.pos 110) (Sat.Literal.pos 55) (positive_of_descriptor s 5071 (.lex permutation13 110) (by rfl)) (lex_13_110_prefix s) (positive_select s 110) (lex_13_110_image s)

theorem lex_13_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.pos 110), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation13 110 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5070) (Sat.Literal.pos 110) (Sat.Literal.pos 55) (lex_13_110_prefix s) (positive_select s 110) (lex_13_110_image s)

theorem lex_13_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.pos 5070)] :=
  (lex_13_110_gate s).prop _ (List.Mem.head _)

theorem lex_13_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.neg 110), (Sat.Literal.pos 55)] :=
  (lex_13_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.pos 110), (Sat.Literal.neg 55)] :=
  (lex_13_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.neg 110), (Sat.Literal.neg 55), (Sat.Literal.pos 5071)] :=
  (lex_13_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5070), (Sat.Literal.pos 110), (Sat.Literal.pos 55), (Sat.Literal.pos 5071)] :=
  (lex_13_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5071) = lexBefore s permutation13 109 := by
  exact (positive_lex_of_descriptor s 5071 permutation13 110 (by rfl)).trans ((lex_skipped s permutation13 109 110 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation13 109) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation13 109 by rw [image13_eq]; rfl))

theorem lex_13_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5072) (Sat.Literal.pos 5071) (Sat.Literal.pos 109) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation13 109 (assignment s)
    (Sat.Literal.pos 5072) (Sat.Literal.pos 5071) (Sat.Literal.pos 109) (Sat.Literal.pos 182) (positive_of_descriptor s 5072 (.lex permutation13 109) (by rfl)) (lex_13_109_prefix s) (positive_select s 109) (lex_13_109_image s)

theorem lex_13_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.pos 109), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation13 109 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5071) (Sat.Literal.pos 109) (Sat.Literal.pos 182) (lex_13_109_prefix s) (positive_select s 109) (lex_13_109_image s)

theorem lex_13_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.pos 5071)] :=
  (lex_13_109_gate s).prop _ (List.Mem.head _)

theorem lex_13_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.neg 109), (Sat.Literal.pos 182)] :=
  (lex_13_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.pos 109), (Sat.Literal.neg 182)] :=
  (lex_13_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.neg 109), (Sat.Literal.neg 182), (Sat.Literal.pos 5072)] :=
  (lex_13_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5071), (Sat.Literal.pos 109), (Sat.Literal.pos 182), (Sat.Literal.pos 5072)] :=
  (lex_13_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5072) = lexBefore s permutation13 108 := by
  exact (positive_lex_of_descriptor s 5072 permutation13 109 (by rfl)).trans ((lex_skipped s permutation13 108 109 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation13 108) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation13 108 by rw [image13_eq]; rfl))

theorem lex_13_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5073) (Sat.Literal.pos 5072) (Sat.Literal.pos 108) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation13 108 (assignment s)
    (Sat.Literal.pos 5073) (Sat.Literal.pos 5072) (Sat.Literal.pos 108) (Sat.Literal.pos 54) (positive_of_descriptor s 5073 (.lex permutation13 108) (by rfl)) (lex_13_108_prefix s) (positive_select s 108) (lex_13_108_image s)

theorem lex_13_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.pos 108), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation13 108 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5072) (Sat.Literal.pos 108) (Sat.Literal.pos 54) (lex_13_108_prefix s) (positive_select s 108) (lex_13_108_image s)

theorem lex_13_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.pos 5072)] :=
  (lex_13_108_gate s).prop _ (List.Mem.head _)

theorem lex_13_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.neg 108), (Sat.Literal.pos 54)] :=
  (lex_13_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.pos 108), (Sat.Literal.neg 54)] :=
  (lex_13_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.neg 108), (Sat.Literal.neg 54), (Sat.Literal.pos 5073)] :=
  (lex_13_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5072), (Sat.Literal.pos 108), (Sat.Literal.pos 54), (Sat.Literal.pos 5073)] :=
  (lex_13_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5073) = lexBefore s permutation13 107 := by
  exact (positive_lex_of_descriptor s 5073 permutation13 108 (by rfl)).trans ((lex_skipped s permutation13 107 108 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation13 107) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation13 107 by rw [image13_eq]; rfl))

theorem lex_13_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5074) (Sat.Literal.pos 5073) (Sat.Literal.pos 107) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation13 107 (assignment s)
    (Sat.Literal.pos 5074) (Sat.Literal.pos 5073) (Sat.Literal.pos 107) (Sat.Literal.pos 181) (positive_of_descriptor s 5074 (.lex permutation13 107) (by rfl)) (lex_13_107_prefix s) (positive_select s 107) (lex_13_107_image s)

theorem lex_13_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.pos 107), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation13 107 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5073) (Sat.Literal.pos 107) (Sat.Literal.pos 181) (lex_13_107_prefix s) (positive_select s 107) (lex_13_107_image s)

theorem lex_13_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.pos 5073)] :=
  (lex_13_107_gate s).prop _ (List.Mem.head _)

theorem lex_13_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.neg 107), (Sat.Literal.pos 181)] :=
  (lex_13_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.pos 107), (Sat.Literal.neg 181)] :=
  (lex_13_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.neg 107), (Sat.Literal.neg 181), (Sat.Literal.pos 5074)] :=
  (lex_13_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5073), (Sat.Literal.pos 107), (Sat.Literal.pos 181), (Sat.Literal.pos 5074)] :=
  (lex_13_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5074) = lexBefore s permutation13 106 := by
  exact (positive_lex_of_descriptor s 5074 permutation13 107 (by rfl)).trans ((lex_skipped s permutation13 106 107 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation13 106) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation13 106 by rw [image13_eq]; rfl))

theorem lex_13_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5075) (Sat.Literal.pos 5074) (Sat.Literal.pos 106) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation13 106 (assignment s)
    (Sat.Literal.pos 5075) (Sat.Literal.pos 5074) (Sat.Literal.pos 106) (Sat.Literal.pos 53) (positive_of_descriptor s 5075 (.lex permutation13 106) (by rfl)) (lex_13_106_prefix s) (positive_select s 106) (lex_13_106_image s)

theorem lex_13_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.pos 106), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation13 106 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5074) (Sat.Literal.pos 106) (Sat.Literal.pos 53) (lex_13_106_prefix s) (positive_select s 106) (lex_13_106_image s)

theorem lex_13_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.pos 5074)] :=
  (lex_13_106_gate s).prop _ (List.Mem.head _)

theorem lex_13_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.neg 106), (Sat.Literal.pos 53)] :=
  (lex_13_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.pos 106), (Sat.Literal.neg 53)] :=
  (lex_13_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.neg 106), (Sat.Literal.neg 53), (Sat.Literal.pos 5075)] :=
  (lex_13_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5074), (Sat.Literal.pos 106), (Sat.Literal.pos 53), (Sat.Literal.pos 5075)] :=
  (lex_13_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5075) = lexBefore s permutation13 105 := by
  exact (positive_lex_of_descriptor s 5075 permutation13 106 (by rfl)).trans ((lex_skipped s permutation13 105 106 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation13 105) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation13 105 by rw [image13_eq]; rfl))

theorem lex_13_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5076) (Sat.Literal.pos 5075) (Sat.Literal.pos 105) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation13 105 (assignment s)
    (Sat.Literal.pos 5076) (Sat.Literal.pos 5075) (Sat.Literal.pos 105) (Sat.Literal.pos 180) (positive_of_descriptor s 5076 (.lex permutation13 105) (by rfl)) (lex_13_105_prefix s) (positive_select s 105) (lex_13_105_image s)

theorem lex_13_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.pos 105), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation13 105 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5075) (Sat.Literal.pos 105) (Sat.Literal.pos 180) (lex_13_105_prefix s) (positive_select s 105) (lex_13_105_image s)

theorem lex_13_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.pos 5075)] :=
  (lex_13_105_gate s).prop _ (List.Mem.head _)

theorem lex_13_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.neg 105), (Sat.Literal.pos 180)] :=
  (lex_13_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.pos 105), (Sat.Literal.neg 180)] :=
  (lex_13_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.neg 105), (Sat.Literal.neg 180), (Sat.Literal.pos 5076)] :=
  (lex_13_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5075), (Sat.Literal.pos 105), (Sat.Literal.pos 180), (Sat.Literal.pos 5076)] :=
  (lex_13_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5076) = lexBefore s permutation13 104 := by
  exact (positive_lex_of_descriptor s 5076 permutation13 105 (by rfl)).trans ((lex_skipped s permutation13 104 105 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation13 104) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation13 104 by rw [image13_eq]; rfl))

theorem lex_13_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5077) (Sat.Literal.pos 5076) (Sat.Literal.pos 104) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation13 104 (assignment s)
    (Sat.Literal.pos 5077) (Sat.Literal.pos 5076) (Sat.Literal.pos 104) (Sat.Literal.pos 52) (positive_of_descriptor s 5077 (.lex permutation13 104) (by rfl)) (lex_13_104_prefix s) (positive_select s 104) (lex_13_104_image s)

theorem lex_13_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.pos 104), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation13 104 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5076) (Sat.Literal.pos 104) (Sat.Literal.pos 52) (lex_13_104_prefix s) (positive_select s 104) (lex_13_104_image s)

theorem lex_13_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.pos 5076)] :=
  (lex_13_104_gate s).prop _ (List.Mem.head _)

theorem lex_13_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.neg 104), (Sat.Literal.pos 52)] :=
  (lex_13_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.pos 104), (Sat.Literal.neg 52)] :=
  (lex_13_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.neg 104), (Sat.Literal.neg 52), (Sat.Literal.pos 5077)] :=
  (lex_13_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5076), (Sat.Literal.pos 104), (Sat.Literal.pos 52), (Sat.Literal.pos 5077)] :=
  (lex_13_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5077) = lexBefore s permutation13 103 := by
  exact (positive_lex_of_descriptor s 5077 permutation13 104 (by rfl)).trans ((lex_skipped s permutation13 103 104 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation13 103) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation13 103 by rw [image13_eq]; rfl))

theorem lex_13_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5078) (Sat.Literal.pos 5077) (Sat.Literal.pos 103) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation13 103 (assignment s)
    (Sat.Literal.pos 5078) (Sat.Literal.pos 5077) (Sat.Literal.pos 103) (Sat.Literal.pos 179) (positive_of_descriptor s 5078 (.lex permutation13 103) (by rfl)) (lex_13_103_prefix s) (positive_select s 103) (lex_13_103_image s)

theorem lex_13_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.pos 103), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation13 103 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5077) (Sat.Literal.pos 103) (Sat.Literal.pos 179) (lex_13_103_prefix s) (positive_select s 103) (lex_13_103_image s)

theorem lex_13_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.pos 5077)] :=
  (lex_13_103_gate s).prop _ (List.Mem.head _)

theorem lex_13_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.neg 103), (Sat.Literal.pos 179)] :=
  (lex_13_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.pos 103), (Sat.Literal.neg 179)] :=
  (lex_13_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.neg 103), (Sat.Literal.neg 179), (Sat.Literal.pos 5078)] :=
  (lex_13_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5077), (Sat.Literal.pos 103), (Sat.Literal.pos 179), (Sat.Literal.pos 5078)] :=
  (lex_13_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5078) = lexBefore s permutation13 102 := by
  exact (positive_lex_of_descriptor s 5078 permutation13 103 (by rfl)).trans ((lex_skipped s permutation13 102 103 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation13 102) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation13 102 by rw [image13_eq]; rfl))

theorem lex_13_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5079) (Sat.Literal.pos 5078) (Sat.Literal.pos 102) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation13 102 (assignment s)
    (Sat.Literal.pos 5079) (Sat.Literal.pos 5078) (Sat.Literal.pos 102) (Sat.Literal.pos 51) (positive_of_descriptor s 5079 (.lex permutation13 102) (by rfl)) (lex_13_102_prefix s) (positive_select s 102) (lex_13_102_image s)

theorem lex_13_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.pos 102), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation13 102 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5078) (Sat.Literal.pos 102) (Sat.Literal.pos 51) (lex_13_102_prefix s) (positive_select s 102) (lex_13_102_image s)

theorem lex_13_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.pos 5078)] :=
  (lex_13_102_gate s).prop _ (List.Mem.head _)

theorem lex_13_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.neg 102), (Sat.Literal.pos 51)] :=
  (lex_13_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.pos 102), (Sat.Literal.neg 51)] :=
  (lex_13_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.neg 102), (Sat.Literal.neg 51), (Sat.Literal.pos 5079)] :=
  (lex_13_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5078), (Sat.Literal.pos 102), (Sat.Literal.pos 51), (Sat.Literal.pos 5079)] :=
  (lex_13_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5079) = lexBefore s permutation13 101 := by
  exact (positive_lex_of_descriptor s 5079 permutation13 102 (by rfl)).trans ((lex_skipped s permutation13 101 102 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation13 101) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation13 101 by rw [image13_eq]; rfl))

theorem lex_13_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5080) (Sat.Literal.pos 5079) (Sat.Literal.pos 101) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation13 101 (assignment s)
    (Sat.Literal.pos 5080) (Sat.Literal.pos 5079) (Sat.Literal.pos 101) (Sat.Literal.pos 178) (positive_of_descriptor s 5080 (.lex permutation13 101) (by rfl)) (lex_13_101_prefix s) (positive_select s 101) (lex_13_101_image s)

theorem lex_13_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.pos 101), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation13 101 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5079) (Sat.Literal.pos 101) (Sat.Literal.pos 178) (lex_13_101_prefix s) (positive_select s 101) (lex_13_101_image s)

theorem lex_13_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.pos 5079)] :=
  (lex_13_101_gate s).prop _ (List.Mem.head _)

theorem lex_13_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.neg 101), (Sat.Literal.pos 178)] :=
  (lex_13_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.pos 101), (Sat.Literal.neg 178)] :=
  (lex_13_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.neg 101), (Sat.Literal.neg 178), (Sat.Literal.pos 5080)] :=
  (lex_13_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5079), (Sat.Literal.pos 101), (Sat.Literal.pos 178), (Sat.Literal.pos 5080)] :=
  (lex_13_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5080) = lexBefore s permutation13 100 := by
  exact (positive_lex_of_descriptor s 5080 permutation13 101 (by rfl)).trans ((lex_skipped s permutation13 100 101 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation13 100) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation13 100 by rw [image13_eq]; rfl))

theorem lex_13_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5081) (Sat.Literal.pos 5080) (Sat.Literal.pos 100) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation13 100 (assignment s)
    (Sat.Literal.pos 5081) (Sat.Literal.pos 5080) (Sat.Literal.pos 100) (Sat.Literal.pos 50) (positive_of_descriptor s 5081 (.lex permutation13 100) (by rfl)) (lex_13_100_prefix s) (positive_select s 100) (lex_13_100_image s)

theorem lex_13_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.pos 100), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation13 100 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5080) (Sat.Literal.pos 100) (Sat.Literal.pos 50) (lex_13_100_prefix s) (positive_select s 100) (lex_13_100_image s)

theorem lex_13_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.pos 5080)] :=
  (lex_13_100_gate s).prop _ (List.Mem.head _)

theorem lex_13_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.neg 100), (Sat.Literal.pos 50)] :=
  (lex_13_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.pos 100), (Sat.Literal.neg 50)] :=
  (lex_13_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.neg 100), (Sat.Literal.neg 50), (Sat.Literal.pos 5081)] :=
  (lex_13_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5080), (Sat.Literal.pos 100), (Sat.Literal.pos 50), (Sat.Literal.pos 5081)] :=
  (lex_13_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5081) = lexBefore s permutation13 99 := by
  exact (positive_lex_of_descriptor s 5081 permutation13 100 (by rfl)).trans ((lex_skipped s permutation13 99 100 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation13 99) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation13 99 by rw [image13_eq]; rfl))

theorem lex_13_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5082) (Sat.Literal.pos 5081) (Sat.Literal.pos 99) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation13 99 (assignment s)
    (Sat.Literal.pos 5082) (Sat.Literal.pos 5081) (Sat.Literal.pos 99) (Sat.Literal.pos 177) (positive_of_descriptor s 5082 (.lex permutation13 99) (by rfl)) (lex_13_99_prefix s) (positive_select s 99) (lex_13_99_image s)

theorem lex_13_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.pos 99), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation13 99 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5081) (Sat.Literal.pos 99) (Sat.Literal.pos 177) (lex_13_99_prefix s) (positive_select s 99) (lex_13_99_image s)

theorem lex_13_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.pos 5081)] :=
  (lex_13_99_gate s).prop _ (List.Mem.head _)

theorem lex_13_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.neg 99), (Sat.Literal.pos 177)] :=
  (lex_13_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.pos 99), (Sat.Literal.neg 177)] :=
  (lex_13_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.neg 99), (Sat.Literal.neg 177), (Sat.Literal.pos 5082)] :=
  (lex_13_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5081), (Sat.Literal.pos 99), (Sat.Literal.pos 177), (Sat.Literal.pos 5082)] :=
  (lex_13_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5082) = lexBefore s permutation13 98 := by
  exact (positive_lex_of_descriptor s 5082 permutation13 99 (by rfl)).trans ((lex_skipped s permutation13 98 99 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation13 98) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation13 98 by rw [image13_eq]; rfl))

theorem lex_13_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5083) (Sat.Literal.pos 5082) (Sat.Literal.pos 98) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation13 98 (assignment s)
    (Sat.Literal.pos 5083) (Sat.Literal.pos 5082) (Sat.Literal.pos 98) (Sat.Literal.pos 49) (positive_of_descriptor s 5083 (.lex permutation13 98) (by rfl)) (lex_13_98_prefix s) (positive_select s 98) (lex_13_98_image s)

theorem lex_13_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.pos 98), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation13 98 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5082) (Sat.Literal.pos 98) (Sat.Literal.pos 49) (lex_13_98_prefix s) (positive_select s 98) (lex_13_98_image s)

theorem lex_13_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.pos 5082)] :=
  (lex_13_98_gate s).prop _ (List.Mem.head _)

theorem lex_13_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.neg 98), (Sat.Literal.pos 49)] :=
  (lex_13_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.pos 98), (Sat.Literal.neg 49)] :=
  (lex_13_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.neg 98), (Sat.Literal.neg 49), (Sat.Literal.pos 5083)] :=
  (lex_13_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5082), (Sat.Literal.pos 98), (Sat.Literal.pos 49), (Sat.Literal.pos 5083)] :=
  (lex_13_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5083) = lexBefore s permutation13 97 := by
  exact (positive_lex_of_descriptor s 5083 permutation13 98 (by rfl)).trans ((lex_skipped s permutation13 97 98 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation13 97) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation13 97 by rw [image13_eq]; rfl))

theorem lex_13_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5084) (Sat.Literal.pos 5083) (Sat.Literal.pos 97) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation13 97 (assignment s)
    (Sat.Literal.pos 5084) (Sat.Literal.pos 5083) (Sat.Literal.pos 97) (Sat.Literal.pos 176) (positive_of_descriptor s 5084 (.lex permutation13 97) (by rfl)) (lex_13_97_prefix s) (positive_select s 97) (lex_13_97_image s)

theorem lex_13_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.pos 97), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation13 97 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5083) (Sat.Literal.pos 97) (Sat.Literal.pos 176) (lex_13_97_prefix s) (positive_select s 97) (lex_13_97_image s)

theorem lex_13_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.pos 5083)] :=
  (lex_13_97_gate s).prop _ (List.Mem.head _)

theorem lex_13_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.neg 97), (Sat.Literal.pos 176)] :=
  (lex_13_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.pos 97), (Sat.Literal.neg 176)] :=
  (lex_13_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.neg 97), (Sat.Literal.neg 176), (Sat.Literal.pos 5084)] :=
  (lex_13_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5083), (Sat.Literal.pos 97), (Sat.Literal.pos 176), (Sat.Literal.pos 5084)] :=
  (lex_13_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5084) = lexBefore s permutation13 96 := by
  exact (positive_lex_of_descriptor s 5084 permutation13 97 (by rfl)).trans ((lex_skipped s permutation13 96 97 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation13 96) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation13 96 by rw [image13_eq]; rfl))

theorem lex_13_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5085) (Sat.Literal.pos 5084) (Sat.Literal.pos 96) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation13 96 (assignment s)
    (Sat.Literal.pos 5085) (Sat.Literal.pos 5084) (Sat.Literal.pos 96) (Sat.Literal.pos 48) (positive_of_descriptor s 5085 (.lex permutation13 96) (by rfl)) (lex_13_96_prefix s) (positive_select s 96) (lex_13_96_image s)

theorem lex_13_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.pos 96), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation13 96 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5084) (Sat.Literal.pos 96) (Sat.Literal.pos 48) (lex_13_96_prefix s) (positive_select s 96) (lex_13_96_image s)

theorem lex_13_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.pos 5084)] :=
  (lex_13_96_gate s).prop _ (List.Mem.head _)

theorem lex_13_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.neg 96), (Sat.Literal.pos 48)] :=
  (lex_13_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.pos 96), (Sat.Literal.neg 48)] :=
  (lex_13_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.neg 96), (Sat.Literal.neg 48), (Sat.Literal.pos 5085)] :=
  (lex_13_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5084), (Sat.Literal.pos 96), (Sat.Literal.pos 48), (Sat.Literal.pos 5085)] :=
  (lex_13_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5085) = lexBefore s permutation13 95 := by
  exact (positive_lex_of_descriptor s 5085 permutation13 96 (by rfl)).trans ((lex_skipped s permutation13 95 96 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation13 95) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation13 95 by rw [image13_eq]; rfl))

theorem lex_13_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5086) (Sat.Literal.pos 5085) (Sat.Literal.pos 95) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation13 95 (assignment s)
    (Sat.Literal.pos 5086) (Sat.Literal.pos 5085) (Sat.Literal.pos 95) (Sat.Literal.pos 175) (positive_of_descriptor s 5086 (.lex permutation13 95) (by rfl)) (lex_13_95_prefix s) (positive_select s 95) (lex_13_95_image s)

theorem lex_13_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.pos 95), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation13 95 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5085) (Sat.Literal.pos 95) (Sat.Literal.pos 175) (lex_13_95_prefix s) (positive_select s 95) (lex_13_95_image s)

theorem lex_13_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.pos 5085)] :=
  (lex_13_95_gate s).prop _ (List.Mem.head _)

theorem lex_13_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.neg 95), (Sat.Literal.pos 175)] :=
  (lex_13_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.pos 95), (Sat.Literal.neg 175)] :=
  (lex_13_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.neg 95), (Sat.Literal.neg 175), (Sat.Literal.pos 5086)] :=
  (lex_13_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5085), (Sat.Literal.pos 95), (Sat.Literal.pos 175), (Sat.Literal.pos 5086)] :=
  (lex_13_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5086) = lexBefore s permutation13 94 := by
  exact (positive_lex_of_descriptor s 5086 permutation13 95 (by rfl)).trans ((lex_skipped s permutation13 94 95 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation13 94) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation13 94 by rw [image13_eq]; rfl))

theorem lex_13_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5087) (Sat.Literal.pos 5086) (Sat.Literal.pos 94) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation13 94 (assignment s)
    (Sat.Literal.pos 5087) (Sat.Literal.pos 5086) (Sat.Literal.pos 94) (Sat.Literal.pos 47) (positive_of_descriptor s 5087 (.lex permutation13 94) (by rfl)) (lex_13_94_prefix s) (positive_select s 94) (lex_13_94_image s)

theorem lex_13_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.pos 94), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation13 94 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5086) (Sat.Literal.pos 94) (Sat.Literal.pos 47) (lex_13_94_prefix s) (positive_select s 94) (lex_13_94_image s)

theorem lex_13_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.pos 5086)] :=
  (lex_13_94_gate s).prop _ (List.Mem.head _)

theorem lex_13_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.neg 94), (Sat.Literal.pos 47)] :=
  (lex_13_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.pos 94), (Sat.Literal.neg 47)] :=
  (lex_13_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.neg 94), (Sat.Literal.neg 47), (Sat.Literal.pos 5087)] :=
  (lex_13_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5086), (Sat.Literal.pos 94), (Sat.Literal.pos 47), (Sat.Literal.pos 5087)] :=
  (lex_13_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5087) = lexBefore s permutation13 93 := by
  exact (positive_lex_of_descriptor s 5087 permutation13 94 (by rfl)).trans ((lex_skipped s permutation13 93 94 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation13 93) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation13 93 by rw [image13_eq]; rfl))

theorem lex_13_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5088) (Sat.Literal.pos 5087) (Sat.Literal.pos 93) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation13 93 (assignment s)
    (Sat.Literal.pos 5088) (Sat.Literal.pos 5087) (Sat.Literal.pos 93) (Sat.Literal.pos 174) (positive_of_descriptor s 5088 (.lex permutation13 93) (by rfl)) (lex_13_93_prefix s) (positive_select s 93) (lex_13_93_image s)

theorem lex_13_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.pos 93), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation13 93 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5087) (Sat.Literal.pos 93) (Sat.Literal.pos 174) (lex_13_93_prefix s) (positive_select s 93) (lex_13_93_image s)

theorem lex_13_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.pos 5087)] :=
  (lex_13_93_gate s).prop _ (List.Mem.head _)

theorem lex_13_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.neg 93), (Sat.Literal.pos 174)] :=
  (lex_13_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.pos 93), (Sat.Literal.neg 174)] :=
  (lex_13_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.neg 93), (Sat.Literal.neg 174), (Sat.Literal.pos 5088)] :=
  (lex_13_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5087), (Sat.Literal.pos 93), (Sat.Literal.pos 174), (Sat.Literal.pos 5088)] :=
  (lex_13_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5088) = lexBefore s permutation13 92 := by
  exact (positive_lex_of_descriptor s 5088 permutation13 93 (by rfl)).trans ((lex_skipped s permutation13 92 93 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation13 92) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation13 92 by rw [image13_eq]; rfl))

theorem lex_13_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5089) (Sat.Literal.pos 5088) (Sat.Literal.pos 92) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation13 92 (assignment s)
    (Sat.Literal.pos 5089) (Sat.Literal.pos 5088) (Sat.Literal.pos 92) (Sat.Literal.pos 46) (positive_of_descriptor s 5089 (.lex permutation13 92) (by rfl)) (lex_13_92_prefix s) (positive_select s 92) (lex_13_92_image s)

theorem lex_13_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.pos 92), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation13 92 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5088) (Sat.Literal.pos 92) (Sat.Literal.pos 46) (lex_13_92_prefix s) (positive_select s 92) (lex_13_92_image s)

theorem lex_13_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.pos 5088)] :=
  (lex_13_92_gate s).prop _ (List.Mem.head _)

theorem lex_13_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.neg 92), (Sat.Literal.pos 46)] :=
  (lex_13_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.pos 92), (Sat.Literal.neg 46)] :=
  (lex_13_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.neg 92), (Sat.Literal.neg 46), (Sat.Literal.pos 5089)] :=
  (lex_13_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5088), (Sat.Literal.pos 92), (Sat.Literal.pos 46), (Sat.Literal.pos 5089)] :=
  (lex_13_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5089) = lexBefore s permutation13 91 := by
  exact (positive_lex_of_descriptor s 5089 permutation13 92 (by rfl)).trans ((lex_skipped s permutation13 91 92 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation13 91) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation13 91 by rw [image13_eq]; rfl))

theorem lex_13_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5090) (Sat.Literal.pos 5089) (Sat.Literal.pos 91) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation13 91 (assignment s)
    (Sat.Literal.pos 5090) (Sat.Literal.pos 5089) (Sat.Literal.pos 91) (Sat.Literal.pos 173) (positive_of_descriptor s 5090 (.lex permutation13 91) (by rfl)) (lex_13_91_prefix s) (positive_select s 91) (lex_13_91_image s)

theorem lex_13_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.pos 91), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation13 91 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5089) (Sat.Literal.pos 91) (Sat.Literal.pos 173) (lex_13_91_prefix s) (positive_select s 91) (lex_13_91_image s)

theorem lex_13_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.pos 5089)] :=
  (lex_13_91_gate s).prop _ (List.Mem.head _)

theorem lex_13_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.neg 91), (Sat.Literal.pos 173)] :=
  (lex_13_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.pos 91), (Sat.Literal.neg 173)] :=
  (lex_13_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.neg 91), (Sat.Literal.neg 173), (Sat.Literal.pos 5090)] :=
  (lex_13_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5089), (Sat.Literal.pos 91), (Sat.Literal.pos 173), (Sat.Literal.pos 5090)] :=
  (lex_13_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5090) = lexBefore s permutation13 90 := by
  exact (positive_lex_of_descriptor s 5090 permutation13 91 (by rfl)).trans ((lex_skipped s permutation13 90 91 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation13 90) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation13 90 by rw [image13_eq]; rfl))

theorem lex_13_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5091) (Sat.Literal.pos 5090) (Sat.Literal.pos 90) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation13 90 (assignment s)
    (Sat.Literal.pos 5091) (Sat.Literal.pos 5090) (Sat.Literal.pos 90) (Sat.Literal.pos 45) (positive_of_descriptor s 5091 (.lex permutation13 90) (by rfl)) (lex_13_90_prefix s) (positive_select s 90) (lex_13_90_image s)

theorem lex_13_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.pos 90), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation13 90 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5090) (Sat.Literal.pos 90) (Sat.Literal.pos 45) (lex_13_90_prefix s) (positive_select s 90) (lex_13_90_image s)

theorem lex_13_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.pos 5090)] :=
  (lex_13_90_gate s).prop _ (List.Mem.head _)

theorem lex_13_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.neg 90), (Sat.Literal.pos 45)] :=
  (lex_13_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.pos 90), (Sat.Literal.neg 45)] :=
  (lex_13_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.neg 90), (Sat.Literal.neg 45), (Sat.Literal.pos 5091)] :=
  (lex_13_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5090), (Sat.Literal.pos 90), (Sat.Literal.pos 45), (Sat.Literal.pos 5091)] :=
  (lex_13_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5091) = lexBefore s permutation13 89 := by
  exact (positive_lex_of_descriptor s 5091 permutation13 90 (by rfl)).trans ((lex_skipped s permutation13 89 90 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation13 89) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation13 89 by rw [image13_eq]; rfl))

theorem lex_13_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5092) (Sat.Literal.pos 5091) (Sat.Literal.pos 89) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation13 89 (assignment s)
    (Sat.Literal.pos 5092) (Sat.Literal.pos 5091) (Sat.Literal.pos 89) (Sat.Literal.pos 172) (positive_of_descriptor s 5092 (.lex permutation13 89) (by rfl)) (lex_13_89_prefix s) (positive_select s 89) (lex_13_89_image s)

theorem lex_13_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.pos 89), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation13 89 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5091) (Sat.Literal.pos 89) (Sat.Literal.pos 172) (lex_13_89_prefix s) (positive_select s 89) (lex_13_89_image s)

theorem lex_13_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.pos 5091)] :=
  (lex_13_89_gate s).prop _ (List.Mem.head _)

theorem lex_13_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.neg 89), (Sat.Literal.pos 172)] :=
  (lex_13_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.pos 89), (Sat.Literal.neg 172)] :=
  (lex_13_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.neg 89), (Sat.Literal.neg 172), (Sat.Literal.pos 5092)] :=
  (lex_13_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5091), (Sat.Literal.pos 89), (Sat.Literal.pos 172), (Sat.Literal.pos 5092)] :=
  (lex_13_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5092) = lexBefore s permutation13 88 := by
  exact (positive_lex_of_descriptor s 5092 permutation13 89 (by rfl)).trans ((lex_skipped s permutation13 88 89 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation13 88) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation13 88 by rw [image13_eq]; rfl))

theorem lex_13_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5093) (Sat.Literal.pos 5092) (Sat.Literal.pos 88) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation13 88 (assignment s)
    (Sat.Literal.pos 5093) (Sat.Literal.pos 5092) (Sat.Literal.pos 88) (Sat.Literal.pos 44) (positive_of_descriptor s 5093 (.lex permutation13 88) (by rfl)) (lex_13_88_prefix s) (positive_select s 88) (lex_13_88_image s)

theorem lex_13_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.pos 88), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation13 88 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5092) (Sat.Literal.pos 88) (Sat.Literal.pos 44) (lex_13_88_prefix s) (positive_select s 88) (lex_13_88_image s)

theorem lex_13_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.pos 5092)] :=
  (lex_13_88_gate s).prop _ (List.Mem.head _)

theorem lex_13_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.neg 88), (Sat.Literal.pos 44)] :=
  (lex_13_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.pos 88), (Sat.Literal.neg 44)] :=
  (lex_13_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.neg 88), (Sat.Literal.neg 44), (Sat.Literal.pos 5093)] :=
  (lex_13_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5092), (Sat.Literal.pos 88), (Sat.Literal.pos 44), (Sat.Literal.pos 5093)] :=
  (lex_13_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5093) = lexBefore s permutation13 87 := by
  exact (positive_lex_of_descriptor s 5093 permutation13 88 (by rfl)).trans ((lex_skipped s permutation13 87 88 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation13 87) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation13 87 by rw [image13_eq]; rfl))

theorem lex_13_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5094) (Sat.Literal.pos 5093) (Sat.Literal.pos 87) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation13 87 (assignment s)
    (Sat.Literal.pos 5094) (Sat.Literal.pos 5093) (Sat.Literal.pos 87) (Sat.Literal.pos 171) (positive_of_descriptor s 5094 (.lex permutation13 87) (by rfl)) (lex_13_87_prefix s) (positive_select s 87) (lex_13_87_image s)

theorem lex_13_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.pos 87), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation13 87 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5093) (Sat.Literal.pos 87) (Sat.Literal.pos 171) (lex_13_87_prefix s) (positive_select s 87) (lex_13_87_image s)

theorem lex_13_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.pos 5093)] :=
  (lex_13_87_gate s).prop _ (List.Mem.head _)

theorem lex_13_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.neg 87), (Sat.Literal.pos 171)] :=
  (lex_13_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.pos 87), (Sat.Literal.neg 171)] :=
  (lex_13_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.neg 87), (Sat.Literal.neg 171), (Sat.Literal.pos 5094)] :=
  (lex_13_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5093), (Sat.Literal.pos 87), (Sat.Literal.pos 171), (Sat.Literal.pos 5094)] :=
  (lex_13_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5094) = lexBefore s permutation13 86 := by
  exact (positive_lex_of_descriptor s 5094 permutation13 87 (by rfl)).trans ((lex_skipped s permutation13 86 87 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation13 86) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation13 86 by rw [image13_eq]; rfl))

theorem lex_13_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5095) (Sat.Literal.pos 5094) (Sat.Literal.pos 86) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation13 86 (assignment s)
    (Sat.Literal.pos 5095) (Sat.Literal.pos 5094) (Sat.Literal.pos 86) (Sat.Literal.pos 43) (positive_of_descriptor s 5095 (.lex permutation13 86) (by rfl)) (lex_13_86_prefix s) (positive_select s 86) (lex_13_86_image s)

theorem lex_13_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.pos 86), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation13 86 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5094) (Sat.Literal.pos 86) (Sat.Literal.pos 43) (lex_13_86_prefix s) (positive_select s 86) (lex_13_86_image s)

theorem lex_13_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.pos 5094)] :=
  (lex_13_86_gate s).prop _ (List.Mem.head _)

theorem lex_13_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.neg 86), (Sat.Literal.pos 43)] :=
  (lex_13_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.pos 86), (Sat.Literal.neg 43)] :=
  (lex_13_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.neg 86), (Sat.Literal.neg 43), (Sat.Literal.pos 5095)] :=
  (lex_13_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5094), (Sat.Literal.pos 86), (Sat.Literal.pos 43), (Sat.Literal.pos 5095)] :=
  (lex_13_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5095) = lexBefore s permutation13 85 := by
  exact (positive_lex_of_descriptor s 5095 permutation13 86 (by rfl)).trans ((lex_skipped s permutation13 85 86 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation13 85) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation13 85 by rw [image13_eq]; rfl))

theorem lex_13_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5096) (Sat.Literal.pos 5095) (Sat.Literal.pos 85) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation13 85 (assignment s)
    (Sat.Literal.pos 5096) (Sat.Literal.pos 5095) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (positive_of_descriptor s 5096 (.lex permutation13 85) (by rfl)) (lex_13_85_prefix s) (positive_select s 85) (lex_13_85_image s)

theorem lex_13_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation13 85 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5095) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (lex_13_85_prefix s) (positive_select s 85) (lex_13_85_image s)

theorem lex_13_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.pos 5095)] :=
  (lex_13_85_gate s).prop _ (List.Mem.head _)

theorem lex_13_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.neg 85), (Sat.Literal.pos 170)] :=
  (lex_13_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] :=
  (lex_13_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.neg 85), (Sat.Literal.neg 170), (Sat.Literal.pos 5096)] :=
  (lex_13_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5095), (Sat.Literal.pos 85), (Sat.Literal.pos 170), (Sat.Literal.pos 5096)] :=
  (lex_13_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5096) = lexBefore s permutation13 84 := by
  exact (positive_lex_of_descriptor s 5096 permutation13 85 (by rfl)).trans ((lex_skipped s permutation13 84 85 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation13 84) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation13 84 by rw [image13_eq]; rfl))

theorem lex_13_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5097) (Sat.Literal.pos 5096) (Sat.Literal.pos 84) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation13 84 (assignment s)
    (Sat.Literal.pos 5097) (Sat.Literal.pos 5096) (Sat.Literal.pos 84) (Sat.Literal.pos 42) (positive_of_descriptor s 5097 (.lex permutation13 84) (by rfl)) (lex_13_84_prefix s) (positive_select s 84) (lex_13_84_image s)

theorem lex_13_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.pos 84), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation13 84 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5096) (Sat.Literal.pos 84) (Sat.Literal.pos 42) (lex_13_84_prefix s) (positive_select s 84) (lex_13_84_image s)

theorem lex_13_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.pos 5096)] :=
  (lex_13_84_gate s).prop _ (List.Mem.head _)

theorem lex_13_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.neg 84), (Sat.Literal.pos 42)] :=
  (lex_13_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.pos 84), (Sat.Literal.neg 42)] :=
  (lex_13_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.neg 84), (Sat.Literal.neg 42), (Sat.Literal.pos 5097)] :=
  (lex_13_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5096), (Sat.Literal.pos 84), (Sat.Literal.pos 42), (Sat.Literal.pos 5097)] :=
  (lex_13_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5097) = lexBefore s permutation13 83 := by
  exact (positive_lex_of_descriptor s 5097 permutation13 84 (by rfl)).trans ((lex_skipped s permutation13 83 84 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation13 83) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation13 83 by rw [image13_eq]; rfl))

theorem lex_13_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5098) (Sat.Literal.pos 5097) (Sat.Literal.pos 83) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation13 83 (assignment s)
    (Sat.Literal.pos 5098) (Sat.Literal.pos 5097) (Sat.Literal.pos 83) (Sat.Literal.pos 169) (positive_of_descriptor s 5098 (.lex permutation13 83) (by rfl)) (lex_13_83_prefix s) (positive_select s 83) (lex_13_83_image s)

theorem lex_13_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.pos 83), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation13 83 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5097) (Sat.Literal.pos 83) (Sat.Literal.pos 169) (lex_13_83_prefix s) (positive_select s 83) (lex_13_83_image s)

theorem lex_13_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.pos 5097)] :=
  (lex_13_83_gate s).prop _ (List.Mem.head _)

theorem lex_13_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.neg 83), (Sat.Literal.pos 169)] :=
  (lex_13_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.pos 83), (Sat.Literal.neg 169)] :=
  (lex_13_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.neg 83), (Sat.Literal.neg 169), (Sat.Literal.pos 5098)] :=
  (lex_13_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5097), (Sat.Literal.pos 83), (Sat.Literal.pos 169), (Sat.Literal.pos 5098)] :=
  (lex_13_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5098) = lexBefore s permutation13 82 := by
  exact (positive_lex_of_descriptor s 5098 permutation13 83 (by rfl)).trans ((lex_skipped s permutation13 82 83 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation13 82) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation13 82 by rw [image13_eq]; rfl))

theorem lex_13_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5099) (Sat.Literal.pos 5098) (Sat.Literal.pos 82) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation13 82 (assignment s)
    (Sat.Literal.pos 5099) (Sat.Literal.pos 5098) (Sat.Literal.pos 82) (Sat.Literal.pos 41) (positive_of_descriptor s 5099 (.lex permutation13 82) (by rfl)) (lex_13_82_prefix s) (positive_select s 82) (lex_13_82_image s)

theorem lex_13_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.pos 82), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation13 82 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5098) (Sat.Literal.pos 82) (Sat.Literal.pos 41) (lex_13_82_prefix s) (positive_select s 82) (lex_13_82_image s)

theorem lex_13_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.pos 5098)] :=
  (lex_13_82_gate s).prop _ (List.Mem.head _)

theorem lex_13_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.neg 82), (Sat.Literal.pos 41)] :=
  (lex_13_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.pos 82), (Sat.Literal.neg 41)] :=
  (lex_13_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.neg 82), (Sat.Literal.neg 41), (Sat.Literal.pos 5099)] :=
  (lex_13_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5098), (Sat.Literal.pos 82), (Sat.Literal.pos 41), (Sat.Literal.pos 5099)] :=
  (lex_13_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5099) = lexBefore s permutation13 81 := by
  exact (positive_lex_of_descriptor s 5099 permutation13 82 (by rfl)).trans ((lex_skipped s permutation13 81 82 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation13 81) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation13 81 by rw [image13_eq]; rfl))

theorem lex_13_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5100) (Sat.Literal.pos 5099) (Sat.Literal.pos 81) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation13 81 (assignment s)
    (Sat.Literal.pos 5100) (Sat.Literal.pos 5099) (Sat.Literal.pos 81) (Sat.Literal.pos 168) (positive_of_descriptor s 5100 (.lex permutation13 81) (by rfl)) (lex_13_81_prefix s) (positive_select s 81) (lex_13_81_image s)

theorem lex_13_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.pos 81), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation13 81 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5099) (Sat.Literal.pos 81) (Sat.Literal.pos 168) (lex_13_81_prefix s) (positive_select s 81) (lex_13_81_image s)

theorem lex_13_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.pos 5099)] :=
  (lex_13_81_gate s).prop _ (List.Mem.head _)

theorem lex_13_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.neg 81), (Sat.Literal.pos 168)] :=
  (lex_13_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.pos 81), (Sat.Literal.neg 168)] :=
  (lex_13_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.neg 81), (Sat.Literal.neg 168), (Sat.Literal.pos 5100)] :=
  (lex_13_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5099), (Sat.Literal.pos 81), (Sat.Literal.pos 168), (Sat.Literal.pos 5100)] :=
  (lex_13_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5100) = lexBefore s permutation13 80 := by
  exact (positive_lex_of_descriptor s 5100 permutation13 81 (by rfl)).trans ((lex_skipped s permutation13 80 81 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation13 80) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation13 80 by rw [image13_eq]; rfl))

theorem lex_13_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5101) (Sat.Literal.pos 5100) (Sat.Literal.pos 80) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation13 80 (assignment s)
    (Sat.Literal.pos 5101) (Sat.Literal.pos 5100) (Sat.Literal.pos 80) (Sat.Literal.pos 40) (positive_of_descriptor s 5101 (.lex permutation13 80) (by rfl)) (lex_13_80_prefix s) (positive_select s 80) (lex_13_80_image s)

theorem lex_13_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.pos 80), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation13 80 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5100) (Sat.Literal.pos 80) (Sat.Literal.pos 40) (lex_13_80_prefix s) (positive_select s 80) (lex_13_80_image s)

theorem lex_13_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.pos 5100)] :=
  (lex_13_80_gate s).prop _ (List.Mem.head _)

theorem lex_13_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.neg 80), (Sat.Literal.pos 40)] :=
  (lex_13_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.pos 80), (Sat.Literal.neg 40)] :=
  (lex_13_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.neg 80), (Sat.Literal.neg 40), (Sat.Literal.pos 5101)] :=
  (lex_13_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5100), (Sat.Literal.pos 80), (Sat.Literal.pos 40), (Sat.Literal.pos 5101)] :=
  (lex_13_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5101) = lexBefore s permutation13 79 := by
  exact (positive_lex_of_descriptor s 5101 permutation13 80 (by rfl)).trans ((lex_skipped s permutation13 79 80 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation13 79) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation13 79 by rw [image13_eq]; rfl))

theorem lex_13_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5102) (Sat.Literal.pos 5101) (Sat.Literal.pos 79) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation13 79 (assignment s)
    (Sat.Literal.pos 5102) (Sat.Literal.pos 5101) (Sat.Literal.pos 79) (Sat.Literal.pos 167) (positive_of_descriptor s 5102 (.lex permutation13 79) (by rfl)) (lex_13_79_prefix s) (positive_select s 79) (lex_13_79_image s)

theorem lex_13_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.pos 79), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation13 79 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5101) (Sat.Literal.pos 79) (Sat.Literal.pos 167) (lex_13_79_prefix s) (positive_select s 79) (lex_13_79_image s)

theorem lex_13_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.pos 5101)] :=
  (lex_13_79_gate s).prop _ (List.Mem.head _)

theorem lex_13_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.neg 79), (Sat.Literal.pos 167)] :=
  (lex_13_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.pos 79), (Sat.Literal.neg 167)] :=
  (lex_13_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.neg 79), (Sat.Literal.neg 167), (Sat.Literal.pos 5102)] :=
  (lex_13_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5101), (Sat.Literal.pos 79), (Sat.Literal.pos 167), (Sat.Literal.pos 5102)] :=
  (lex_13_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5102) = lexBefore s permutation13 78 := by
  exact (positive_lex_of_descriptor s 5102 permutation13 79 (by rfl)).trans ((lex_skipped s permutation13 78 79 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation13 78) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation13 78 by rw [image13_eq]; rfl))

theorem lex_13_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5103) (Sat.Literal.pos 5102) (Sat.Literal.pos 78) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation13 78 (assignment s)
    (Sat.Literal.pos 5103) (Sat.Literal.pos 5102) (Sat.Literal.pos 78) (Sat.Literal.pos 39) (positive_of_descriptor s 5103 (.lex permutation13 78) (by rfl)) (lex_13_78_prefix s) (positive_select s 78) (lex_13_78_image s)

theorem lex_13_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.pos 78), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation13 78 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5102) (Sat.Literal.pos 78) (Sat.Literal.pos 39) (lex_13_78_prefix s) (positive_select s 78) (lex_13_78_image s)

theorem lex_13_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.pos 5102)] :=
  (lex_13_78_gate s).prop _ (List.Mem.head _)

theorem lex_13_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.neg 78), (Sat.Literal.pos 39)] :=
  (lex_13_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.pos 78), (Sat.Literal.neg 39)] :=
  (lex_13_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.neg 78), (Sat.Literal.neg 39), (Sat.Literal.pos 5103)] :=
  (lex_13_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5102), (Sat.Literal.pos 78), (Sat.Literal.pos 39), (Sat.Literal.pos 5103)] :=
  (lex_13_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5103) = lexBefore s permutation13 77 := by
  exact (positive_lex_of_descriptor s 5103 permutation13 78 (by rfl)).trans ((lex_skipped s permutation13 77 78 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation13 77) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation13 77 by rw [image13_eq]; rfl))

theorem lex_13_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5104) (Sat.Literal.pos 5103) (Sat.Literal.pos 77) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation13 77 (assignment s)
    (Sat.Literal.pos 5104) (Sat.Literal.pos 5103) (Sat.Literal.pos 77) (Sat.Literal.pos 166) (positive_of_descriptor s 5104 (.lex permutation13 77) (by rfl)) (lex_13_77_prefix s) (positive_select s 77) (lex_13_77_image s)

theorem lex_13_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.pos 77), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation13 77 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5103) (Sat.Literal.pos 77) (Sat.Literal.pos 166) (lex_13_77_prefix s) (positive_select s 77) (lex_13_77_image s)

theorem lex_13_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.pos 5103)] :=
  (lex_13_77_gate s).prop _ (List.Mem.head _)

theorem lex_13_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.neg 77), (Sat.Literal.pos 166)] :=
  (lex_13_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.pos 77), (Sat.Literal.neg 166)] :=
  (lex_13_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.neg 77), (Sat.Literal.neg 166), (Sat.Literal.pos 5104)] :=
  (lex_13_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5103), (Sat.Literal.pos 77), (Sat.Literal.pos 166), (Sat.Literal.pos 5104)] :=
  (lex_13_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5104) = lexBefore s permutation13 76 := by
  exact (positive_lex_of_descriptor s 5104 permutation13 77 (by rfl)).trans ((lex_skipped s permutation13 76 77 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation13 76) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation13 76 by rw [image13_eq]; rfl))

theorem lex_13_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5105) (Sat.Literal.pos 5104) (Sat.Literal.pos 76) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation13 76 (assignment s)
    (Sat.Literal.pos 5105) (Sat.Literal.pos 5104) (Sat.Literal.pos 76) (Sat.Literal.pos 38) (positive_of_descriptor s 5105 (.lex permutation13 76) (by rfl)) (lex_13_76_prefix s) (positive_select s 76) (lex_13_76_image s)

theorem lex_13_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.pos 76), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation13 76 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5104) (Sat.Literal.pos 76) (Sat.Literal.pos 38) (lex_13_76_prefix s) (positive_select s 76) (lex_13_76_image s)

theorem lex_13_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.pos 5104)] :=
  (lex_13_76_gate s).prop _ (List.Mem.head _)

theorem lex_13_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.neg 76), (Sat.Literal.pos 38)] :=
  (lex_13_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.pos 76), (Sat.Literal.neg 38)] :=
  (lex_13_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.neg 76), (Sat.Literal.neg 38), (Sat.Literal.pos 5105)] :=
  (lex_13_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5104), (Sat.Literal.pos 76), (Sat.Literal.pos 38), (Sat.Literal.pos 5105)] :=
  (lex_13_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5105) = lexBefore s permutation13 75 := by
  exact (positive_lex_of_descriptor s 5105 permutation13 76 (by rfl)).trans ((lex_skipped s permutation13 75 76 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation13 75) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation13 75 by rw [image13_eq]; rfl))

theorem lex_13_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5106) (Sat.Literal.pos 5105) (Sat.Literal.pos 75) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation13 75 (assignment s)
    (Sat.Literal.pos 5106) (Sat.Literal.pos 5105) (Sat.Literal.pos 75) (Sat.Literal.pos 165) (positive_of_descriptor s 5106 (.lex permutation13 75) (by rfl)) (lex_13_75_prefix s) (positive_select s 75) (lex_13_75_image s)

theorem lex_13_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.pos 75), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation13 75 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5105) (Sat.Literal.pos 75) (Sat.Literal.pos 165) (lex_13_75_prefix s) (positive_select s 75) (lex_13_75_image s)

theorem lex_13_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.pos 5105)] :=
  (lex_13_75_gate s).prop _ (List.Mem.head _)

theorem lex_13_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.neg 75), (Sat.Literal.pos 165)] :=
  (lex_13_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.pos 75), (Sat.Literal.neg 165)] :=
  (lex_13_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.neg 75), (Sat.Literal.neg 165), (Sat.Literal.pos 5106)] :=
  (lex_13_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5105), (Sat.Literal.pos 75), (Sat.Literal.pos 165), (Sat.Literal.pos 5106)] :=
  (lex_13_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5106) = lexBefore s permutation13 74 := by
  exact (positive_lex_of_descriptor s 5106 permutation13 75 (by rfl)).trans ((lex_skipped s permutation13 74 75 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation13 74) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation13 74 by rw [image13_eq]; rfl))

theorem lex_13_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5107) (Sat.Literal.pos 5106) (Sat.Literal.pos 74) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation13 74 (assignment s)
    (Sat.Literal.pos 5107) (Sat.Literal.pos 5106) (Sat.Literal.pos 74) (Sat.Literal.pos 37) (positive_of_descriptor s 5107 (.lex permutation13 74) (by rfl)) (lex_13_74_prefix s) (positive_select s 74) (lex_13_74_image s)

theorem lex_13_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.pos 74), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation13 74 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5106) (Sat.Literal.pos 74) (Sat.Literal.pos 37) (lex_13_74_prefix s) (positive_select s 74) (lex_13_74_image s)

theorem lex_13_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.pos 5106)] :=
  (lex_13_74_gate s).prop _ (List.Mem.head _)

theorem lex_13_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.neg 74), (Sat.Literal.pos 37)] :=
  (lex_13_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.pos 74), (Sat.Literal.neg 37)] :=
  (lex_13_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.neg 74), (Sat.Literal.neg 37), (Sat.Literal.pos 5107)] :=
  (lex_13_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5106), (Sat.Literal.pos 74), (Sat.Literal.pos 37), (Sat.Literal.pos 5107)] :=
  (lex_13_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5107) = lexBefore s permutation13 73 := by
  exact (positive_lex_of_descriptor s 5107 permutation13 74 (by rfl)).trans ((lex_skipped s permutation13 73 74 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation13 73) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation13 73 by rw [image13_eq]; rfl))

theorem lex_13_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5108) (Sat.Literal.pos 5107) (Sat.Literal.pos 73) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation13 73 (assignment s)
    (Sat.Literal.pos 5108) (Sat.Literal.pos 5107) (Sat.Literal.pos 73) (Sat.Literal.pos 164) (positive_of_descriptor s 5108 (.lex permutation13 73) (by rfl)) (lex_13_73_prefix s) (positive_select s 73) (lex_13_73_image s)

theorem lex_13_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.pos 73), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation13 73 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5107) (Sat.Literal.pos 73) (Sat.Literal.pos 164) (lex_13_73_prefix s) (positive_select s 73) (lex_13_73_image s)

theorem lex_13_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.pos 5107)] :=
  (lex_13_73_gate s).prop _ (List.Mem.head _)

theorem lex_13_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.neg 73), (Sat.Literal.pos 164)] :=
  (lex_13_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.pos 73), (Sat.Literal.neg 164)] :=
  (lex_13_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.neg 73), (Sat.Literal.neg 164), (Sat.Literal.pos 5108)] :=
  (lex_13_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5107), (Sat.Literal.pos 73), (Sat.Literal.pos 164), (Sat.Literal.pos 5108)] :=
  (lex_13_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5108) = lexBefore s permutation13 72 := by
  exact (positive_lex_of_descriptor s 5108 permutation13 73 (by rfl)).trans ((lex_skipped s permutation13 72 73 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation13 72) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation13 72 by rw [image13_eq]; rfl))

theorem lex_13_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5109) (Sat.Literal.pos 5108) (Sat.Literal.pos 72) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation13 72 (assignment s)
    (Sat.Literal.pos 5109) (Sat.Literal.pos 5108) (Sat.Literal.pos 72) (Sat.Literal.pos 36) (positive_of_descriptor s 5109 (.lex permutation13 72) (by rfl)) (lex_13_72_prefix s) (positive_select s 72) (lex_13_72_image s)

theorem lex_13_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.pos 72), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation13 72 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5108) (Sat.Literal.pos 72) (Sat.Literal.pos 36) (lex_13_72_prefix s) (positive_select s 72) (lex_13_72_image s)

theorem lex_13_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.pos 5108)] :=
  (lex_13_72_gate s).prop _ (List.Mem.head _)

theorem lex_13_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.neg 72), (Sat.Literal.pos 36)] :=
  (lex_13_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.pos 72), (Sat.Literal.neg 36)] :=
  (lex_13_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.neg 72), (Sat.Literal.neg 36), (Sat.Literal.pos 5109)] :=
  (lex_13_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5108), (Sat.Literal.pos 72), (Sat.Literal.pos 36), (Sat.Literal.pos 5109)] :=
  (lex_13_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5109) = lexBefore s permutation13 71 := by
  exact (positive_lex_of_descriptor s 5109 permutation13 72 (by rfl)).trans ((lex_skipped s permutation13 71 72 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation13 71) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation13 71 by rw [image13_eq]; rfl))

theorem lex_13_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5110) (Sat.Literal.pos 5109) (Sat.Literal.pos 71) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation13 71 (assignment s)
    (Sat.Literal.pos 5110) (Sat.Literal.pos 5109) (Sat.Literal.pos 71) (Sat.Literal.pos 163) (positive_of_descriptor s 5110 (.lex permutation13 71) (by rfl)) (lex_13_71_prefix s) (positive_select s 71) (lex_13_71_image s)

theorem lex_13_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.pos 71), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation13 71 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5109) (Sat.Literal.pos 71) (Sat.Literal.pos 163) (lex_13_71_prefix s) (positive_select s 71) (lex_13_71_image s)

theorem lex_13_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.pos 5109)] :=
  (lex_13_71_gate s).prop _ (List.Mem.head _)

theorem lex_13_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.neg 71), (Sat.Literal.pos 163)] :=
  (lex_13_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.pos 71), (Sat.Literal.neg 163)] :=
  (lex_13_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.neg 71), (Sat.Literal.neg 163), (Sat.Literal.pos 5110)] :=
  (lex_13_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5109), (Sat.Literal.pos 71), (Sat.Literal.pos 163), (Sat.Literal.pos 5110)] :=
  (lex_13_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5110) = lexBefore s permutation13 70 := by
  exact (positive_lex_of_descriptor s 5110 permutation13 71 (by rfl)).trans ((lex_skipped s permutation13 70 71 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation13 70) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation13 70 by rw [image13_eq]; rfl))

theorem lex_13_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5111) (Sat.Literal.pos 5110) (Sat.Literal.pos 70) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation13 70 (assignment s)
    (Sat.Literal.pos 5111) (Sat.Literal.pos 5110) (Sat.Literal.pos 70) (Sat.Literal.pos 35) (positive_of_descriptor s 5111 (.lex permutation13 70) (by rfl)) (lex_13_70_prefix s) (positive_select s 70) (lex_13_70_image s)

theorem lex_13_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.pos 70), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation13 70 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5110) (Sat.Literal.pos 70) (Sat.Literal.pos 35) (lex_13_70_prefix s) (positive_select s 70) (lex_13_70_image s)

theorem lex_13_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.pos 5110)] :=
  (lex_13_70_gate s).prop _ (List.Mem.head _)

theorem lex_13_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.neg 70), (Sat.Literal.pos 35)] :=
  (lex_13_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.pos 70), (Sat.Literal.neg 35)] :=
  (lex_13_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.neg 70), (Sat.Literal.neg 35), (Sat.Literal.pos 5111)] :=
  (lex_13_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5110), (Sat.Literal.pos 70), (Sat.Literal.pos 35), (Sat.Literal.pos 5111)] :=
  (lex_13_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5111) = lexBefore s permutation13 69 := by
  exact (positive_lex_of_descriptor s 5111 permutation13 70 (by rfl)).trans ((lex_skipped s permutation13 69 70 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation13 69) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation13 69 by rw [image13_eq]; rfl))

theorem lex_13_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5112) (Sat.Literal.pos 5111) (Sat.Literal.pos 69) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation13 69 (assignment s)
    (Sat.Literal.pos 5112) (Sat.Literal.pos 5111) (Sat.Literal.pos 69) (Sat.Literal.pos 162) (positive_of_descriptor s 5112 (.lex permutation13 69) (by rfl)) (lex_13_69_prefix s) (positive_select s 69) (lex_13_69_image s)

theorem lex_13_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.pos 69), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation13 69 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5111) (Sat.Literal.pos 69) (Sat.Literal.pos 162) (lex_13_69_prefix s) (positive_select s 69) (lex_13_69_image s)

theorem lex_13_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.pos 5111)] :=
  (lex_13_69_gate s).prop _ (List.Mem.head _)

theorem lex_13_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.neg 69), (Sat.Literal.pos 162)] :=
  (lex_13_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.pos 69), (Sat.Literal.neg 162)] :=
  (lex_13_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.neg 69), (Sat.Literal.neg 162), (Sat.Literal.pos 5112)] :=
  (lex_13_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5111), (Sat.Literal.pos 69), (Sat.Literal.pos 162), (Sat.Literal.pos 5112)] :=
  (lex_13_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5112) = lexBefore s permutation13 68 := by
  exact (positive_lex_of_descriptor s 5112 permutation13 69 (by rfl)).trans ((lex_skipped s permutation13 68 69 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation13 68) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation13 68 by rw [image13_eq]; rfl))

theorem lex_13_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5113) (Sat.Literal.pos 5112) (Sat.Literal.pos 68) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation13 68 (assignment s)
    (Sat.Literal.pos 5113) (Sat.Literal.pos 5112) (Sat.Literal.pos 68) (Sat.Literal.pos 34) (positive_of_descriptor s 5113 (.lex permutation13 68) (by rfl)) (lex_13_68_prefix s) (positive_select s 68) (lex_13_68_image s)

theorem lex_13_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.pos 68), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation13 68 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5112) (Sat.Literal.pos 68) (Sat.Literal.pos 34) (lex_13_68_prefix s) (positive_select s 68) (lex_13_68_image s)

theorem lex_13_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.pos 5112)] :=
  (lex_13_68_gate s).prop _ (List.Mem.head _)

theorem lex_13_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.neg 68), (Sat.Literal.pos 34)] :=
  (lex_13_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.pos 68), (Sat.Literal.neg 34)] :=
  (lex_13_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.neg 68), (Sat.Literal.neg 34), (Sat.Literal.pos 5113)] :=
  (lex_13_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5112), (Sat.Literal.pos 68), (Sat.Literal.pos 34), (Sat.Literal.pos 5113)] :=
  (lex_13_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5113) = lexBefore s permutation13 67 := by
  exact (positive_lex_of_descriptor s 5113 permutation13 68 (by rfl)).trans ((lex_skipped s permutation13 67 68 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation13 67) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation13 67 by rw [image13_eq]; rfl))

theorem lex_13_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5114) (Sat.Literal.pos 5113) (Sat.Literal.pos 67) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation13 67 (assignment s)
    (Sat.Literal.pos 5114) (Sat.Literal.pos 5113) (Sat.Literal.pos 67) (Sat.Literal.pos 161) (positive_of_descriptor s 5114 (.lex permutation13 67) (by rfl)) (lex_13_67_prefix s) (positive_select s 67) (lex_13_67_image s)

theorem lex_13_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.pos 67), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation13 67 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5113) (Sat.Literal.pos 67) (Sat.Literal.pos 161) (lex_13_67_prefix s) (positive_select s 67) (lex_13_67_image s)

theorem lex_13_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.pos 5113)] :=
  (lex_13_67_gate s).prop _ (List.Mem.head _)

theorem lex_13_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.neg 67), (Sat.Literal.pos 161)] :=
  (lex_13_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.pos 67), (Sat.Literal.neg 161)] :=
  (lex_13_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.neg 67), (Sat.Literal.neg 161), (Sat.Literal.pos 5114)] :=
  (lex_13_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5113), (Sat.Literal.pos 67), (Sat.Literal.pos 161), (Sat.Literal.pos 5114)] :=
  (lex_13_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5114) = lexBefore s permutation13 66 := by
  exact (positive_lex_of_descriptor s 5114 permutation13 67 (by rfl)).trans ((lex_skipped s permutation13 66 67 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation13 66) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation13 66 by rw [image13_eq]; rfl))

theorem lex_13_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5115) (Sat.Literal.pos 5114) (Sat.Literal.pos 66) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation13 66 (assignment s)
    (Sat.Literal.pos 5115) (Sat.Literal.pos 5114) (Sat.Literal.pos 66) (Sat.Literal.pos 33) (positive_of_descriptor s 5115 (.lex permutation13 66) (by rfl)) (lex_13_66_prefix s) (positive_select s 66) (lex_13_66_image s)

theorem lex_13_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.pos 66), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation13 66 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5114) (Sat.Literal.pos 66) (Sat.Literal.pos 33) (lex_13_66_prefix s) (positive_select s 66) (lex_13_66_image s)

theorem lex_13_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.pos 5114)] :=
  (lex_13_66_gate s).prop _ (List.Mem.head _)

theorem lex_13_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.neg 66), (Sat.Literal.pos 33)] :=
  (lex_13_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.pos 66), (Sat.Literal.neg 33)] :=
  (lex_13_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.neg 66), (Sat.Literal.neg 33), (Sat.Literal.pos 5115)] :=
  (lex_13_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5114), (Sat.Literal.pos 66), (Sat.Literal.pos 33), (Sat.Literal.pos 5115)] :=
  (lex_13_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5115) = lexBefore s permutation13 65 := by
  exact (positive_lex_of_descriptor s 5115 permutation13 66 (by rfl)).trans ((lex_skipped s permutation13 65 66 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation13 65) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation13 65 by rw [image13_eq]; rfl))

theorem lex_13_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5116) (Sat.Literal.pos 5115) (Sat.Literal.pos 65) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation13 65 (assignment s)
    (Sat.Literal.pos 5116) (Sat.Literal.pos 5115) (Sat.Literal.pos 65) (Sat.Literal.pos 160) (positive_of_descriptor s 5116 (.lex permutation13 65) (by rfl)) (lex_13_65_prefix s) (positive_select s 65) (lex_13_65_image s)

theorem lex_13_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.pos 65), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation13 65 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5115) (Sat.Literal.pos 65) (Sat.Literal.pos 160) (lex_13_65_prefix s) (positive_select s 65) (lex_13_65_image s)

theorem lex_13_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.pos 5115)] :=
  (lex_13_65_gate s).prop _ (List.Mem.head _)

theorem lex_13_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.neg 65), (Sat.Literal.pos 160)] :=
  (lex_13_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.pos 65), (Sat.Literal.neg 160)] :=
  (lex_13_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.neg 65), (Sat.Literal.neg 160), (Sat.Literal.pos 5116)] :=
  (lex_13_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5115), (Sat.Literal.pos 65), (Sat.Literal.pos 160), (Sat.Literal.pos 5116)] :=
  (lex_13_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5116) = lexBefore s permutation13 64 := by
  exact (positive_lex_of_descriptor s 5116 permutation13 65 (by rfl)).trans ((lex_skipped s permutation13 64 65 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation13 64) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation13 64 by rw [image13_eq]; rfl))

theorem lex_13_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5117) (Sat.Literal.pos 5116) (Sat.Literal.pos 64) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation13 64 (assignment s)
    (Sat.Literal.pos 5117) (Sat.Literal.pos 5116) (Sat.Literal.pos 64) (Sat.Literal.pos 32) (positive_of_descriptor s 5117 (.lex permutation13 64) (by rfl)) (lex_13_64_prefix s) (positive_select s 64) (lex_13_64_image s)

theorem lex_13_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.pos 64), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation13 64 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5116) (Sat.Literal.pos 64) (Sat.Literal.pos 32) (lex_13_64_prefix s) (positive_select s 64) (lex_13_64_image s)

theorem lex_13_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.pos 5116)] :=
  (lex_13_64_gate s).prop _ (List.Mem.head _)

theorem lex_13_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.neg 64), (Sat.Literal.pos 32)] :=
  (lex_13_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.pos 64), (Sat.Literal.neg 32)] :=
  (lex_13_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.neg 64), (Sat.Literal.neg 32), (Sat.Literal.pos 5117)] :=
  (lex_13_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5116), (Sat.Literal.pos 64), (Sat.Literal.pos 32), (Sat.Literal.pos 5117)] :=
  (lex_13_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5117) = lexBefore s permutation13 63 := by
  exact (positive_lex_of_descriptor s 5117 permutation13 64 (by rfl)).trans ((lex_skipped s permutation13 63 64 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation13 63) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation13 63 by rw [image13_eq]; rfl))

theorem lex_13_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5118) (Sat.Literal.pos 5117) (Sat.Literal.pos 63) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation13 63 (assignment s)
    (Sat.Literal.pos 5118) (Sat.Literal.pos 5117) (Sat.Literal.pos 63) (Sat.Literal.pos 159) (positive_of_descriptor s 5118 (.lex permutation13 63) (by rfl)) (lex_13_63_prefix s) (positive_select s 63) (lex_13_63_image s)

theorem lex_13_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.pos 63), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation13 63 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5117) (Sat.Literal.pos 63) (Sat.Literal.pos 159) (lex_13_63_prefix s) (positive_select s 63) (lex_13_63_image s)

theorem lex_13_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.pos 5117)] :=
  (lex_13_63_gate s).prop _ (List.Mem.head _)

theorem lex_13_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.neg 63), (Sat.Literal.pos 159)] :=
  (lex_13_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.pos 63), (Sat.Literal.neg 159)] :=
  (lex_13_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.neg 63), (Sat.Literal.neg 159), (Sat.Literal.pos 5118)] :=
  (lex_13_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5117), (Sat.Literal.pos 63), (Sat.Literal.pos 159), (Sat.Literal.pos 5118)] :=
  (lex_13_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5118) = lexBefore s permutation13 62 := by
  exact (positive_lex_of_descriptor s 5118 permutation13 63 (by rfl)).trans ((lex_skipped s permutation13 62 63 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation13 62) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation13 62 by rw [image13_eq]; rfl))

theorem lex_13_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5119) (Sat.Literal.pos 5118) (Sat.Literal.pos 62) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation13 62 (assignment s)
    (Sat.Literal.pos 5119) (Sat.Literal.pos 5118) (Sat.Literal.pos 62) (Sat.Literal.pos 31) (positive_of_descriptor s 5119 (.lex permutation13 62) (by rfl)) (lex_13_62_prefix s) (positive_select s 62) (lex_13_62_image s)

theorem lex_13_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.pos 62), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation13 62 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5118) (Sat.Literal.pos 62) (Sat.Literal.pos 31) (lex_13_62_prefix s) (positive_select s 62) (lex_13_62_image s)

theorem lex_13_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.pos 5118)] :=
  (lex_13_62_gate s).prop _ (List.Mem.head _)

theorem lex_13_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.neg 62), (Sat.Literal.pos 31)] :=
  (lex_13_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.pos 62), (Sat.Literal.neg 31)] :=
  (lex_13_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.neg 62), (Sat.Literal.neg 31), (Sat.Literal.pos 5119)] :=
  (lex_13_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5118), (Sat.Literal.pos 62), (Sat.Literal.pos 31), (Sat.Literal.pos 5119)] :=
  (lex_13_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5119) = lexBefore s permutation13 61 := by
  exact (positive_lex_of_descriptor s 5119 permutation13 62 (by rfl)).trans ((lex_skipped s permutation13 61 62 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation13 61) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation13 61 by rw [image13_eq]; rfl))

theorem lex_13_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5120) (Sat.Literal.pos 5119) (Sat.Literal.pos 61) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation13 61 (assignment s)
    (Sat.Literal.pos 5120) (Sat.Literal.pos 5119) (Sat.Literal.pos 61) (Sat.Literal.pos 158) (positive_of_descriptor s 5120 (.lex permutation13 61) (by rfl)) (lex_13_61_prefix s) (positive_select s 61) (lex_13_61_image s)

theorem lex_13_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.pos 61), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation13 61 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5119) (Sat.Literal.pos 61) (Sat.Literal.pos 158) (lex_13_61_prefix s) (positive_select s 61) (lex_13_61_image s)

theorem lex_13_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.pos 5119)] :=
  (lex_13_61_gate s).prop _ (List.Mem.head _)

theorem lex_13_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.neg 61), (Sat.Literal.pos 158)] :=
  (lex_13_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.pos 61), (Sat.Literal.neg 158)] :=
  (lex_13_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.neg 61), (Sat.Literal.neg 158), (Sat.Literal.pos 5120)] :=
  (lex_13_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5119), (Sat.Literal.pos 61), (Sat.Literal.pos 158), (Sat.Literal.pos 5120)] :=
  (lex_13_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5120) = lexBefore s permutation13 60 := by
  exact (positive_lex_of_descriptor s 5120 permutation13 61 (by rfl)).trans ((lex_skipped s permutation13 60 61 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation13 60) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation13 60 by rw [image13_eq]; rfl))

theorem lex_13_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5121) (Sat.Literal.pos 5120) (Sat.Literal.pos 60) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation13 60 (assignment s)
    (Sat.Literal.pos 5121) (Sat.Literal.pos 5120) (Sat.Literal.pos 60) (Sat.Literal.pos 30) (positive_of_descriptor s 5121 (.lex permutation13 60) (by rfl)) (lex_13_60_prefix s) (positive_select s 60) (lex_13_60_image s)

theorem lex_13_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.pos 60), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation13 60 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5120) (Sat.Literal.pos 60) (Sat.Literal.pos 30) (lex_13_60_prefix s) (positive_select s 60) (lex_13_60_image s)

theorem lex_13_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.pos 5120)] :=
  (lex_13_60_gate s).prop _ (List.Mem.head _)

theorem lex_13_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.neg 60), (Sat.Literal.pos 30)] :=
  (lex_13_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.pos 60), (Sat.Literal.neg 30)] :=
  (lex_13_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.neg 60), (Sat.Literal.neg 30), (Sat.Literal.pos 5121)] :=
  (lex_13_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5120), (Sat.Literal.pos 60), (Sat.Literal.pos 30), (Sat.Literal.pos 5121)] :=
  (lex_13_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5121) = lexBefore s permutation13 59 := by
  exact (positive_lex_of_descriptor s 5121 permutation13 60 (by rfl)).trans ((lex_skipped s permutation13 59 60 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation13 59) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation13 59 by rw [image13_eq]; rfl))

theorem lex_13_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5122) (Sat.Literal.pos 5121) (Sat.Literal.pos 59) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation13 59 (assignment s)
    (Sat.Literal.pos 5122) (Sat.Literal.pos 5121) (Sat.Literal.pos 59) (Sat.Literal.pos 157) (positive_of_descriptor s 5122 (.lex permutation13 59) (by rfl)) (lex_13_59_prefix s) (positive_select s 59) (lex_13_59_image s)

theorem lex_13_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.pos 59), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation13 59 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5121) (Sat.Literal.pos 59) (Sat.Literal.pos 157) (lex_13_59_prefix s) (positive_select s 59) (lex_13_59_image s)

theorem lex_13_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.pos 5121)] :=
  (lex_13_59_gate s).prop _ (List.Mem.head _)

theorem lex_13_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.neg 59), (Sat.Literal.pos 157)] :=
  (lex_13_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.pos 59), (Sat.Literal.neg 157)] :=
  (lex_13_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.neg 59), (Sat.Literal.neg 157), (Sat.Literal.pos 5122)] :=
  (lex_13_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5121), (Sat.Literal.pos 59), (Sat.Literal.pos 157), (Sat.Literal.pos 5122)] :=
  (lex_13_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5122) = lexBefore s permutation13 58 := by
  exact (positive_lex_of_descriptor s 5122 permutation13 59 (by rfl)).trans ((lex_skipped s permutation13 58 59 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation13 58) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation13 58 by rw [image13_eq]; rfl))

theorem lex_13_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5123) (Sat.Literal.pos 5122) (Sat.Literal.pos 58) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation13 58 (assignment s)
    (Sat.Literal.pos 5123) (Sat.Literal.pos 5122) (Sat.Literal.pos 58) (Sat.Literal.pos 29) (positive_of_descriptor s 5123 (.lex permutation13 58) (by rfl)) (lex_13_58_prefix s) (positive_select s 58) (lex_13_58_image s)

theorem lex_13_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.pos 58), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation13 58 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5122) (Sat.Literal.pos 58) (Sat.Literal.pos 29) (lex_13_58_prefix s) (positive_select s 58) (lex_13_58_image s)

theorem lex_13_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.pos 5122)] :=
  (lex_13_58_gate s).prop _ (List.Mem.head _)

theorem lex_13_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.neg 58), (Sat.Literal.pos 29)] :=
  (lex_13_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.pos 58), (Sat.Literal.neg 29)] :=
  (lex_13_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.neg 58), (Sat.Literal.neg 29), (Sat.Literal.pos 5123)] :=
  (lex_13_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5122), (Sat.Literal.pos 58), (Sat.Literal.pos 29), (Sat.Literal.pos 5123)] :=
  (lex_13_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5123) = lexBefore s permutation13 57 := by
  exact (positive_lex_of_descriptor s 5123 permutation13 58 (by rfl)).trans ((lex_skipped s permutation13 57 58 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation13 57) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation13 57 by rw [image13_eq]; rfl))

theorem lex_13_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5124) (Sat.Literal.pos 5123) (Sat.Literal.pos 57) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation13 57 (assignment s)
    (Sat.Literal.pos 5124) (Sat.Literal.pos 5123) (Sat.Literal.pos 57) (Sat.Literal.pos 156) (positive_of_descriptor s 5124 (.lex permutation13 57) (by rfl)) (lex_13_57_prefix s) (positive_select s 57) (lex_13_57_image s)

theorem lex_13_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.pos 57), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation13 57 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5123) (Sat.Literal.pos 57) (Sat.Literal.pos 156) (lex_13_57_prefix s) (positive_select s 57) (lex_13_57_image s)

theorem lex_13_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.pos 5123)] :=
  (lex_13_57_gate s).prop _ (List.Mem.head _)

theorem lex_13_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.neg 57), (Sat.Literal.pos 156)] :=
  (lex_13_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.pos 57), (Sat.Literal.neg 156)] :=
  (lex_13_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.neg 57), (Sat.Literal.neg 156), (Sat.Literal.pos 5124)] :=
  (lex_13_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5123), (Sat.Literal.pos 57), (Sat.Literal.pos 156), (Sat.Literal.pos 5124)] :=
  (lex_13_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_13_156_gate

end Crown.CertificateData
