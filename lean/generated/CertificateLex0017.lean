import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_10_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4224) = lexBefore s permutation10 208 := by
  exact (positive_lex_of_descriptor s 4224 permutation10 209 (by rfl)).trans ((lex_skipped s permutation10 208 209 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation10 208) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation10 208 by rw [image10_eq]; rfl))

theorem lex_10_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4225) (Sat.Literal.pos 4224) (Sat.Literal.pos 208) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation10 208 (assignment s)
    (Sat.Literal.pos 4225) (Sat.Literal.pos 4224) (Sat.Literal.pos 208) (Sat.Literal.pos 13) (positive_of_descriptor s 4225 (.lex permutation10 208) (by rfl)) (lex_10_208_prefix s) (positive_select s 208) (lex_10_208_image s)

theorem lex_10_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.pos 208), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation10 208 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4224) (Sat.Literal.pos 208) (Sat.Literal.pos 13) (lex_10_208_prefix s) (positive_select s 208) (lex_10_208_image s)

theorem lex_10_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.pos 4224)] :=
  (lex_10_208_gate s).prop _ (List.Mem.head _)

theorem lex_10_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.neg 208), (Sat.Literal.pos 13)] :=
  (lex_10_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.pos 208), (Sat.Literal.neg 13)] :=
  (lex_10_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.neg 208), (Sat.Literal.neg 13), (Sat.Literal.pos 4225)] :=
  (lex_10_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.pos 208), (Sat.Literal.pos 13), (Sat.Literal.pos 4225)] :=
  (lex_10_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4225) = lexBefore s permutation10 207 := by
  exact (positive_lex_of_descriptor s 4225 permutation10 208 (by rfl)).trans ((lex_skipped s permutation10 207 208 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation10 207) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation10 207 by rw [image10_eq]; rfl))

theorem lex_10_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4226) (Sat.Literal.pos 4225) (Sat.Literal.pos 207) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation10 207 (assignment s)
    (Sat.Literal.pos 4226) (Sat.Literal.pos 4225) (Sat.Literal.pos 207) (Sat.Literal.pos 252) (positive_of_descriptor s 4226 (.lex permutation10 207) (by rfl)) (lex_10_207_prefix s) (positive_select s 207) (lex_10_207_image s)

theorem lex_10_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.pos 207), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation10 207 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4225) (Sat.Literal.pos 207) (Sat.Literal.pos 252) (lex_10_207_prefix s) (positive_select s 207) (lex_10_207_image s)

theorem lex_10_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.pos 4225)] :=
  (lex_10_207_gate s).prop _ (List.Mem.head _)

theorem lex_10_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.neg 207), (Sat.Literal.pos 252)] :=
  (lex_10_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.pos 207), (Sat.Literal.neg 252)] :=
  (lex_10_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.neg 207), (Sat.Literal.neg 252), (Sat.Literal.pos 4226)] :=
  (lex_10_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4225), (Sat.Literal.pos 207), (Sat.Literal.pos 252), (Sat.Literal.pos 4226)] :=
  (lex_10_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4226) = lexBefore s permutation10 206 := by
  exact (positive_lex_of_descriptor s 4226 permutation10 207 (by rfl)).trans ((lex_skipped s permutation10 206 207 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation10 206) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation10 206 by rw [image10_eq]; rfl))

theorem lex_10_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4227) (Sat.Literal.pos 4226) (Sat.Literal.pos 206) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation10 206 (assignment s)
    (Sat.Literal.pos 4227) (Sat.Literal.pos 4226) (Sat.Literal.pos 206) (Sat.Literal.pos 236) (positive_of_descriptor s 4227 (.lex permutation10 206) (by rfl)) (lex_10_206_prefix s) (positive_select s 206) (lex_10_206_image s)

theorem lex_10_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.pos 206), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation10 206 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4226) (Sat.Literal.pos 206) (Sat.Literal.pos 236) (lex_10_206_prefix s) (positive_select s 206) (lex_10_206_image s)

theorem lex_10_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.pos 4226)] :=
  (lex_10_206_gate s).prop _ (List.Mem.head _)

theorem lex_10_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.neg 206), (Sat.Literal.pos 236)] :=
  (lex_10_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.pos 206), (Sat.Literal.neg 236)] :=
  (lex_10_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.neg 206), (Sat.Literal.neg 236), (Sat.Literal.pos 4227)] :=
  (lex_10_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4226), (Sat.Literal.pos 206), (Sat.Literal.pos 236), (Sat.Literal.pos 4227)] :=
  (lex_10_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4227) = lexBefore s permutation10 205 := by
  exact (positive_lex_of_descriptor s 4227 permutation10 206 (by rfl)).trans ((lex_skipped s permutation10 205 206 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation10 205) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation10 205 by rw [image10_eq]; rfl))

theorem lex_10_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4228) (Sat.Literal.pos 4227) (Sat.Literal.pos 205) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation10 205 (assignment s)
    (Sat.Literal.pos 4228) (Sat.Literal.pos 4227) (Sat.Literal.pos 205) (Sat.Literal.pos 220) (positive_of_descriptor s 4228 (.lex permutation10 205) (by rfl)) (lex_10_205_prefix s) (positive_select s 205) (lex_10_205_image s)

theorem lex_10_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.pos 205), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation10 205 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4227) (Sat.Literal.pos 205) (Sat.Literal.pos 220) (lex_10_205_prefix s) (positive_select s 205) (lex_10_205_image s)

theorem lex_10_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.pos 4227)] :=
  (lex_10_205_gate s).prop _ (List.Mem.head _)

theorem lex_10_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.neg 205), (Sat.Literal.pos 220)] :=
  (lex_10_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.pos 205), (Sat.Literal.neg 220)] :=
  (lex_10_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.neg 205), (Sat.Literal.neg 220), (Sat.Literal.pos 4228)] :=
  (lex_10_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4227), (Sat.Literal.pos 205), (Sat.Literal.pos 220), (Sat.Literal.pos 4228)] :=
  (lex_10_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4228) = lexBefore s permutation10 203 := by
  exact (positive_lex_of_descriptor s 4228 permutation10 205 (by rfl)).trans ((lex_skipped s permutation10 203 205 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 204 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation10 203) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation10 203 by rw [image10_eq]; rfl))

theorem lex_10_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4229) (Sat.Literal.pos 4228) (Sat.Literal.pos 203) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation10 203 (assignment s)
    (Sat.Literal.pos 4229) (Sat.Literal.pos 4228) (Sat.Literal.pos 203) (Sat.Literal.pos 188) (positive_of_descriptor s 4229 (.lex permutation10 203) (by rfl)) (lex_10_203_prefix s) (positive_select s 203) (lex_10_203_image s)

theorem lex_10_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.pos 203), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation10 203 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4228) (Sat.Literal.pos 203) (Sat.Literal.pos 188) (lex_10_203_prefix s) (positive_select s 203) (lex_10_203_image s)

theorem lex_10_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.pos 4228)] :=
  (lex_10_203_gate s).prop _ (List.Mem.head _)

theorem lex_10_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.neg 203), (Sat.Literal.pos 188)] :=
  (lex_10_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.pos 203), (Sat.Literal.neg 188)] :=
  (lex_10_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.neg 203), (Sat.Literal.neg 188), (Sat.Literal.pos 4229)] :=
  (lex_10_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4228), (Sat.Literal.pos 203), (Sat.Literal.pos 188), (Sat.Literal.pos 4229)] :=
  (lex_10_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4229) = lexBefore s permutation10 202 := by
  exact (positive_lex_of_descriptor s 4229 permutation10 203 (by rfl)).trans ((lex_skipped s permutation10 202 203 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation10 202) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation10 202 by rw [image10_eq]; rfl))

theorem lex_10_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4230) (Sat.Literal.pos 4229) (Sat.Literal.pos 202) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation10 202 (assignment s)
    (Sat.Literal.pos 4230) (Sat.Literal.pos 4229) (Sat.Literal.pos 202) (Sat.Literal.pos 172) (positive_of_descriptor s 4230 (.lex permutation10 202) (by rfl)) (lex_10_202_prefix s) (positive_select s 202) (lex_10_202_image s)

theorem lex_10_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.pos 202), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation10 202 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4229) (Sat.Literal.pos 202) (Sat.Literal.pos 172) (lex_10_202_prefix s) (positive_select s 202) (lex_10_202_image s)

theorem lex_10_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.pos 4229)] :=
  (lex_10_202_gate s).prop _ (List.Mem.head _)

theorem lex_10_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.neg 202), (Sat.Literal.pos 172)] :=
  (lex_10_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.pos 202), (Sat.Literal.neg 172)] :=
  (lex_10_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.neg 202), (Sat.Literal.neg 172), (Sat.Literal.pos 4230)] :=
  (lex_10_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4229), (Sat.Literal.pos 202), (Sat.Literal.pos 172), (Sat.Literal.pos 4230)] :=
  (lex_10_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4230) = lexBefore s permutation10 201 := by
  exact (positive_lex_of_descriptor s 4230 permutation10 202 (by rfl)).trans ((lex_skipped s permutation10 201 202 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation10 201) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation10 201 by rw [image10_eq]; rfl))

theorem lex_10_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4231) (Sat.Literal.pos 4230) (Sat.Literal.pos 201) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation10 201 (assignment s)
    (Sat.Literal.pos 4231) (Sat.Literal.pos 4230) (Sat.Literal.pos 201) (Sat.Literal.pos 156) (positive_of_descriptor s 4231 (.lex permutation10 201) (by rfl)) (lex_10_201_prefix s) (positive_select s 201) (lex_10_201_image s)

theorem lex_10_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.pos 201), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation10 201 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4230) (Sat.Literal.pos 201) (Sat.Literal.pos 156) (lex_10_201_prefix s) (positive_select s 201) (lex_10_201_image s)

theorem lex_10_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.pos 4230)] :=
  (lex_10_201_gate s).prop _ (List.Mem.head _)

theorem lex_10_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.neg 201), (Sat.Literal.pos 156)] :=
  (lex_10_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.pos 201), (Sat.Literal.neg 156)] :=
  (lex_10_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.neg 201), (Sat.Literal.neg 156), (Sat.Literal.pos 4231)] :=
  (lex_10_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4230), (Sat.Literal.pos 201), (Sat.Literal.pos 156), (Sat.Literal.pos 4231)] :=
  (lex_10_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4231) = lexBefore s permutation10 200 := by
  exact (positive_lex_of_descriptor s 4231 permutation10 201 (by rfl)).trans ((lex_skipped s permutation10 200 201 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation10 200) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation10 200 by rw [image10_eq]; rfl))

theorem lex_10_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4232) (Sat.Literal.pos 4231) (Sat.Literal.pos 200) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation10 200 (assignment s)
    (Sat.Literal.pos 4232) (Sat.Literal.pos 4231) (Sat.Literal.pos 200) (Sat.Literal.pos 140) (positive_of_descriptor s 4232 (.lex permutation10 200) (by rfl)) (lex_10_200_prefix s) (positive_select s 200) (lex_10_200_image s)

theorem lex_10_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.pos 200), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation10 200 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4231) (Sat.Literal.pos 200) (Sat.Literal.pos 140) (lex_10_200_prefix s) (positive_select s 200) (lex_10_200_image s)

theorem lex_10_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.pos 4231)] :=
  (lex_10_200_gate s).prop _ (List.Mem.head _)

theorem lex_10_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.neg 200), (Sat.Literal.pos 140)] :=
  (lex_10_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.pos 200), (Sat.Literal.neg 140)] :=
  (lex_10_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.neg 200), (Sat.Literal.neg 140), (Sat.Literal.pos 4232)] :=
  (lex_10_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4231), (Sat.Literal.pos 200), (Sat.Literal.pos 140), (Sat.Literal.pos 4232)] :=
  (lex_10_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4232) = lexBefore s permutation10 199 := by
  exact (positive_lex_of_descriptor s 4232 permutation10 200 (by rfl)).trans ((lex_skipped s permutation10 199 200 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation10 199) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation10 199 by rw [image10_eq]; rfl))

theorem lex_10_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4233) (Sat.Literal.pos 4232) (Sat.Literal.pos 199) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation10 199 (assignment s)
    (Sat.Literal.pos 4233) (Sat.Literal.pos 4232) (Sat.Literal.pos 199) (Sat.Literal.pos 124) (positive_of_descriptor s 4233 (.lex permutation10 199) (by rfl)) (lex_10_199_prefix s) (positive_select s 199) (lex_10_199_image s)

theorem lex_10_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.pos 199), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation10 199 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4232) (Sat.Literal.pos 199) (Sat.Literal.pos 124) (lex_10_199_prefix s) (positive_select s 199) (lex_10_199_image s)

theorem lex_10_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.pos 4232)] :=
  (lex_10_199_gate s).prop _ (List.Mem.head _)

theorem lex_10_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.neg 199), (Sat.Literal.pos 124)] :=
  (lex_10_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.pos 199), (Sat.Literal.neg 124)] :=
  (lex_10_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.neg 199), (Sat.Literal.neg 124), (Sat.Literal.pos 4233)] :=
  (lex_10_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4232), (Sat.Literal.pos 199), (Sat.Literal.pos 124), (Sat.Literal.pos 4233)] :=
  (lex_10_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4233) = lexBefore s permutation10 198 := by
  exact (positive_lex_of_descriptor s 4233 permutation10 199 (by rfl)).trans ((lex_skipped s permutation10 198 199 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation10 198) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation10 198 by rw [image10_eq]; rfl))

theorem lex_10_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4234) (Sat.Literal.pos 4233) (Sat.Literal.pos 198) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation10 198 (assignment s)
    (Sat.Literal.pos 4234) (Sat.Literal.pos 4233) (Sat.Literal.pos 198) (Sat.Literal.pos 108) (positive_of_descriptor s 4234 (.lex permutation10 198) (by rfl)) (lex_10_198_prefix s) (positive_select s 198) (lex_10_198_image s)

theorem lex_10_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.pos 198), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation10 198 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4233) (Sat.Literal.pos 198) (Sat.Literal.pos 108) (lex_10_198_prefix s) (positive_select s 198) (lex_10_198_image s)

theorem lex_10_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.pos 4233)] :=
  (lex_10_198_gate s).prop _ (List.Mem.head _)

theorem lex_10_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.neg 198), (Sat.Literal.pos 108)] :=
  (lex_10_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.pos 198), (Sat.Literal.neg 108)] :=
  (lex_10_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.neg 198), (Sat.Literal.neg 108), (Sat.Literal.pos 4234)] :=
  (lex_10_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4233), (Sat.Literal.pos 198), (Sat.Literal.pos 108), (Sat.Literal.pos 4234)] :=
  (lex_10_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4234) = lexBefore s permutation10 197 := by
  exact (positive_lex_of_descriptor s 4234 permutation10 198 (by rfl)).trans ((lex_skipped s permutation10 197 198 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation10 197) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation10 197 by rw [image10_eq]; rfl))

theorem lex_10_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4235) (Sat.Literal.pos 4234) (Sat.Literal.pos 197) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation10 197 (assignment s)
    (Sat.Literal.pos 4235) (Sat.Literal.pos 4234) (Sat.Literal.pos 197) (Sat.Literal.pos 92) (positive_of_descriptor s 4235 (.lex permutation10 197) (by rfl)) (lex_10_197_prefix s) (positive_select s 197) (lex_10_197_image s)

theorem lex_10_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.pos 197), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation10 197 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4234) (Sat.Literal.pos 197) (Sat.Literal.pos 92) (lex_10_197_prefix s) (positive_select s 197) (lex_10_197_image s)

theorem lex_10_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.pos 4234)] :=
  (lex_10_197_gate s).prop _ (List.Mem.head _)

theorem lex_10_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.neg 197), (Sat.Literal.pos 92)] :=
  (lex_10_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.pos 197), (Sat.Literal.neg 92)] :=
  (lex_10_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.neg 197), (Sat.Literal.neg 92), (Sat.Literal.pos 4235)] :=
  (lex_10_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4234), (Sat.Literal.pos 197), (Sat.Literal.pos 92), (Sat.Literal.pos 4235)] :=
  (lex_10_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4235) = lexBefore s permutation10 196 := by
  exact (positive_lex_of_descriptor s 4235 permutation10 197 (by rfl)).trans ((lex_skipped s permutation10 196 197 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation10 196) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation10 196 by rw [image10_eq]; rfl))

theorem lex_10_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4236) (Sat.Literal.pos 4235) (Sat.Literal.pos 196) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation10 196 (assignment s)
    (Sat.Literal.pos 4236) (Sat.Literal.pos 4235) (Sat.Literal.pos 196) (Sat.Literal.pos 76) (positive_of_descriptor s 4236 (.lex permutation10 196) (by rfl)) (lex_10_196_prefix s) (positive_select s 196) (lex_10_196_image s)

theorem lex_10_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.pos 196), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation10 196 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4235) (Sat.Literal.pos 196) (Sat.Literal.pos 76) (lex_10_196_prefix s) (positive_select s 196) (lex_10_196_image s)

theorem lex_10_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.pos 4235)] :=
  (lex_10_196_gate s).prop _ (List.Mem.head _)

theorem lex_10_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.neg 196), (Sat.Literal.pos 76)] :=
  (lex_10_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.pos 196), (Sat.Literal.neg 76)] :=
  (lex_10_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.neg 196), (Sat.Literal.neg 76), (Sat.Literal.pos 4236)] :=
  (lex_10_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4235), (Sat.Literal.pos 196), (Sat.Literal.pos 76), (Sat.Literal.pos 4236)] :=
  (lex_10_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4236) = lexBefore s permutation10 195 := by
  exact (positive_lex_of_descriptor s 4236 permutation10 196 (by rfl)).trans ((lex_skipped s permutation10 195 196 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation10 195) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation10 195 by rw [image10_eq]; rfl))

theorem lex_10_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4237) (Sat.Literal.pos 4236) (Sat.Literal.pos 195) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation10 195 (assignment s)
    (Sat.Literal.pos 4237) (Sat.Literal.pos 4236) (Sat.Literal.pos 195) (Sat.Literal.pos 60) (positive_of_descriptor s 4237 (.lex permutation10 195) (by rfl)) (lex_10_195_prefix s) (positive_select s 195) (lex_10_195_image s)

theorem lex_10_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.pos 195), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation10 195 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4236) (Sat.Literal.pos 195) (Sat.Literal.pos 60) (lex_10_195_prefix s) (positive_select s 195) (lex_10_195_image s)

theorem lex_10_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.pos 4236)] :=
  (lex_10_195_gate s).prop _ (List.Mem.head _)

theorem lex_10_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.neg 195), (Sat.Literal.pos 60)] :=
  (lex_10_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.pos 195), (Sat.Literal.neg 60)] :=
  (lex_10_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.neg 195), (Sat.Literal.neg 60), (Sat.Literal.pos 4237)] :=
  (lex_10_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4236), (Sat.Literal.pos 195), (Sat.Literal.pos 60), (Sat.Literal.pos 4237)] :=
  (lex_10_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4237) = lexBefore s permutation10 194 := by
  exact (positive_lex_of_descriptor s 4237 permutation10 195 (by rfl)).trans ((lex_skipped s permutation10 194 195 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation10 194) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation10 194 by rw [image10_eq]; rfl))

theorem lex_10_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4238) (Sat.Literal.pos 4237) (Sat.Literal.pos 194) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation10 194 (assignment s)
    (Sat.Literal.pos 4238) (Sat.Literal.pos 4237) (Sat.Literal.pos 194) (Sat.Literal.pos 44) (positive_of_descriptor s 4238 (.lex permutation10 194) (by rfl)) (lex_10_194_prefix s) (positive_select s 194) (lex_10_194_image s)

theorem lex_10_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.pos 194), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation10 194 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4237) (Sat.Literal.pos 194) (Sat.Literal.pos 44) (lex_10_194_prefix s) (positive_select s 194) (lex_10_194_image s)

theorem lex_10_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.pos 4237)] :=
  (lex_10_194_gate s).prop _ (List.Mem.head _)

theorem lex_10_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.neg 194), (Sat.Literal.pos 44)] :=
  (lex_10_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.pos 194), (Sat.Literal.neg 44)] :=
  (lex_10_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.neg 194), (Sat.Literal.neg 44), (Sat.Literal.pos 4238)] :=
  (lex_10_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4237), (Sat.Literal.pos 194), (Sat.Literal.pos 44), (Sat.Literal.pos 4238)] :=
  (lex_10_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4238) = lexBefore s permutation10 193 := by
  exact (positive_lex_of_descriptor s 4238 permutation10 194 (by rfl)).trans ((lex_skipped s permutation10 193 194 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation10 193) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation10 193 by rw [image10_eq]; rfl))

theorem lex_10_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4239) (Sat.Literal.pos 4238) (Sat.Literal.pos 193) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation10 193 (assignment s)
    (Sat.Literal.pos 4239) (Sat.Literal.pos 4238) (Sat.Literal.pos 193) (Sat.Literal.pos 28) (positive_of_descriptor s 4239 (.lex permutation10 193) (by rfl)) (lex_10_193_prefix s) (positive_select s 193) (lex_10_193_image s)

theorem lex_10_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.pos 193), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation10 193 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4238) (Sat.Literal.pos 193) (Sat.Literal.pos 28) (lex_10_193_prefix s) (positive_select s 193) (lex_10_193_image s)

theorem lex_10_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.pos 4238)] :=
  (lex_10_193_gate s).prop _ (List.Mem.head _)

theorem lex_10_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.neg 193), (Sat.Literal.pos 28)] :=
  (lex_10_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.pos 193), (Sat.Literal.neg 28)] :=
  (lex_10_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.neg 193), (Sat.Literal.neg 28), (Sat.Literal.pos 4239)] :=
  (lex_10_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4238), (Sat.Literal.pos 193), (Sat.Literal.pos 28), (Sat.Literal.pos 4239)] :=
  (lex_10_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4239) = lexBefore s permutation10 192 := by
  exact (positive_lex_of_descriptor s 4239 permutation10 193 (by rfl)).trans ((lex_skipped s permutation10 192 193 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation10 192) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation10 192 by rw [image10_eq]; rfl))

theorem lex_10_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4240) (Sat.Literal.pos 4239) (Sat.Literal.pos 192) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation10 192 (assignment s)
    (Sat.Literal.pos 4240) (Sat.Literal.pos 4239) (Sat.Literal.pos 192) (Sat.Literal.pos 12) (positive_of_descriptor s 4240 (.lex permutation10 192) (by rfl)) (lex_10_192_prefix s) (positive_select s 192) (lex_10_192_image s)

theorem lex_10_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.pos 192), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation10 192 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4239) (Sat.Literal.pos 192) (Sat.Literal.pos 12) (lex_10_192_prefix s) (positive_select s 192) (lex_10_192_image s)

theorem lex_10_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.pos 4239)] :=
  (lex_10_192_gate s).prop _ (List.Mem.head _)

theorem lex_10_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.neg 192), (Sat.Literal.pos 12)] :=
  (lex_10_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.pos 192), (Sat.Literal.neg 12)] :=
  (lex_10_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.neg 192), (Sat.Literal.neg 12), (Sat.Literal.pos 4240)] :=
  (lex_10_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4239), (Sat.Literal.pos 192), (Sat.Literal.pos 12), (Sat.Literal.pos 4240)] :=
  (lex_10_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4240) = lexBefore s permutation10 191 := by
  exact (positive_lex_of_descriptor s 4240 permutation10 192 (by rfl)).trans ((lex_skipped s permutation10 191 192 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation10 191) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation10 191 by rw [image10_eq]; rfl))

theorem lex_10_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4241) (Sat.Literal.pos 4240) (Sat.Literal.pos 191) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation10 191 (assignment s)
    (Sat.Literal.pos 4241) (Sat.Literal.pos 4240) (Sat.Literal.pos 191) (Sat.Literal.pos 251) (positive_of_descriptor s 4241 (.lex permutation10 191) (by rfl)) (lex_10_191_prefix s) (positive_select s 191) (lex_10_191_image s)

theorem lex_10_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.pos 191), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation10 191 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4240) (Sat.Literal.pos 191) (Sat.Literal.pos 251) (lex_10_191_prefix s) (positive_select s 191) (lex_10_191_image s)

theorem lex_10_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.pos 4240)] :=
  (lex_10_191_gate s).prop _ (List.Mem.head _)

theorem lex_10_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.neg 191), (Sat.Literal.pos 251)] :=
  (lex_10_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.pos 191), (Sat.Literal.neg 251)] :=
  (lex_10_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.neg 191), (Sat.Literal.neg 251), (Sat.Literal.pos 4241)] :=
  (lex_10_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4240), (Sat.Literal.pos 191), (Sat.Literal.pos 251), (Sat.Literal.pos 4241)] :=
  (lex_10_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4241) = lexBefore s permutation10 190 := by
  exact (positive_lex_of_descriptor s 4241 permutation10 191 (by rfl)).trans ((lex_skipped s permutation10 190 191 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation10 190) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation10 190 by rw [image10_eq]; rfl))

theorem lex_10_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4242) (Sat.Literal.pos 4241) (Sat.Literal.pos 190) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation10 190 (assignment s)
    (Sat.Literal.pos 4242) (Sat.Literal.pos 4241) (Sat.Literal.pos 190) (Sat.Literal.pos 235) (positive_of_descriptor s 4242 (.lex permutation10 190) (by rfl)) (lex_10_190_prefix s) (positive_select s 190) (lex_10_190_image s)

theorem lex_10_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.pos 190), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation10 190 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4241) (Sat.Literal.pos 190) (Sat.Literal.pos 235) (lex_10_190_prefix s) (positive_select s 190) (lex_10_190_image s)

theorem lex_10_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.pos 4241)] :=
  (lex_10_190_gate s).prop _ (List.Mem.head _)

theorem lex_10_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.neg 190), (Sat.Literal.pos 235)] :=
  (lex_10_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.pos 190), (Sat.Literal.neg 235)] :=
  (lex_10_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.neg 190), (Sat.Literal.neg 235), (Sat.Literal.pos 4242)] :=
  (lex_10_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4241), (Sat.Literal.pos 190), (Sat.Literal.pos 235), (Sat.Literal.pos 4242)] :=
  (lex_10_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4242) = lexBefore s permutation10 189 := by
  exact (positive_lex_of_descriptor s 4242 permutation10 190 (by rfl)).trans ((lex_skipped s permutation10 189 190 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation10 189) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation10 189 by rw [image10_eq]; rfl))

theorem lex_10_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4243) (Sat.Literal.pos 4242) (Sat.Literal.pos 189) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation10 189 (assignment s)
    (Sat.Literal.pos 4243) (Sat.Literal.pos 4242) (Sat.Literal.pos 189) (Sat.Literal.pos 219) (positive_of_descriptor s 4243 (.lex permutation10 189) (by rfl)) (lex_10_189_prefix s) (positive_select s 189) (lex_10_189_image s)

theorem lex_10_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.pos 189), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation10 189 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4242) (Sat.Literal.pos 189) (Sat.Literal.pos 219) (lex_10_189_prefix s) (positive_select s 189) (lex_10_189_image s)

theorem lex_10_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.pos 4242)] :=
  (lex_10_189_gate s).prop _ (List.Mem.head _)

theorem lex_10_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.neg 189), (Sat.Literal.pos 219)] :=
  (lex_10_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.pos 189), (Sat.Literal.neg 219)] :=
  (lex_10_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.neg 189), (Sat.Literal.neg 219), (Sat.Literal.pos 4243)] :=
  (lex_10_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4242), (Sat.Literal.pos 189), (Sat.Literal.pos 219), (Sat.Literal.pos 4243)] :=
  (lex_10_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4243) = lexBefore s permutation10 188 := by
  exact (positive_lex_of_descriptor s 4243 permutation10 189 (by rfl)).trans ((lex_skipped s permutation10 188 189 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation10 188) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation10 188 by rw [image10_eq]; rfl))

theorem lex_10_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4244) (Sat.Literal.pos 4243) (Sat.Literal.pos 188) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation10 188 (assignment s)
    (Sat.Literal.pos 4244) (Sat.Literal.pos 4243) (Sat.Literal.pos 188) (Sat.Literal.pos 203) (positive_of_descriptor s 4244 (.lex permutation10 188) (by rfl)) (lex_10_188_prefix s) (positive_select s 188) (lex_10_188_image s)

theorem lex_10_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.pos 188), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation10 188 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4243) (Sat.Literal.pos 188) (Sat.Literal.pos 203) (lex_10_188_prefix s) (positive_select s 188) (lex_10_188_image s)

theorem lex_10_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.pos 4243)] :=
  (lex_10_188_gate s).prop _ (List.Mem.head _)

theorem lex_10_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.neg 188), (Sat.Literal.pos 203)] :=
  (lex_10_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.pos 188), (Sat.Literal.neg 203)] :=
  (lex_10_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.neg 188), (Sat.Literal.neg 203), (Sat.Literal.pos 4244)] :=
  (lex_10_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4243), (Sat.Literal.pos 188), (Sat.Literal.pos 203), (Sat.Literal.pos 4244)] :=
  (lex_10_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4244) = lexBefore s permutation10 186 := by
  exact (positive_lex_of_descriptor s 4244 permutation10 188 (by rfl)).trans ((lex_skipped s permutation10 186 188 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 187 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation10 186) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation10 186 by rw [image10_eq]; rfl))

theorem lex_10_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4245) (Sat.Literal.pos 4244) (Sat.Literal.pos 186) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation10 186 (assignment s)
    (Sat.Literal.pos 4245) (Sat.Literal.pos 4244) (Sat.Literal.pos 186) (Sat.Literal.pos 171) (positive_of_descriptor s 4245 (.lex permutation10 186) (by rfl)) (lex_10_186_prefix s) (positive_select s 186) (lex_10_186_image s)

theorem lex_10_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.pos 186), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation10 186 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4244) (Sat.Literal.pos 186) (Sat.Literal.pos 171) (lex_10_186_prefix s) (positive_select s 186) (lex_10_186_image s)

theorem lex_10_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.pos 4244)] :=
  (lex_10_186_gate s).prop _ (List.Mem.head _)

theorem lex_10_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.neg 186), (Sat.Literal.pos 171)] :=
  (lex_10_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.pos 186), (Sat.Literal.neg 171)] :=
  (lex_10_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.neg 186), (Sat.Literal.neg 171), (Sat.Literal.pos 4245)] :=
  (lex_10_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4244), (Sat.Literal.pos 186), (Sat.Literal.pos 171), (Sat.Literal.pos 4245)] :=
  (lex_10_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4245) = lexBefore s permutation10 185 := by
  exact (positive_lex_of_descriptor s 4245 permutation10 186 (by rfl)).trans ((lex_skipped s permutation10 185 186 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation10 185) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation10 185 by rw [image10_eq]; rfl))

theorem lex_10_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4246) (Sat.Literal.pos 4245) (Sat.Literal.pos 185) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation10 185 (assignment s)
    (Sat.Literal.pos 4246) (Sat.Literal.pos 4245) (Sat.Literal.pos 185) (Sat.Literal.pos 155) (positive_of_descriptor s 4246 (.lex permutation10 185) (by rfl)) (lex_10_185_prefix s) (positive_select s 185) (lex_10_185_image s)

theorem lex_10_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.pos 185), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation10 185 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4245) (Sat.Literal.pos 185) (Sat.Literal.pos 155) (lex_10_185_prefix s) (positive_select s 185) (lex_10_185_image s)

theorem lex_10_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.pos 4245)] :=
  (lex_10_185_gate s).prop _ (List.Mem.head _)

theorem lex_10_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.neg 185), (Sat.Literal.pos 155)] :=
  (lex_10_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.pos 185), (Sat.Literal.neg 155)] :=
  (lex_10_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.neg 185), (Sat.Literal.neg 155), (Sat.Literal.pos 4246)] :=
  (lex_10_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4245), (Sat.Literal.pos 185), (Sat.Literal.pos 155), (Sat.Literal.pos 4246)] :=
  (lex_10_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4246) = lexBefore s permutation10 184 := by
  exact (positive_lex_of_descriptor s 4246 permutation10 185 (by rfl)).trans ((lex_skipped s permutation10 184 185 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation10 184) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation10 184 by rw [image10_eq]; rfl))

theorem lex_10_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4247) (Sat.Literal.pos 4246) (Sat.Literal.pos 184) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation10 184 (assignment s)
    (Sat.Literal.pos 4247) (Sat.Literal.pos 4246) (Sat.Literal.pos 184) (Sat.Literal.pos 139) (positive_of_descriptor s 4247 (.lex permutation10 184) (by rfl)) (lex_10_184_prefix s) (positive_select s 184) (lex_10_184_image s)

theorem lex_10_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.pos 184), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation10 184 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4246) (Sat.Literal.pos 184) (Sat.Literal.pos 139) (lex_10_184_prefix s) (positive_select s 184) (lex_10_184_image s)

theorem lex_10_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.pos 4246)] :=
  (lex_10_184_gate s).prop _ (List.Mem.head _)

theorem lex_10_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.neg 184), (Sat.Literal.pos 139)] :=
  (lex_10_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.pos 184), (Sat.Literal.neg 139)] :=
  (lex_10_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.neg 184), (Sat.Literal.neg 139), (Sat.Literal.pos 4247)] :=
  (lex_10_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4246), (Sat.Literal.pos 184), (Sat.Literal.pos 139), (Sat.Literal.pos 4247)] :=
  (lex_10_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4247) = lexBefore s permutation10 183 := by
  exact (positive_lex_of_descriptor s 4247 permutation10 184 (by rfl)).trans ((lex_skipped s permutation10 183 184 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation10 183) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation10 183 by rw [image10_eq]; rfl))

theorem lex_10_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4248) (Sat.Literal.pos 4247) (Sat.Literal.pos 183) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation10 183 (assignment s)
    (Sat.Literal.pos 4248) (Sat.Literal.pos 4247) (Sat.Literal.pos 183) (Sat.Literal.pos 123) (positive_of_descriptor s 4248 (.lex permutation10 183) (by rfl)) (lex_10_183_prefix s) (positive_select s 183) (lex_10_183_image s)

theorem lex_10_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.pos 183), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation10 183 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4247) (Sat.Literal.pos 183) (Sat.Literal.pos 123) (lex_10_183_prefix s) (positive_select s 183) (lex_10_183_image s)

theorem lex_10_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.pos 4247)] :=
  (lex_10_183_gate s).prop _ (List.Mem.head _)

theorem lex_10_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.neg 183), (Sat.Literal.pos 123)] :=
  (lex_10_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.pos 183), (Sat.Literal.neg 123)] :=
  (lex_10_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.neg 183), (Sat.Literal.neg 123), (Sat.Literal.pos 4248)] :=
  (lex_10_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4247), (Sat.Literal.pos 183), (Sat.Literal.pos 123), (Sat.Literal.pos 4248)] :=
  (lex_10_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4248) = lexBefore s permutation10 182 := by
  exact (positive_lex_of_descriptor s 4248 permutation10 183 (by rfl)).trans ((lex_skipped s permutation10 182 183 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation10 182) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation10 182 by rw [image10_eq]; rfl))

theorem lex_10_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4249) (Sat.Literal.pos 4248) (Sat.Literal.pos 182) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation10 182 (assignment s)
    (Sat.Literal.pos 4249) (Sat.Literal.pos 4248) (Sat.Literal.pos 182) (Sat.Literal.pos 107) (positive_of_descriptor s 4249 (.lex permutation10 182) (by rfl)) (lex_10_182_prefix s) (positive_select s 182) (lex_10_182_image s)

theorem lex_10_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.pos 182), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation10 182 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4248) (Sat.Literal.pos 182) (Sat.Literal.pos 107) (lex_10_182_prefix s) (positive_select s 182) (lex_10_182_image s)

theorem lex_10_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.pos 4248)] :=
  (lex_10_182_gate s).prop _ (List.Mem.head _)

theorem lex_10_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.neg 182), (Sat.Literal.pos 107)] :=
  (lex_10_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.pos 182), (Sat.Literal.neg 107)] :=
  (lex_10_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.neg 182), (Sat.Literal.neg 107), (Sat.Literal.pos 4249)] :=
  (lex_10_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4248), (Sat.Literal.pos 182), (Sat.Literal.pos 107), (Sat.Literal.pos 4249)] :=
  (lex_10_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4249) = lexBefore s permutation10 181 := by
  exact (positive_lex_of_descriptor s 4249 permutation10 182 (by rfl)).trans ((lex_skipped s permutation10 181 182 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation10 181) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation10 181 by rw [image10_eq]; rfl))

theorem lex_10_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4250) (Sat.Literal.pos 4249) (Sat.Literal.pos 181) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation10 181 (assignment s)
    (Sat.Literal.pos 4250) (Sat.Literal.pos 4249) (Sat.Literal.pos 181) (Sat.Literal.pos 91) (positive_of_descriptor s 4250 (.lex permutation10 181) (by rfl)) (lex_10_181_prefix s) (positive_select s 181) (lex_10_181_image s)

theorem lex_10_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.pos 181), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation10 181 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4249) (Sat.Literal.pos 181) (Sat.Literal.pos 91) (lex_10_181_prefix s) (positive_select s 181) (lex_10_181_image s)

theorem lex_10_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.pos 4249)] :=
  (lex_10_181_gate s).prop _ (List.Mem.head _)

theorem lex_10_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.neg 181), (Sat.Literal.pos 91)] :=
  (lex_10_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.pos 181), (Sat.Literal.neg 91)] :=
  (lex_10_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.neg 181), (Sat.Literal.neg 91), (Sat.Literal.pos 4250)] :=
  (lex_10_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4249), (Sat.Literal.pos 181), (Sat.Literal.pos 91), (Sat.Literal.pos 4250)] :=
  (lex_10_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4250) = lexBefore s permutation10 180 := by
  exact (positive_lex_of_descriptor s 4250 permutation10 181 (by rfl)).trans ((lex_skipped s permutation10 180 181 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation10 180) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation10 180 by rw [image10_eq]; rfl))

theorem lex_10_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4251) (Sat.Literal.pos 4250) (Sat.Literal.pos 180) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation10 180 (assignment s)
    (Sat.Literal.pos 4251) (Sat.Literal.pos 4250) (Sat.Literal.pos 180) (Sat.Literal.pos 75) (positive_of_descriptor s 4251 (.lex permutation10 180) (by rfl)) (lex_10_180_prefix s) (positive_select s 180) (lex_10_180_image s)

theorem lex_10_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.pos 180), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation10 180 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4250) (Sat.Literal.pos 180) (Sat.Literal.pos 75) (lex_10_180_prefix s) (positive_select s 180) (lex_10_180_image s)

theorem lex_10_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.pos 4250)] :=
  (lex_10_180_gate s).prop _ (List.Mem.head _)

theorem lex_10_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.neg 180), (Sat.Literal.pos 75)] :=
  (lex_10_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.pos 180), (Sat.Literal.neg 75)] :=
  (lex_10_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.neg 180), (Sat.Literal.neg 75), (Sat.Literal.pos 4251)] :=
  (lex_10_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4250), (Sat.Literal.pos 180), (Sat.Literal.pos 75), (Sat.Literal.pos 4251)] :=
  (lex_10_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4251) = lexBefore s permutation10 179 := by
  exact (positive_lex_of_descriptor s 4251 permutation10 180 (by rfl)).trans ((lex_skipped s permutation10 179 180 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation10 179) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation10 179 by rw [image10_eq]; rfl))

theorem lex_10_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4252) (Sat.Literal.pos 4251) (Sat.Literal.pos 179) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation10 179 (assignment s)
    (Sat.Literal.pos 4252) (Sat.Literal.pos 4251) (Sat.Literal.pos 179) (Sat.Literal.pos 59) (positive_of_descriptor s 4252 (.lex permutation10 179) (by rfl)) (lex_10_179_prefix s) (positive_select s 179) (lex_10_179_image s)

theorem lex_10_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.pos 179), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation10 179 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4251) (Sat.Literal.pos 179) (Sat.Literal.pos 59) (lex_10_179_prefix s) (positive_select s 179) (lex_10_179_image s)

theorem lex_10_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.pos 4251)] :=
  (lex_10_179_gate s).prop _ (List.Mem.head _)

theorem lex_10_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.neg 179), (Sat.Literal.pos 59)] :=
  (lex_10_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.pos 179), (Sat.Literal.neg 59)] :=
  (lex_10_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.neg 179), (Sat.Literal.neg 59), (Sat.Literal.pos 4252)] :=
  (lex_10_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4251), (Sat.Literal.pos 179), (Sat.Literal.pos 59), (Sat.Literal.pos 4252)] :=
  (lex_10_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4252) = lexBefore s permutation10 178 := by
  exact (positive_lex_of_descriptor s 4252 permutation10 179 (by rfl)).trans ((lex_skipped s permutation10 178 179 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation10 178) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation10 178 by rw [image10_eq]; rfl))

theorem lex_10_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4253) (Sat.Literal.pos 4252) (Sat.Literal.pos 178) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation10 178 (assignment s)
    (Sat.Literal.pos 4253) (Sat.Literal.pos 4252) (Sat.Literal.pos 178) (Sat.Literal.pos 43) (positive_of_descriptor s 4253 (.lex permutation10 178) (by rfl)) (lex_10_178_prefix s) (positive_select s 178) (lex_10_178_image s)

theorem lex_10_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.pos 178), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation10 178 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4252) (Sat.Literal.pos 178) (Sat.Literal.pos 43) (lex_10_178_prefix s) (positive_select s 178) (lex_10_178_image s)

theorem lex_10_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.pos 4252)] :=
  (lex_10_178_gate s).prop _ (List.Mem.head _)

theorem lex_10_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.neg 178), (Sat.Literal.pos 43)] :=
  (lex_10_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.pos 178), (Sat.Literal.neg 43)] :=
  (lex_10_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.neg 178), (Sat.Literal.neg 43), (Sat.Literal.pos 4253)] :=
  (lex_10_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4252), (Sat.Literal.pos 178), (Sat.Literal.pos 43), (Sat.Literal.pos 4253)] :=
  (lex_10_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4253) = lexBefore s permutation10 177 := by
  exact (positive_lex_of_descriptor s 4253 permutation10 178 (by rfl)).trans ((lex_skipped s permutation10 177 178 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation10 177) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation10 177 by rw [image10_eq]; rfl))

theorem lex_10_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4254) (Sat.Literal.pos 4253) (Sat.Literal.pos 177) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation10 177 (assignment s)
    (Sat.Literal.pos 4254) (Sat.Literal.pos 4253) (Sat.Literal.pos 177) (Sat.Literal.pos 27) (positive_of_descriptor s 4254 (.lex permutation10 177) (by rfl)) (lex_10_177_prefix s) (positive_select s 177) (lex_10_177_image s)

theorem lex_10_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.pos 177), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation10 177 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4253) (Sat.Literal.pos 177) (Sat.Literal.pos 27) (lex_10_177_prefix s) (positive_select s 177) (lex_10_177_image s)

theorem lex_10_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.pos 4253)] :=
  (lex_10_177_gate s).prop _ (List.Mem.head _)

theorem lex_10_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.neg 177), (Sat.Literal.pos 27)] :=
  (lex_10_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.pos 177), (Sat.Literal.neg 27)] :=
  (lex_10_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.neg 177), (Sat.Literal.neg 27), (Sat.Literal.pos 4254)] :=
  (lex_10_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4253), (Sat.Literal.pos 177), (Sat.Literal.pos 27), (Sat.Literal.pos 4254)] :=
  (lex_10_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4254) = lexBefore s permutation10 176 := by
  exact (positive_lex_of_descriptor s 4254 permutation10 177 (by rfl)).trans ((lex_skipped s permutation10 176 177 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation10 176) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation10 176 by rw [image10_eq]; rfl))

theorem lex_10_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4255) (Sat.Literal.pos 4254) (Sat.Literal.pos 176) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation10 176 (assignment s)
    (Sat.Literal.pos 4255) (Sat.Literal.pos 4254) (Sat.Literal.pos 176) (Sat.Literal.pos 11) (positive_of_descriptor s 4255 (.lex permutation10 176) (by rfl)) (lex_10_176_prefix s) (positive_select s 176) (lex_10_176_image s)

theorem lex_10_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.pos 176), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation10 176 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4254) (Sat.Literal.pos 176) (Sat.Literal.pos 11) (lex_10_176_prefix s) (positive_select s 176) (lex_10_176_image s)

theorem lex_10_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.pos 4254)] :=
  (lex_10_176_gate s).prop _ (List.Mem.head _)

theorem lex_10_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.neg 176), (Sat.Literal.pos 11)] :=
  (lex_10_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.pos 176), (Sat.Literal.neg 11)] :=
  (lex_10_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.neg 176), (Sat.Literal.neg 11), (Sat.Literal.pos 4255)] :=
  (lex_10_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4254), (Sat.Literal.pos 176), (Sat.Literal.pos 11), (Sat.Literal.pos 4255)] :=
  (lex_10_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4255) = lexBefore s permutation10 175 := by
  exact (positive_lex_of_descriptor s 4255 permutation10 176 (by rfl)).trans ((lex_skipped s permutation10 175 176 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation10 175) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation10 175 by rw [image10_eq]; rfl))

theorem lex_10_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4256) (Sat.Literal.pos 4255) (Sat.Literal.pos 175) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation10 175 (assignment s)
    (Sat.Literal.pos 4256) (Sat.Literal.pos 4255) (Sat.Literal.pos 175) (Sat.Literal.pos 250) (positive_of_descriptor s 4256 (.lex permutation10 175) (by rfl)) (lex_10_175_prefix s) (positive_select s 175) (lex_10_175_image s)

theorem lex_10_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.pos 175), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation10 175 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4255) (Sat.Literal.pos 175) (Sat.Literal.pos 250) (lex_10_175_prefix s) (positive_select s 175) (lex_10_175_image s)

theorem lex_10_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.pos 4255)] :=
  (lex_10_175_gate s).prop _ (List.Mem.head _)

theorem lex_10_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.neg 175), (Sat.Literal.pos 250)] :=
  (lex_10_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.pos 175), (Sat.Literal.neg 250)] :=
  (lex_10_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.neg 175), (Sat.Literal.neg 250), (Sat.Literal.pos 4256)] :=
  (lex_10_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4255), (Sat.Literal.pos 175), (Sat.Literal.pos 250), (Sat.Literal.pos 4256)] :=
  (lex_10_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4256) = lexBefore s permutation10 174 := by
  exact (positive_lex_of_descriptor s 4256 permutation10 175 (by rfl)).trans ((lex_skipped s permutation10 174 175 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation10 174) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation10 174 by rw [image10_eq]; rfl))

theorem lex_10_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4257) (Sat.Literal.pos 4256) (Sat.Literal.pos 174) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation10 174 (assignment s)
    (Sat.Literal.pos 4257) (Sat.Literal.pos 4256) (Sat.Literal.pos 174) (Sat.Literal.pos 234) (positive_of_descriptor s 4257 (.lex permutation10 174) (by rfl)) (lex_10_174_prefix s) (positive_select s 174) (lex_10_174_image s)

theorem lex_10_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.pos 174), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation10 174 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4256) (Sat.Literal.pos 174) (Sat.Literal.pos 234) (lex_10_174_prefix s) (positive_select s 174) (lex_10_174_image s)

theorem lex_10_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.pos 4256)] :=
  (lex_10_174_gate s).prop _ (List.Mem.head _)

theorem lex_10_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.neg 174), (Sat.Literal.pos 234)] :=
  (lex_10_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.pos 174), (Sat.Literal.neg 234)] :=
  (lex_10_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.neg 174), (Sat.Literal.neg 234), (Sat.Literal.pos 4257)] :=
  (lex_10_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4256), (Sat.Literal.pos 174), (Sat.Literal.pos 234), (Sat.Literal.pos 4257)] :=
  (lex_10_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4257) = lexBefore s permutation10 173 := by
  exact (positive_lex_of_descriptor s 4257 permutation10 174 (by rfl)).trans ((lex_skipped s permutation10 173 174 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation10 173) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation10 173 by rw [image10_eq]; rfl))

theorem lex_10_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4258) (Sat.Literal.pos 4257) (Sat.Literal.pos 173) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation10 173 (assignment s)
    (Sat.Literal.pos 4258) (Sat.Literal.pos 4257) (Sat.Literal.pos 173) (Sat.Literal.pos 218) (positive_of_descriptor s 4258 (.lex permutation10 173) (by rfl)) (lex_10_173_prefix s) (positive_select s 173) (lex_10_173_image s)

theorem lex_10_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.pos 173), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation10 173 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4257) (Sat.Literal.pos 173) (Sat.Literal.pos 218) (lex_10_173_prefix s) (positive_select s 173) (lex_10_173_image s)

theorem lex_10_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.pos 4257)] :=
  (lex_10_173_gate s).prop _ (List.Mem.head _)

theorem lex_10_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.neg 173), (Sat.Literal.pos 218)] :=
  (lex_10_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.pos 173), (Sat.Literal.neg 218)] :=
  (lex_10_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.neg 173), (Sat.Literal.neg 218), (Sat.Literal.pos 4258)] :=
  (lex_10_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4257), (Sat.Literal.pos 173), (Sat.Literal.pos 218), (Sat.Literal.pos 4258)] :=
  (lex_10_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4258) = lexBefore s permutation10 172 := by
  exact (positive_lex_of_descriptor s 4258 permutation10 173 (by rfl)).trans ((lex_skipped s permutation10 172 173 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation10 172) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation10 172 by rw [image10_eq]; rfl))

theorem lex_10_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4259) (Sat.Literal.pos 4258) (Sat.Literal.pos 172) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation10 172 (assignment s)
    (Sat.Literal.pos 4259) (Sat.Literal.pos 4258) (Sat.Literal.pos 172) (Sat.Literal.pos 202) (positive_of_descriptor s 4259 (.lex permutation10 172) (by rfl)) (lex_10_172_prefix s) (positive_select s 172) (lex_10_172_image s)

theorem lex_10_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.pos 172), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation10 172 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4258) (Sat.Literal.pos 172) (Sat.Literal.pos 202) (lex_10_172_prefix s) (positive_select s 172) (lex_10_172_image s)

theorem lex_10_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.pos 4258)] :=
  (lex_10_172_gate s).prop _ (List.Mem.head _)

theorem lex_10_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.neg 172), (Sat.Literal.pos 202)] :=
  (lex_10_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.pos 172), (Sat.Literal.neg 202)] :=
  (lex_10_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.neg 172), (Sat.Literal.neg 202), (Sat.Literal.pos 4259)] :=
  (lex_10_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4258), (Sat.Literal.pos 172), (Sat.Literal.pos 202), (Sat.Literal.pos 4259)] :=
  (lex_10_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4259) = lexBefore s permutation10 171 := by
  exact (positive_lex_of_descriptor s 4259 permutation10 172 (by rfl)).trans ((lex_skipped s permutation10 171 172 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation10 171) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation10 171 by rw [image10_eq]; rfl))

theorem lex_10_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4260) (Sat.Literal.pos 4259) (Sat.Literal.pos 171) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation10 171 (assignment s)
    (Sat.Literal.pos 4260) (Sat.Literal.pos 4259) (Sat.Literal.pos 171) (Sat.Literal.pos 186) (positive_of_descriptor s 4260 (.lex permutation10 171) (by rfl)) (lex_10_171_prefix s) (positive_select s 171) (lex_10_171_image s)

theorem lex_10_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.pos 171), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation10 171 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4259) (Sat.Literal.pos 171) (Sat.Literal.pos 186) (lex_10_171_prefix s) (positive_select s 171) (lex_10_171_image s)

theorem lex_10_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.pos 4259)] :=
  (lex_10_171_gate s).prop _ (List.Mem.head _)

theorem lex_10_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.neg 171), (Sat.Literal.pos 186)] :=
  (lex_10_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.pos 171), (Sat.Literal.neg 186)] :=
  (lex_10_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.neg 171), (Sat.Literal.neg 186), (Sat.Literal.pos 4260)] :=
  (lex_10_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4259), (Sat.Literal.pos 171), (Sat.Literal.pos 186), (Sat.Literal.pos 4260)] :=
  (lex_10_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4260) = lexBefore s permutation10 169 := by
  exact (positive_lex_of_descriptor s 4260 permutation10 171 (by rfl)).trans ((lex_skipped s permutation10 169 171 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 170 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation10 169) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation10 169 by rw [image10_eq]; rfl))

theorem lex_10_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4261) (Sat.Literal.pos 4260) (Sat.Literal.pos 169) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation10 169 (assignment s)
    (Sat.Literal.pos 4261) (Sat.Literal.pos 4260) (Sat.Literal.pos 169) (Sat.Literal.pos 154) (positive_of_descriptor s 4261 (.lex permutation10 169) (by rfl)) (lex_10_169_prefix s) (positive_select s 169) (lex_10_169_image s)

theorem lex_10_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.pos 169), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation10 169 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4260) (Sat.Literal.pos 169) (Sat.Literal.pos 154) (lex_10_169_prefix s) (positive_select s 169) (lex_10_169_image s)

theorem lex_10_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.pos 4260)] :=
  (lex_10_169_gate s).prop _ (List.Mem.head _)

theorem lex_10_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.neg 169), (Sat.Literal.pos 154)] :=
  (lex_10_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.pos 169), (Sat.Literal.neg 154)] :=
  (lex_10_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.neg 169), (Sat.Literal.neg 154), (Sat.Literal.pos 4261)] :=
  (lex_10_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4260), (Sat.Literal.pos 169), (Sat.Literal.pos 154), (Sat.Literal.pos 4261)] :=
  (lex_10_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4261) = lexBefore s permutation10 168 := by
  exact (positive_lex_of_descriptor s 4261 permutation10 169 (by rfl)).trans ((lex_skipped s permutation10 168 169 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation10 168) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation10 168 by rw [image10_eq]; rfl))

theorem lex_10_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4262) (Sat.Literal.pos 4261) (Sat.Literal.pos 168) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation10 168 (assignment s)
    (Sat.Literal.pos 4262) (Sat.Literal.pos 4261) (Sat.Literal.pos 168) (Sat.Literal.pos 138) (positive_of_descriptor s 4262 (.lex permutation10 168) (by rfl)) (lex_10_168_prefix s) (positive_select s 168) (lex_10_168_image s)

theorem lex_10_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.pos 168), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation10 168 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4261) (Sat.Literal.pos 168) (Sat.Literal.pos 138) (lex_10_168_prefix s) (positive_select s 168) (lex_10_168_image s)

theorem lex_10_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.pos 4261)] :=
  (lex_10_168_gate s).prop _ (List.Mem.head _)

theorem lex_10_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.neg 168), (Sat.Literal.pos 138)] :=
  (lex_10_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.pos 168), (Sat.Literal.neg 138)] :=
  (lex_10_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.neg 168), (Sat.Literal.neg 138), (Sat.Literal.pos 4262)] :=
  (lex_10_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4261), (Sat.Literal.pos 168), (Sat.Literal.pos 138), (Sat.Literal.pos 4262)] :=
  (lex_10_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4262) = lexBefore s permutation10 167 := by
  exact (positive_lex_of_descriptor s 4262 permutation10 168 (by rfl)).trans ((lex_skipped s permutation10 167 168 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation10 167) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation10 167 by rw [image10_eq]; rfl))

theorem lex_10_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4263) (Sat.Literal.pos 4262) (Sat.Literal.pos 167) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation10 167 (assignment s)
    (Sat.Literal.pos 4263) (Sat.Literal.pos 4262) (Sat.Literal.pos 167) (Sat.Literal.pos 122) (positive_of_descriptor s 4263 (.lex permutation10 167) (by rfl)) (lex_10_167_prefix s) (positive_select s 167) (lex_10_167_image s)

theorem lex_10_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.pos 167), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation10 167 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4262) (Sat.Literal.pos 167) (Sat.Literal.pos 122) (lex_10_167_prefix s) (positive_select s 167) (lex_10_167_image s)

theorem lex_10_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.pos 4262)] :=
  (lex_10_167_gate s).prop _ (List.Mem.head _)

theorem lex_10_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.neg 167), (Sat.Literal.pos 122)] :=
  (lex_10_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.pos 167), (Sat.Literal.neg 122)] :=
  (lex_10_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.neg 167), (Sat.Literal.neg 122), (Sat.Literal.pos 4263)] :=
  (lex_10_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4262), (Sat.Literal.pos 167), (Sat.Literal.pos 122), (Sat.Literal.pos 4263)] :=
  (lex_10_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4263) = lexBefore s permutation10 166 := by
  exact (positive_lex_of_descriptor s 4263 permutation10 167 (by rfl)).trans ((lex_skipped s permutation10 166 167 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation10 166) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation10 166 by rw [image10_eq]; rfl))

theorem lex_10_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4264) (Sat.Literal.pos 4263) (Sat.Literal.pos 166) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation10 166 (assignment s)
    (Sat.Literal.pos 4264) (Sat.Literal.pos 4263) (Sat.Literal.pos 166) (Sat.Literal.pos 106) (positive_of_descriptor s 4264 (.lex permutation10 166) (by rfl)) (lex_10_166_prefix s) (positive_select s 166) (lex_10_166_image s)

theorem lex_10_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.pos 166), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation10 166 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4263) (Sat.Literal.pos 166) (Sat.Literal.pos 106) (lex_10_166_prefix s) (positive_select s 166) (lex_10_166_image s)

theorem lex_10_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.pos 4263)] :=
  (lex_10_166_gate s).prop _ (List.Mem.head _)

theorem lex_10_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.neg 166), (Sat.Literal.pos 106)] :=
  (lex_10_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.pos 166), (Sat.Literal.neg 106)] :=
  (lex_10_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.neg 166), (Sat.Literal.neg 106), (Sat.Literal.pos 4264)] :=
  (lex_10_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4263), (Sat.Literal.pos 166), (Sat.Literal.pos 106), (Sat.Literal.pos 4264)] :=
  (lex_10_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4264) = lexBefore s permutation10 165 := by
  exact (positive_lex_of_descriptor s 4264 permutation10 166 (by rfl)).trans ((lex_skipped s permutation10 165 166 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation10 165) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation10 165 by rw [image10_eq]; rfl))

theorem lex_10_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4265) (Sat.Literal.pos 4264) (Sat.Literal.pos 165) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation10 165 (assignment s)
    (Sat.Literal.pos 4265) (Sat.Literal.pos 4264) (Sat.Literal.pos 165) (Sat.Literal.pos 90) (positive_of_descriptor s 4265 (.lex permutation10 165) (by rfl)) (lex_10_165_prefix s) (positive_select s 165) (lex_10_165_image s)

theorem lex_10_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.pos 165), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation10 165 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4264) (Sat.Literal.pos 165) (Sat.Literal.pos 90) (lex_10_165_prefix s) (positive_select s 165) (lex_10_165_image s)

theorem lex_10_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.pos 4264)] :=
  (lex_10_165_gate s).prop _ (List.Mem.head _)

theorem lex_10_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.neg 165), (Sat.Literal.pos 90)] :=
  (lex_10_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.pos 165), (Sat.Literal.neg 90)] :=
  (lex_10_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.neg 165), (Sat.Literal.neg 90), (Sat.Literal.pos 4265)] :=
  (lex_10_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4264), (Sat.Literal.pos 165), (Sat.Literal.pos 90), (Sat.Literal.pos 4265)] :=
  (lex_10_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4265) = lexBefore s permutation10 164 := by
  exact (positive_lex_of_descriptor s 4265 permutation10 165 (by rfl)).trans ((lex_skipped s permutation10 164 165 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation10 164) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation10 164 by rw [image10_eq]; rfl))

theorem lex_10_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4266) (Sat.Literal.pos 4265) (Sat.Literal.pos 164) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation10 164 (assignment s)
    (Sat.Literal.pos 4266) (Sat.Literal.pos 4265) (Sat.Literal.pos 164) (Sat.Literal.pos 74) (positive_of_descriptor s 4266 (.lex permutation10 164) (by rfl)) (lex_10_164_prefix s) (positive_select s 164) (lex_10_164_image s)

theorem lex_10_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.pos 164), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation10 164 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4265) (Sat.Literal.pos 164) (Sat.Literal.pos 74) (lex_10_164_prefix s) (positive_select s 164) (lex_10_164_image s)

theorem lex_10_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.pos 4265)] :=
  (lex_10_164_gate s).prop _ (List.Mem.head _)

theorem lex_10_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.neg 164), (Sat.Literal.pos 74)] :=
  (lex_10_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.pos 164), (Sat.Literal.neg 74)] :=
  (lex_10_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.neg 164), (Sat.Literal.neg 74), (Sat.Literal.pos 4266)] :=
  (lex_10_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4265), (Sat.Literal.pos 164), (Sat.Literal.pos 74), (Sat.Literal.pos 4266)] :=
  (lex_10_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4266) = lexBefore s permutation10 163 := by
  exact (positive_lex_of_descriptor s 4266 permutation10 164 (by rfl)).trans ((lex_skipped s permutation10 163 164 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation10 163) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation10 163 by rw [image10_eq]; rfl))

theorem lex_10_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4267) (Sat.Literal.pos 4266) (Sat.Literal.pos 163) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation10 163 (assignment s)
    (Sat.Literal.pos 4267) (Sat.Literal.pos 4266) (Sat.Literal.pos 163) (Sat.Literal.pos 58) (positive_of_descriptor s 4267 (.lex permutation10 163) (by rfl)) (lex_10_163_prefix s) (positive_select s 163) (lex_10_163_image s)

theorem lex_10_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.pos 163), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation10 163 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4266) (Sat.Literal.pos 163) (Sat.Literal.pos 58) (lex_10_163_prefix s) (positive_select s 163) (lex_10_163_image s)

theorem lex_10_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.pos 4266)] :=
  (lex_10_163_gate s).prop _ (List.Mem.head _)

theorem lex_10_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.neg 163), (Sat.Literal.pos 58)] :=
  (lex_10_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.pos 163), (Sat.Literal.neg 58)] :=
  (lex_10_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.neg 163), (Sat.Literal.neg 58), (Sat.Literal.pos 4267)] :=
  (lex_10_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4266), (Sat.Literal.pos 163), (Sat.Literal.pos 58), (Sat.Literal.pos 4267)] :=
  (lex_10_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4267) = lexBefore s permutation10 162 := by
  exact (positive_lex_of_descriptor s 4267 permutation10 163 (by rfl)).trans ((lex_skipped s permutation10 162 163 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation10 162) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation10 162 by rw [image10_eq]; rfl))

theorem lex_10_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4268) (Sat.Literal.pos 4267) (Sat.Literal.pos 162) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation10 162 (assignment s)
    (Sat.Literal.pos 4268) (Sat.Literal.pos 4267) (Sat.Literal.pos 162) (Sat.Literal.pos 42) (positive_of_descriptor s 4268 (.lex permutation10 162) (by rfl)) (lex_10_162_prefix s) (positive_select s 162) (lex_10_162_image s)

theorem lex_10_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.pos 162), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation10 162 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4267) (Sat.Literal.pos 162) (Sat.Literal.pos 42) (lex_10_162_prefix s) (positive_select s 162) (lex_10_162_image s)

theorem lex_10_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.pos 4267)] :=
  (lex_10_162_gate s).prop _ (List.Mem.head _)

theorem lex_10_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.neg 162), (Sat.Literal.pos 42)] :=
  (lex_10_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.pos 162), (Sat.Literal.neg 42)] :=
  (lex_10_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.neg 162), (Sat.Literal.neg 42), (Sat.Literal.pos 4268)] :=
  (lex_10_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4267), (Sat.Literal.pos 162), (Sat.Literal.pos 42), (Sat.Literal.pos 4268)] :=
  (lex_10_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4268) = lexBefore s permutation10 161 := by
  exact (positive_lex_of_descriptor s 4268 permutation10 162 (by rfl)).trans ((lex_skipped s permutation10 161 162 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation10 161) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation10 161 by rw [image10_eq]; rfl))

theorem lex_10_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4269) (Sat.Literal.pos 4268) (Sat.Literal.pos 161) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation10 161 (assignment s)
    (Sat.Literal.pos 4269) (Sat.Literal.pos 4268) (Sat.Literal.pos 161) (Sat.Literal.pos 26) (positive_of_descriptor s 4269 (.lex permutation10 161) (by rfl)) (lex_10_161_prefix s) (positive_select s 161) (lex_10_161_image s)

theorem lex_10_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.pos 161), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation10 161 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4268) (Sat.Literal.pos 161) (Sat.Literal.pos 26) (lex_10_161_prefix s) (positive_select s 161) (lex_10_161_image s)

theorem lex_10_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.pos 4268)] :=
  (lex_10_161_gate s).prop _ (List.Mem.head _)

theorem lex_10_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.neg 161), (Sat.Literal.pos 26)] :=
  (lex_10_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.pos 161), (Sat.Literal.neg 26)] :=
  (lex_10_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.neg 161), (Sat.Literal.neg 26), (Sat.Literal.pos 4269)] :=
  (lex_10_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4268), (Sat.Literal.pos 161), (Sat.Literal.pos 26), (Sat.Literal.pos 4269)] :=
  (lex_10_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4269) = lexBefore s permutation10 160 := by
  exact (positive_lex_of_descriptor s 4269 permutation10 161 (by rfl)).trans ((lex_skipped s permutation10 160 161 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation10 160) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation10 160 by rw [image10_eq]; rfl))

theorem lex_10_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4270) (Sat.Literal.pos 4269) (Sat.Literal.pos 160) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation10 160 (assignment s)
    (Sat.Literal.pos 4270) (Sat.Literal.pos 4269) (Sat.Literal.pos 160) (Sat.Literal.pos 10) (positive_of_descriptor s 4270 (.lex permutation10 160) (by rfl)) (lex_10_160_prefix s) (positive_select s 160) (lex_10_160_image s)

theorem lex_10_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.pos 160), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation10 160 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4269) (Sat.Literal.pos 160) (Sat.Literal.pos 10) (lex_10_160_prefix s) (positive_select s 160) (lex_10_160_image s)

theorem lex_10_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.pos 4269)] :=
  (lex_10_160_gate s).prop _ (List.Mem.head _)

theorem lex_10_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.neg 160), (Sat.Literal.pos 10)] :=
  (lex_10_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.pos 160), (Sat.Literal.neg 10)] :=
  (lex_10_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.neg 160), (Sat.Literal.neg 10), (Sat.Literal.pos 4270)] :=
  (lex_10_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4269), (Sat.Literal.pos 160), (Sat.Literal.pos 10), (Sat.Literal.pos 4270)] :=
  (lex_10_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4270) = lexBefore s permutation10 159 := by
  exact (positive_lex_of_descriptor s 4270 permutation10 160 (by rfl)).trans ((lex_skipped s permutation10 159 160 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation10 159) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation10 159 by rw [image10_eq]; rfl))

theorem lex_10_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4271) (Sat.Literal.pos 4270) (Sat.Literal.pos 159) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation10 159 (assignment s)
    (Sat.Literal.pos 4271) (Sat.Literal.pos 4270) (Sat.Literal.pos 159) (Sat.Literal.pos 249) (positive_of_descriptor s 4271 (.lex permutation10 159) (by rfl)) (lex_10_159_prefix s) (positive_select s 159) (lex_10_159_image s)

theorem lex_10_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.pos 159), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation10 159 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4270) (Sat.Literal.pos 159) (Sat.Literal.pos 249) (lex_10_159_prefix s) (positive_select s 159) (lex_10_159_image s)

theorem lex_10_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.pos 4270)] :=
  (lex_10_159_gate s).prop _ (List.Mem.head _)

theorem lex_10_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.neg 159), (Sat.Literal.pos 249)] :=
  (lex_10_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.pos 159), (Sat.Literal.neg 249)] :=
  (lex_10_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.neg 159), (Sat.Literal.neg 249), (Sat.Literal.pos 4271)] :=
  (lex_10_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4270), (Sat.Literal.pos 159), (Sat.Literal.pos 249), (Sat.Literal.pos 4271)] :=
  (lex_10_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4271) = lexBefore s permutation10 158 := by
  exact (positive_lex_of_descriptor s 4271 permutation10 159 (by rfl)).trans ((lex_skipped s permutation10 158 159 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation10 158) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation10 158 by rw [image10_eq]; rfl))

theorem lex_10_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4272) (Sat.Literal.pos 4271) (Sat.Literal.pos 158) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation10 158 (assignment s)
    (Sat.Literal.pos 4272) (Sat.Literal.pos 4271) (Sat.Literal.pos 158) (Sat.Literal.pos 233) (positive_of_descriptor s 4272 (.lex permutation10 158) (by rfl)) (lex_10_158_prefix s) (positive_select s 158) (lex_10_158_image s)

theorem lex_10_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.pos 158), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation10 158 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4271) (Sat.Literal.pos 158) (Sat.Literal.pos 233) (lex_10_158_prefix s) (positive_select s 158) (lex_10_158_image s)

theorem lex_10_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.pos 4271)] :=
  (lex_10_158_gate s).prop _ (List.Mem.head _)

theorem lex_10_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.neg 158), (Sat.Literal.pos 233)] :=
  (lex_10_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.pos 158), (Sat.Literal.neg 233)] :=
  (lex_10_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.neg 158), (Sat.Literal.neg 233), (Sat.Literal.pos 4272)] :=
  (lex_10_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4271), (Sat.Literal.pos 158), (Sat.Literal.pos 233), (Sat.Literal.pos 4272)] :=
  (lex_10_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4272) = lexBefore s permutation10 157 := by
  exact (positive_lex_of_descriptor s 4272 permutation10 158 (by rfl)).trans ((lex_skipped s permutation10 157 158 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation10 157) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation10 157 by rw [image10_eq]; rfl))

theorem lex_10_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4273) (Sat.Literal.pos 4272) (Sat.Literal.pos 157) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation10 157 (assignment s)
    (Sat.Literal.pos 4273) (Sat.Literal.pos 4272) (Sat.Literal.pos 157) (Sat.Literal.pos 217) (positive_of_descriptor s 4273 (.lex permutation10 157) (by rfl)) (lex_10_157_prefix s) (positive_select s 157) (lex_10_157_image s)

theorem lex_10_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.pos 157), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation10 157 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4272) (Sat.Literal.pos 157) (Sat.Literal.pos 217) (lex_10_157_prefix s) (positive_select s 157) (lex_10_157_image s)

theorem lex_10_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.pos 4272)] :=
  (lex_10_157_gate s).prop _ (List.Mem.head _)

theorem lex_10_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.neg 157), (Sat.Literal.pos 217)] :=
  (lex_10_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.pos 157), (Sat.Literal.neg 217)] :=
  (lex_10_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.neg 157), (Sat.Literal.neg 217), (Sat.Literal.pos 4273)] :=
  (lex_10_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4272), (Sat.Literal.pos 157), (Sat.Literal.pos 217), (Sat.Literal.pos 4273)] :=
  (lex_10_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4273) = lexBefore s permutation10 156 := by
  exact (positive_lex_of_descriptor s 4273 permutation10 157 (by rfl)).trans ((lex_skipped s permutation10 156 157 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation10 156) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation10 156 by rw [image10_eq]; rfl))

theorem lex_10_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4274) (Sat.Literal.pos 4273) (Sat.Literal.pos 156) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation10 156 (assignment s)
    (Sat.Literal.pos 4274) (Sat.Literal.pos 4273) (Sat.Literal.pos 156) (Sat.Literal.pos 201) (positive_of_descriptor s 4274 (.lex permutation10 156) (by rfl)) (lex_10_156_prefix s) (positive_select s 156) (lex_10_156_image s)

theorem lex_10_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.pos 156), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation10 156 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4273) (Sat.Literal.pos 156) (Sat.Literal.pos 201) (lex_10_156_prefix s) (positive_select s 156) (lex_10_156_image s)

theorem lex_10_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.pos 4273)] :=
  (lex_10_156_gate s).prop _ (List.Mem.head _)

theorem lex_10_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.neg 156), (Sat.Literal.pos 201)] :=
  (lex_10_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.pos 156), (Sat.Literal.neg 201)] :=
  (lex_10_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.neg 156), (Sat.Literal.neg 201), (Sat.Literal.pos 4274)] :=
  (lex_10_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4273), (Sat.Literal.pos 156), (Sat.Literal.pos 201), (Sat.Literal.pos 4274)] :=
  (lex_10_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4274) = lexBefore s permutation10 155 := by
  exact (positive_lex_of_descriptor s 4274 permutation10 156 (by rfl)).trans ((lex_skipped s permutation10 155 156 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation10 155) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation10 155 by rw [image10_eq]; rfl))

theorem lex_10_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4275) (Sat.Literal.pos 4274) (Sat.Literal.pos 155) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation10 155 (assignment s)
    (Sat.Literal.pos 4275) (Sat.Literal.pos 4274) (Sat.Literal.pos 155) (Sat.Literal.pos 185) (positive_of_descriptor s 4275 (.lex permutation10 155) (by rfl)) (lex_10_155_prefix s) (positive_select s 155) (lex_10_155_image s)

theorem lex_10_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.pos 155), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation10 155 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4274) (Sat.Literal.pos 155) (Sat.Literal.pos 185) (lex_10_155_prefix s) (positive_select s 155) (lex_10_155_image s)

theorem lex_10_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.pos 4274)] :=
  (lex_10_155_gate s).prop _ (List.Mem.head _)

theorem lex_10_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.neg 155), (Sat.Literal.pos 185)] :=
  (lex_10_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.pos 155), (Sat.Literal.neg 185)] :=
  (lex_10_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.neg 155), (Sat.Literal.neg 185), (Sat.Literal.pos 4275)] :=
  (lex_10_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4274), (Sat.Literal.pos 155), (Sat.Literal.pos 185), (Sat.Literal.pos 4275)] :=
  (lex_10_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4275) = lexBefore s permutation10 154 := by
  exact (positive_lex_of_descriptor s 4275 permutation10 155 (by rfl)).trans ((lex_skipped s permutation10 154 155 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation10 154) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation10 154 by rw [image10_eq]; rfl))

theorem lex_10_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4276) (Sat.Literal.pos 4275) (Sat.Literal.pos 154) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation10 154 (assignment s)
    (Sat.Literal.pos 4276) (Sat.Literal.pos 4275) (Sat.Literal.pos 154) (Sat.Literal.pos 169) (positive_of_descriptor s 4276 (.lex permutation10 154) (by rfl)) (lex_10_154_prefix s) (positive_select s 154) (lex_10_154_image s)

theorem lex_10_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.pos 154), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation10 154 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4275) (Sat.Literal.pos 154) (Sat.Literal.pos 169) (lex_10_154_prefix s) (positive_select s 154) (lex_10_154_image s)

theorem lex_10_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.pos 4275)] :=
  (lex_10_154_gate s).prop _ (List.Mem.head _)

theorem lex_10_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.neg 154), (Sat.Literal.pos 169)] :=
  (lex_10_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.pos 154), (Sat.Literal.neg 169)] :=
  (lex_10_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.neg 154), (Sat.Literal.neg 169), (Sat.Literal.pos 4276)] :=
  (lex_10_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4275), (Sat.Literal.pos 154), (Sat.Literal.pos 169), (Sat.Literal.pos 4276)] :=
  (lex_10_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4276) = lexBefore s permutation10 152 := by
  exact (positive_lex_of_descriptor s 4276 permutation10 154 (by rfl)).trans ((lex_skipped s permutation10 152 154 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 153 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation10 152) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation10 152 by rw [image10_eq]; rfl))

theorem lex_10_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4277) (Sat.Literal.pos 4276) (Sat.Literal.pos 152) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation10 152 (assignment s)
    (Sat.Literal.pos 4277) (Sat.Literal.pos 4276) (Sat.Literal.pos 152) (Sat.Literal.pos 137) (positive_of_descriptor s 4277 (.lex permutation10 152) (by rfl)) (lex_10_152_prefix s) (positive_select s 152) (lex_10_152_image s)

theorem lex_10_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.pos 152), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation10 152 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4276) (Sat.Literal.pos 152) (Sat.Literal.pos 137) (lex_10_152_prefix s) (positive_select s 152) (lex_10_152_image s)

theorem lex_10_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.pos 4276)] :=
  (lex_10_152_gate s).prop _ (List.Mem.head _)

theorem lex_10_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.neg 152), (Sat.Literal.pos 137)] :=
  (lex_10_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.pos 152), (Sat.Literal.neg 137)] :=
  (lex_10_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.neg 152), (Sat.Literal.neg 137), (Sat.Literal.pos 4277)] :=
  (lex_10_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4276), (Sat.Literal.pos 152), (Sat.Literal.pos 137), (Sat.Literal.pos 4277)] :=
  (lex_10_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4277) = lexBefore s permutation10 151 := by
  exact (positive_lex_of_descriptor s 4277 permutation10 152 (by rfl)).trans ((lex_skipped s permutation10 151 152 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation10 151) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation10 151 by rw [image10_eq]; rfl))

theorem lex_10_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4278) (Sat.Literal.pos 4277) (Sat.Literal.pos 151) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation10 151 (assignment s)
    (Sat.Literal.pos 4278) (Sat.Literal.pos 4277) (Sat.Literal.pos 151) (Sat.Literal.pos 121) (positive_of_descriptor s 4278 (.lex permutation10 151) (by rfl)) (lex_10_151_prefix s) (positive_select s 151) (lex_10_151_image s)

theorem lex_10_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.pos 151), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation10 151 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4277) (Sat.Literal.pos 151) (Sat.Literal.pos 121) (lex_10_151_prefix s) (positive_select s 151) (lex_10_151_image s)

theorem lex_10_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.pos 4277)] :=
  (lex_10_151_gate s).prop _ (List.Mem.head _)

theorem lex_10_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.neg 151), (Sat.Literal.pos 121)] :=
  (lex_10_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.pos 151), (Sat.Literal.neg 121)] :=
  (lex_10_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.neg 151), (Sat.Literal.neg 121), (Sat.Literal.pos 4278)] :=
  (lex_10_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4277), (Sat.Literal.pos 151), (Sat.Literal.pos 121), (Sat.Literal.pos 4278)] :=
  (lex_10_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4278) = lexBefore s permutation10 150 := by
  exact (positive_lex_of_descriptor s 4278 permutation10 151 (by rfl)).trans ((lex_skipped s permutation10 150 151 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation10 150) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation10 150 by rw [image10_eq]; rfl))

theorem lex_10_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4279) (Sat.Literal.pos 4278) (Sat.Literal.pos 150) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation10 150 (assignment s)
    (Sat.Literal.pos 4279) (Sat.Literal.pos 4278) (Sat.Literal.pos 150) (Sat.Literal.pos 105) (positive_of_descriptor s 4279 (.lex permutation10 150) (by rfl)) (lex_10_150_prefix s) (positive_select s 150) (lex_10_150_image s)

theorem lex_10_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.pos 150), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation10 150 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4278) (Sat.Literal.pos 150) (Sat.Literal.pos 105) (lex_10_150_prefix s) (positive_select s 150) (lex_10_150_image s)

theorem lex_10_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.pos 4278)] :=
  (lex_10_150_gate s).prop _ (List.Mem.head _)

theorem lex_10_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.neg 150), (Sat.Literal.pos 105)] :=
  (lex_10_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.pos 150), (Sat.Literal.neg 105)] :=
  (lex_10_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.neg 150), (Sat.Literal.neg 105), (Sat.Literal.pos 4279)] :=
  (lex_10_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4278), (Sat.Literal.pos 150), (Sat.Literal.pos 105), (Sat.Literal.pos 4279)] :=
  (lex_10_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4279) = lexBefore s permutation10 149 := by
  exact (positive_lex_of_descriptor s 4279 permutation10 150 (by rfl)).trans ((lex_skipped s permutation10 149 150 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation10 149) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation10 149 by rw [image10_eq]; rfl))

theorem lex_10_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4280) (Sat.Literal.pos 4279) (Sat.Literal.pos 149) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation10 149 (assignment s)
    (Sat.Literal.pos 4280) (Sat.Literal.pos 4279) (Sat.Literal.pos 149) (Sat.Literal.pos 89) (positive_of_descriptor s 4280 (.lex permutation10 149) (by rfl)) (lex_10_149_prefix s) (positive_select s 149) (lex_10_149_image s)

theorem lex_10_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.pos 149), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation10 149 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4279) (Sat.Literal.pos 149) (Sat.Literal.pos 89) (lex_10_149_prefix s) (positive_select s 149) (lex_10_149_image s)

theorem lex_10_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.pos 4279)] :=
  (lex_10_149_gate s).prop _ (List.Mem.head _)

theorem lex_10_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.neg 149), (Sat.Literal.pos 89)] :=
  (lex_10_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.pos 149), (Sat.Literal.neg 89)] :=
  (lex_10_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.neg 149), (Sat.Literal.neg 89), (Sat.Literal.pos 4280)] :=
  (lex_10_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4279), (Sat.Literal.pos 149), (Sat.Literal.pos 89), (Sat.Literal.pos 4280)] :=
  (lex_10_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4280) = lexBefore s permutation10 148 := by
  exact (positive_lex_of_descriptor s 4280 permutation10 149 (by rfl)).trans ((lex_skipped s permutation10 148 149 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation10 148) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation10 148 by rw [image10_eq]; rfl))

theorem lex_10_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4281) (Sat.Literal.pos 4280) (Sat.Literal.pos 148) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation10 148 (assignment s)
    (Sat.Literal.pos 4281) (Sat.Literal.pos 4280) (Sat.Literal.pos 148) (Sat.Literal.pos 73) (positive_of_descriptor s 4281 (.lex permutation10 148) (by rfl)) (lex_10_148_prefix s) (positive_select s 148) (lex_10_148_image s)

theorem lex_10_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.pos 148), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation10 148 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4280) (Sat.Literal.pos 148) (Sat.Literal.pos 73) (lex_10_148_prefix s) (positive_select s 148) (lex_10_148_image s)

theorem lex_10_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.pos 4280)] :=
  (lex_10_148_gate s).prop _ (List.Mem.head _)

theorem lex_10_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.neg 148), (Sat.Literal.pos 73)] :=
  (lex_10_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.pos 148), (Sat.Literal.neg 73)] :=
  (lex_10_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.neg 148), (Sat.Literal.neg 73), (Sat.Literal.pos 4281)] :=
  (lex_10_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4280), (Sat.Literal.pos 148), (Sat.Literal.pos 73), (Sat.Literal.pos 4281)] :=
  (lex_10_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4281) = lexBefore s permutation10 147 := by
  exact (positive_lex_of_descriptor s 4281 permutation10 148 (by rfl)).trans ((lex_skipped s permutation10 147 148 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation10 147) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation10 147 by rw [image10_eq]; rfl))

theorem lex_10_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4282) (Sat.Literal.pos 4281) (Sat.Literal.pos 147) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation10 147 (assignment s)
    (Sat.Literal.pos 4282) (Sat.Literal.pos 4281) (Sat.Literal.pos 147) (Sat.Literal.pos 57) (positive_of_descriptor s 4282 (.lex permutation10 147) (by rfl)) (lex_10_147_prefix s) (positive_select s 147) (lex_10_147_image s)

theorem lex_10_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.pos 147), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation10 147 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4281) (Sat.Literal.pos 147) (Sat.Literal.pos 57) (lex_10_147_prefix s) (positive_select s 147) (lex_10_147_image s)

theorem lex_10_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.pos 4281)] :=
  (lex_10_147_gate s).prop _ (List.Mem.head _)

theorem lex_10_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.neg 147), (Sat.Literal.pos 57)] :=
  (lex_10_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.pos 147), (Sat.Literal.neg 57)] :=
  (lex_10_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.neg 147), (Sat.Literal.neg 57), (Sat.Literal.pos 4282)] :=
  (lex_10_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4281), (Sat.Literal.pos 147), (Sat.Literal.pos 57), (Sat.Literal.pos 4282)] :=
  (lex_10_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4282) = lexBefore s permutation10 146 := by
  exact (positive_lex_of_descriptor s 4282 permutation10 147 (by rfl)).trans ((lex_skipped s permutation10 146 147 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation10 146) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation10 146 by rw [image10_eq]; rfl))

theorem lex_10_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4283) (Sat.Literal.pos 4282) (Sat.Literal.pos 146) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation10 146 (assignment s)
    (Sat.Literal.pos 4283) (Sat.Literal.pos 4282) (Sat.Literal.pos 146) (Sat.Literal.pos 41) (positive_of_descriptor s 4283 (.lex permutation10 146) (by rfl)) (lex_10_146_prefix s) (positive_select s 146) (lex_10_146_image s)

theorem lex_10_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.pos 146), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation10 146 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4282) (Sat.Literal.pos 146) (Sat.Literal.pos 41) (lex_10_146_prefix s) (positive_select s 146) (lex_10_146_image s)

theorem lex_10_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.pos 4282)] :=
  (lex_10_146_gate s).prop _ (List.Mem.head _)

theorem lex_10_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.neg 146), (Sat.Literal.pos 41)] :=
  (lex_10_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.pos 146), (Sat.Literal.neg 41)] :=
  (lex_10_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.neg 146), (Sat.Literal.neg 41), (Sat.Literal.pos 4283)] :=
  (lex_10_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4282), (Sat.Literal.pos 146), (Sat.Literal.pos 41), (Sat.Literal.pos 4283)] :=
  (lex_10_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4283) = lexBefore s permutation10 145 := by
  exact (positive_lex_of_descriptor s 4283 permutation10 146 (by rfl)).trans ((lex_skipped s permutation10 145 146 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation10 145) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation10 145 by rw [image10_eq]; rfl))

theorem lex_10_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4284) (Sat.Literal.pos 4283) (Sat.Literal.pos 145) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation10 145 (assignment s)
    (Sat.Literal.pos 4284) (Sat.Literal.pos 4283) (Sat.Literal.pos 145) (Sat.Literal.pos 25) (positive_of_descriptor s 4284 (.lex permutation10 145) (by rfl)) (lex_10_145_prefix s) (positive_select s 145) (lex_10_145_image s)

theorem lex_10_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.pos 145), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation10 145 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4283) (Sat.Literal.pos 145) (Sat.Literal.pos 25) (lex_10_145_prefix s) (positive_select s 145) (lex_10_145_image s)

theorem lex_10_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.pos 4283)] :=
  (lex_10_145_gate s).prop _ (List.Mem.head _)

theorem lex_10_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.neg 145), (Sat.Literal.pos 25)] :=
  (lex_10_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.pos 145), (Sat.Literal.neg 25)] :=
  (lex_10_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.neg 145), (Sat.Literal.neg 25), (Sat.Literal.pos 4284)] :=
  (lex_10_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4283), (Sat.Literal.pos 145), (Sat.Literal.pos 25), (Sat.Literal.pos 4284)] :=
  (lex_10_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4284) = lexBefore s permutation10 144 := by
  exact (positive_lex_of_descriptor s 4284 permutation10 145 (by rfl)).trans ((lex_skipped s permutation10 144 145 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation10 144) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation10 144 by rw [image10_eq]; rfl))

theorem lex_10_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4285) (Sat.Literal.pos 4284) (Sat.Literal.pos 144) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation10 144 (assignment s)
    (Sat.Literal.pos 4285) (Sat.Literal.pos 4284) (Sat.Literal.pos 144) (Sat.Literal.pos 9) (positive_of_descriptor s 4285 (.lex permutation10 144) (by rfl)) (lex_10_144_prefix s) (positive_select s 144) (lex_10_144_image s)

theorem lex_10_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.pos 144), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation10 144 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4284) (Sat.Literal.pos 144) (Sat.Literal.pos 9) (lex_10_144_prefix s) (positive_select s 144) (lex_10_144_image s)

theorem lex_10_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.pos 4284)] :=
  (lex_10_144_gate s).prop _ (List.Mem.head _)

theorem lex_10_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.neg 144), (Sat.Literal.pos 9)] :=
  (lex_10_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.pos 144), (Sat.Literal.neg 9)] :=
  (lex_10_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.neg 144), (Sat.Literal.neg 9), (Sat.Literal.pos 4285)] :=
  (lex_10_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4284), (Sat.Literal.pos 144), (Sat.Literal.pos 9), (Sat.Literal.pos 4285)] :=
  (lex_10_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4285) = lexBefore s permutation10 143 := by
  exact (positive_lex_of_descriptor s 4285 permutation10 144 (by rfl)).trans ((lex_skipped s permutation10 143 144 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation10 143) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation10 143 by rw [image10_eq]; rfl))

theorem lex_10_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4286) (Sat.Literal.pos 4285) (Sat.Literal.pos 143) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation10 143 (assignment s)
    (Sat.Literal.pos 4286) (Sat.Literal.pos 4285) (Sat.Literal.pos 143) (Sat.Literal.pos 248) (positive_of_descriptor s 4286 (.lex permutation10 143) (by rfl)) (lex_10_143_prefix s) (positive_select s 143) (lex_10_143_image s)

theorem lex_10_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.pos 143), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation10 143 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4285) (Sat.Literal.pos 143) (Sat.Literal.pos 248) (lex_10_143_prefix s) (positive_select s 143) (lex_10_143_image s)

theorem lex_10_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.pos 4285)] :=
  (lex_10_143_gate s).prop _ (List.Mem.head _)

theorem lex_10_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.neg 143), (Sat.Literal.pos 248)] :=
  (lex_10_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.pos 143), (Sat.Literal.neg 248)] :=
  (lex_10_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.neg 143), (Sat.Literal.neg 248), (Sat.Literal.pos 4286)] :=
  (lex_10_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4285), (Sat.Literal.pos 143), (Sat.Literal.pos 248), (Sat.Literal.pos 4286)] :=
  (lex_10_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4286) = lexBefore s permutation10 142 := by
  exact (positive_lex_of_descriptor s 4286 permutation10 143 (by rfl)).trans ((lex_skipped s permutation10 142 143 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation10 142) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation10 142 by rw [image10_eq]; rfl))

theorem lex_10_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4287) (Sat.Literal.pos 4286) (Sat.Literal.pos 142) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation10 142 (assignment s)
    (Sat.Literal.pos 4287) (Sat.Literal.pos 4286) (Sat.Literal.pos 142) (Sat.Literal.pos 232) (positive_of_descriptor s 4287 (.lex permutation10 142) (by rfl)) (lex_10_142_prefix s) (positive_select s 142) (lex_10_142_image s)

theorem lex_10_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.pos 142), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation10 142 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4286) (Sat.Literal.pos 142) (Sat.Literal.pos 232) (lex_10_142_prefix s) (positive_select s 142) (lex_10_142_image s)

theorem lex_10_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.pos 4286)] :=
  (lex_10_142_gate s).prop _ (List.Mem.head _)

theorem lex_10_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.neg 142), (Sat.Literal.pos 232)] :=
  (lex_10_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.pos 142), (Sat.Literal.neg 232)] :=
  (lex_10_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.neg 142), (Sat.Literal.neg 232), (Sat.Literal.pos 4287)] :=
  (lex_10_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4286), (Sat.Literal.pos 142), (Sat.Literal.pos 232), (Sat.Literal.pos 4287)] :=
  (lex_10_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4287) = lexBefore s permutation10 141 := by
  exact (positive_lex_of_descriptor s 4287 permutation10 142 (by rfl)).trans ((lex_skipped s permutation10 141 142 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation10 141) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation10 141 by rw [image10_eq]; rfl))

theorem lex_10_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4288) (Sat.Literal.pos 4287) (Sat.Literal.pos 141) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation10 141 (assignment s)
    (Sat.Literal.pos 4288) (Sat.Literal.pos 4287) (Sat.Literal.pos 141) (Sat.Literal.pos 216) (positive_of_descriptor s 4288 (.lex permutation10 141) (by rfl)) (lex_10_141_prefix s) (positive_select s 141) (lex_10_141_image s)

theorem lex_10_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.pos 141), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation10 141 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4287) (Sat.Literal.pos 141) (Sat.Literal.pos 216) (lex_10_141_prefix s) (positive_select s 141) (lex_10_141_image s)

theorem lex_10_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.pos 4287)] :=
  (lex_10_141_gate s).prop _ (List.Mem.head _)

theorem lex_10_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.neg 141), (Sat.Literal.pos 216)] :=
  (lex_10_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.pos 141), (Sat.Literal.neg 216)] :=
  (lex_10_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.neg 141), (Sat.Literal.neg 216), (Sat.Literal.pos 4288)] :=
  (lex_10_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4287), (Sat.Literal.pos 141), (Sat.Literal.pos 216), (Sat.Literal.pos 4288)] :=
  (lex_10_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4288) = lexBefore s permutation10 140 := by
  exact (positive_lex_of_descriptor s 4288 permutation10 141 (by rfl)).trans ((lex_skipped s permutation10 140 141 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation10 140) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation10 140 by rw [image10_eq]; rfl))

theorem lex_10_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4289) (Sat.Literal.pos 4288) (Sat.Literal.pos 140) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation10 140 (assignment s)
    (Sat.Literal.pos 4289) (Sat.Literal.pos 4288) (Sat.Literal.pos 140) (Sat.Literal.pos 200) (positive_of_descriptor s 4289 (.lex permutation10 140) (by rfl)) (lex_10_140_prefix s) (positive_select s 140) (lex_10_140_image s)

theorem lex_10_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.pos 140), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation10 140 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4288) (Sat.Literal.pos 140) (Sat.Literal.pos 200) (lex_10_140_prefix s) (positive_select s 140) (lex_10_140_image s)

theorem lex_10_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.pos 4288)] :=
  (lex_10_140_gate s).prop _ (List.Mem.head _)

theorem lex_10_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.neg 140), (Sat.Literal.pos 200)] :=
  (lex_10_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.pos 140), (Sat.Literal.neg 200)] :=
  (lex_10_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.neg 140), (Sat.Literal.neg 200), (Sat.Literal.pos 4289)] :=
  (lex_10_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4288), (Sat.Literal.pos 140), (Sat.Literal.pos 200), (Sat.Literal.pos 4289)] :=
  (lex_10_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4289) = lexBefore s permutation10 139 := by
  exact (positive_lex_of_descriptor s 4289 permutation10 140 (by rfl)).trans ((lex_skipped s permutation10 139 140 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation10 139) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation10 139 by rw [image10_eq]; rfl))

theorem lex_10_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4290) (Sat.Literal.pos 4289) (Sat.Literal.pos 139) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation10 139 (assignment s)
    (Sat.Literal.pos 4290) (Sat.Literal.pos 4289) (Sat.Literal.pos 139) (Sat.Literal.pos 184) (positive_of_descriptor s 4290 (.lex permutation10 139) (by rfl)) (lex_10_139_prefix s) (positive_select s 139) (lex_10_139_image s)

theorem lex_10_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.pos 139), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation10 139 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4289) (Sat.Literal.pos 139) (Sat.Literal.pos 184) (lex_10_139_prefix s) (positive_select s 139) (lex_10_139_image s)

theorem lex_10_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.pos 4289)] :=
  (lex_10_139_gate s).prop _ (List.Mem.head _)

theorem lex_10_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.neg 139), (Sat.Literal.pos 184)] :=
  (lex_10_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.pos 139), (Sat.Literal.neg 184)] :=
  (lex_10_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.neg 139), (Sat.Literal.neg 184), (Sat.Literal.pos 4290)] :=
  (lex_10_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4289), (Sat.Literal.pos 139), (Sat.Literal.pos 184), (Sat.Literal.pos 4290)] :=
  (lex_10_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4290) = lexBefore s permutation10 138 := by
  exact (positive_lex_of_descriptor s 4290 permutation10 139 (by rfl)).trans ((lex_skipped s permutation10 138 139 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation10 138) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation10 138 by rw [image10_eq]; rfl))

theorem lex_10_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4291) (Sat.Literal.pos 4290) (Sat.Literal.pos 138) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation10 138 (assignment s)
    (Sat.Literal.pos 4291) (Sat.Literal.pos 4290) (Sat.Literal.pos 138) (Sat.Literal.pos 168) (positive_of_descriptor s 4291 (.lex permutation10 138) (by rfl)) (lex_10_138_prefix s) (positive_select s 138) (lex_10_138_image s)

theorem lex_10_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.pos 138), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation10 138 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4290) (Sat.Literal.pos 138) (Sat.Literal.pos 168) (lex_10_138_prefix s) (positive_select s 138) (lex_10_138_image s)

theorem lex_10_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.pos 4290)] :=
  (lex_10_138_gate s).prop _ (List.Mem.head _)

theorem lex_10_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.neg 138), (Sat.Literal.pos 168)] :=
  (lex_10_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.pos 138), (Sat.Literal.neg 168)] :=
  (lex_10_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.neg 138), (Sat.Literal.neg 168), (Sat.Literal.pos 4291)] :=
  (lex_10_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4290), (Sat.Literal.pos 138), (Sat.Literal.pos 168), (Sat.Literal.pos 4291)] :=
  (lex_10_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4291) = lexBefore s permutation10 137 := by
  exact (positive_lex_of_descriptor s 4291 permutation10 138 (by rfl)).trans ((lex_skipped s permutation10 137 138 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation10 137) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation10 137 by rw [image10_eq]; rfl))

theorem lex_10_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4292) (Sat.Literal.pos 4291) (Sat.Literal.pos 137) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation10 137 (assignment s)
    (Sat.Literal.pos 4292) (Sat.Literal.pos 4291) (Sat.Literal.pos 137) (Sat.Literal.pos 152) (positive_of_descriptor s 4292 (.lex permutation10 137) (by rfl)) (lex_10_137_prefix s) (positive_select s 137) (lex_10_137_image s)

theorem lex_10_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.pos 137), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation10 137 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4291) (Sat.Literal.pos 137) (Sat.Literal.pos 152) (lex_10_137_prefix s) (positive_select s 137) (lex_10_137_image s)

theorem lex_10_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.pos 4291)] :=
  (lex_10_137_gate s).prop _ (List.Mem.head _)

theorem lex_10_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.neg 137), (Sat.Literal.pos 152)] :=
  (lex_10_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.pos 137), (Sat.Literal.neg 152)] :=
  (lex_10_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.neg 137), (Sat.Literal.neg 152), (Sat.Literal.pos 4292)] :=
  (lex_10_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4291), (Sat.Literal.pos 137), (Sat.Literal.pos 152), (Sat.Literal.pos 4292)] :=
  (lex_10_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4292) = lexBefore s permutation10 135 := by
  exact (positive_lex_of_descriptor s 4292 permutation10 137 (by rfl)).trans ((lex_skipped s permutation10 135 137 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 136 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation10 135) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation10 135 by rw [image10_eq]; rfl))

theorem lex_10_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4293) (Sat.Literal.pos 4292) (Sat.Literal.pos 135) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation10 135 (assignment s)
    (Sat.Literal.pos 4293) (Sat.Literal.pos 4292) (Sat.Literal.pos 135) (Sat.Literal.pos 120) (positive_of_descriptor s 4293 (.lex permutation10 135) (by rfl)) (lex_10_135_prefix s) (positive_select s 135) (lex_10_135_image s)

theorem lex_10_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.pos 135), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation10 135 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4292) (Sat.Literal.pos 135) (Sat.Literal.pos 120) (lex_10_135_prefix s) (positive_select s 135) (lex_10_135_image s)

theorem lex_10_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.pos 4292)] :=
  (lex_10_135_gate s).prop _ (List.Mem.head _)

theorem lex_10_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.neg 135), (Sat.Literal.pos 120)] :=
  (lex_10_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.pos 135), (Sat.Literal.neg 120)] :=
  (lex_10_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.neg 135), (Sat.Literal.neg 120), (Sat.Literal.pos 4293)] :=
  (lex_10_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4292), (Sat.Literal.pos 135), (Sat.Literal.pos 120), (Sat.Literal.pos 4293)] :=
  (lex_10_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4293) = lexBefore s permutation10 134 := by
  exact (positive_lex_of_descriptor s 4293 permutation10 135 (by rfl)).trans ((lex_skipped s permutation10 134 135 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation10 134) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation10 134 by rw [image10_eq]; rfl))

theorem lex_10_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4294) (Sat.Literal.pos 4293) (Sat.Literal.pos 134) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation10 134 (assignment s)
    (Sat.Literal.pos 4294) (Sat.Literal.pos 4293) (Sat.Literal.pos 134) (Sat.Literal.pos 104) (positive_of_descriptor s 4294 (.lex permutation10 134) (by rfl)) (lex_10_134_prefix s) (positive_select s 134) (lex_10_134_image s)

theorem lex_10_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.pos 134), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation10 134 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4293) (Sat.Literal.pos 134) (Sat.Literal.pos 104) (lex_10_134_prefix s) (positive_select s 134) (lex_10_134_image s)

theorem lex_10_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.pos 4293)] :=
  (lex_10_134_gate s).prop _ (List.Mem.head _)

theorem lex_10_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.neg 134), (Sat.Literal.pos 104)] :=
  (lex_10_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.pos 134), (Sat.Literal.neg 104)] :=
  (lex_10_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.neg 134), (Sat.Literal.neg 104), (Sat.Literal.pos 4294)] :=
  (lex_10_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4293), (Sat.Literal.pos 134), (Sat.Literal.pos 104), (Sat.Literal.pos 4294)] :=
  (lex_10_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4294) = lexBefore s permutation10 133 := by
  exact (positive_lex_of_descriptor s 4294 permutation10 134 (by rfl)).trans ((lex_skipped s permutation10 133 134 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation10 133) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation10 133 by rw [image10_eq]; rfl))

theorem lex_10_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4295) (Sat.Literal.pos 4294) (Sat.Literal.pos 133) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation10 133 (assignment s)
    (Sat.Literal.pos 4295) (Sat.Literal.pos 4294) (Sat.Literal.pos 133) (Sat.Literal.pos 88) (positive_of_descriptor s 4295 (.lex permutation10 133) (by rfl)) (lex_10_133_prefix s) (positive_select s 133) (lex_10_133_image s)

theorem lex_10_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.pos 133), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation10 133 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4294) (Sat.Literal.pos 133) (Sat.Literal.pos 88) (lex_10_133_prefix s) (positive_select s 133) (lex_10_133_image s)

theorem lex_10_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.pos 4294)] :=
  (lex_10_133_gate s).prop _ (List.Mem.head _)

theorem lex_10_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.neg 133), (Sat.Literal.pos 88)] :=
  (lex_10_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.pos 133), (Sat.Literal.neg 88)] :=
  (lex_10_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.neg 133), (Sat.Literal.neg 88), (Sat.Literal.pos 4295)] :=
  (lex_10_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4294), (Sat.Literal.pos 133), (Sat.Literal.pos 88), (Sat.Literal.pos 4295)] :=
  (lex_10_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4295) = lexBefore s permutation10 132 := by
  exact (positive_lex_of_descriptor s 4295 permutation10 133 (by rfl)).trans ((lex_skipped s permutation10 132 133 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation10 132) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation10 132 by rw [image10_eq]; rfl))

theorem lex_10_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4296) (Sat.Literal.pos 4295) (Sat.Literal.pos 132) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation10 132 (assignment s)
    (Sat.Literal.pos 4296) (Sat.Literal.pos 4295) (Sat.Literal.pos 132) (Sat.Literal.pos 72) (positive_of_descriptor s 4296 (.lex permutation10 132) (by rfl)) (lex_10_132_prefix s) (positive_select s 132) (lex_10_132_image s)

theorem lex_10_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.pos 132), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation10 132 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4295) (Sat.Literal.pos 132) (Sat.Literal.pos 72) (lex_10_132_prefix s) (positive_select s 132) (lex_10_132_image s)

theorem lex_10_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.pos 4295)] :=
  (lex_10_132_gate s).prop _ (List.Mem.head _)

theorem lex_10_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.neg 132), (Sat.Literal.pos 72)] :=
  (lex_10_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.pos 132), (Sat.Literal.neg 72)] :=
  (lex_10_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.neg 132), (Sat.Literal.neg 72), (Sat.Literal.pos 4296)] :=
  (lex_10_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4295), (Sat.Literal.pos 132), (Sat.Literal.pos 72), (Sat.Literal.pos 4296)] :=
  (lex_10_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4296) = lexBefore s permutation10 131 := by
  exact (positive_lex_of_descriptor s 4296 permutation10 132 (by rfl)).trans ((lex_skipped s permutation10 131 132 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation10 131) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation10 131 by rw [image10_eq]; rfl))

theorem lex_10_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4297) (Sat.Literal.pos 4296) (Sat.Literal.pos 131) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation10 131 (assignment s)
    (Sat.Literal.pos 4297) (Sat.Literal.pos 4296) (Sat.Literal.pos 131) (Sat.Literal.pos 56) (positive_of_descriptor s 4297 (.lex permutation10 131) (by rfl)) (lex_10_131_prefix s) (positive_select s 131) (lex_10_131_image s)

theorem lex_10_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.pos 131), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation10 131 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4296) (Sat.Literal.pos 131) (Sat.Literal.pos 56) (lex_10_131_prefix s) (positive_select s 131) (lex_10_131_image s)

theorem lex_10_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.pos 4296)] :=
  (lex_10_131_gate s).prop _ (List.Mem.head _)

theorem lex_10_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.neg 131), (Sat.Literal.pos 56)] :=
  (lex_10_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.pos 131), (Sat.Literal.neg 56)] :=
  (lex_10_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.neg 131), (Sat.Literal.neg 56), (Sat.Literal.pos 4297)] :=
  (lex_10_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4296), (Sat.Literal.pos 131), (Sat.Literal.pos 56), (Sat.Literal.pos 4297)] :=
  (lex_10_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4297) = lexBefore s permutation10 130 := by
  exact (positive_lex_of_descriptor s 4297 permutation10 131 (by rfl)).trans ((lex_skipped s permutation10 130 131 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation10 130) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation10 130 by rw [image10_eq]; rfl))

theorem lex_10_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4298) (Sat.Literal.pos 4297) (Sat.Literal.pos 130) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation10 130 (assignment s)
    (Sat.Literal.pos 4298) (Sat.Literal.pos 4297) (Sat.Literal.pos 130) (Sat.Literal.pos 40) (positive_of_descriptor s 4298 (.lex permutation10 130) (by rfl)) (lex_10_130_prefix s) (positive_select s 130) (lex_10_130_image s)

theorem lex_10_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.pos 130), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation10 130 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4297) (Sat.Literal.pos 130) (Sat.Literal.pos 40) (lex_10_130_prefix s) (positive_select s 130) (lex_10_130_image s)

theorem lex_10_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.pos 4297)] :=
  (lex_10_130_gate s).prop _ (List.Mem.head _)

theorem lex_10_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.neg 130), (Sat.Literal.pos 40)] :=
  (lex_10_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.pos 130), (Sat.Literal.neg 40)] :=
  (lex_10_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.neg 130), (Sat.Literal.neg 40), (Sat.Literal.pos 4298)] :=
  (lex_10_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4297), (Sat.Literal.pos 130), (Sat.Literal.pos 40), (Sat.Literal.pos 4298)] :=
  (lex_10_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4298) = lexBefore s permutation10 129 := by
  exact (positive_lex_of_descriptor s 4298 permutation10 130 (by rfl)).trans ((lex_skipped s permutation10 129 130 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation10 129) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation10 129 by rw [image10_eq]; rfl))

theorem lex_10_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4299) (Sat.Literal.pos 4298) (Sat.Literal.pos 129) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation10 129 (assignment s)
    (Sat.Literal.pos 4299) (Sat.Literal.pos 4298) (Sat.Literal.pos 129) (Sat.Literal.pos 24) (positive_of_descriptor s 4299 (.lex permutation10 129) (by rfl)) (lex_10_129_prefix s) (positive_select s 129) (lex_10_129_image s)

theorem lex_10_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.pos 129), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation10 129 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4298) (Sat.Literal.pos 129) (Sat.Literal.pos 24) (lex_10_129_prefix s) (positive_select s 129) (lex_10_129_image s)

theorem lex_10_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.pos 4298)] :=
  (lex_10_129_gate s).prop _ (List.Mem.head _)

theorem lex_10_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.neg 129), (Sat.Literal.pos 24)] :=
  (lex_10_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.pos 129), (Sat.Literal.neg 24)] :=
  (lex_10_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.neg 129), (Sat.Literal.neg 24), (Sat.Literal.pos 4299)] :=
  (lex_10_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4298), (Sat.Literal.pos 129), (Sat.Literal.pos 24), (Sat.Literal.pos 4299)] :=
  (lex_10_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4299) = lexBefore s permutation10 128 := by
  exact (positive_lex_of_descriptor s 4299 permutation10 129 (by rfl)).trans ((lex_skipped s permutation10 128 129 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation10 128) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation10 128 by rw [image10_eq]; rfl))

theorem lex_10_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4300) (Sat.Literal.pos 4299) (Sat.Literal.pos 128) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation10 128 (assignment s)
    (Sat.Literal.pos 4300) (Sat.Literal.pos 4299) (Sat.Literal.pos 128) (Sat.Literal.pos 8) (positive_of_descriptor s 4300 (.lex permutation10 128) (by rfl)) (lex_10_128_prefix s) (positive_select s 128) (lex_10_128_image s)

theorem lex_10_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.pos 128), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation10 128 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4299) (Sat.Literal.pos 128) (Sat.Literal.pos 8) (lex_10_128_prefix s) (positive_select s 128) (lex_10_128_image s)

theorem lex_10_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.pos 4299)] :=
  (lex_10_128_gate s).prop _ (List.Mem.head _)

theorem lex_10_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.neg 128), (Sat.Literal.pos 8)] :=
  (lex_10_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.pos 128), (Sat.Literal.neg 8)] :=
  (lex_10_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.neg 128), (Sat.Literal.neg 8), (Sat.Literal.pos 4300)] :=
  (lex_10_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4299), (Sat.Literal.pos 128), (Sat.Literal.pos 8), (Sat.Literal.pos 4300)] :=
  (lex_10_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4300) = lexBefore s permutation10 127 := by
  exact (positive_lex_of_descriptor s 4300 permutation10 128 (by rfl)).trans ((lex_skipped s permutation10 127 128 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation10 127) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation10 127 by rw [image10_eq]; rfl))

theorem lex_10_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4301) (Sat.Literal.pos 4300) (Sat.Literal.pos 127) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation10 127 (assignment s)
    (Sat.Literal.pos 4301) (Sat.Literal.pos 4300) (Sat.Literal.pos 127) (Sat.Literal.pos 247) (positive_of_descriptor s 4301 (.lex permutation10 127) (by rfl)) (lex_10_127_prefix s) (positive_select s 127) (lex_10_127_image s)

theorem lex_10_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.pos 127), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation10 127 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4300) (Sat.Literal.pos 127) (Sat.Literal.pos 247) (lex_10_127_prefix s) (positive_select s 127) (lex_10_127_image s)

theorem lex_10_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.pos 4300)] :=
  (lex_10_127_gate s).prop _ (List.Mem.head _)

theorem lex_10_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.neg 127), (Sat.Literal.pos 247)] :=
  (lex_10_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.pos 127), (Sat.Literal.neg 247)] :=
  (lex_10_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.neg 127), (Sat.Literal.neg 247), (Sat.Literal.pos 4301)] :=
  (lex_10_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4300), (Sat.Literal.pos 127), (Sat.Literal.pos 247), (Sat.Literal.pos 4301)] :=
  (lex_10_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4301) = lexBefore s permutation10 126 := by
  exact (positive_lex_of_descriptor s 4301 permutation10 127 (by rfl)).trans ((lex_skipped s permutation10 126 127 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation10 126) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation10 126 by rw [image10_eq]; rfl))

theorem lex_10_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4302) (Sat.Literal.pos 4301) (Sat.Literal.pos 126) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation10 126 (assignment s)
    (Sat.Literal.pos 4302) (Sat.Literal.pos 4301) (Sat.Literal.pos 126) (Sat.Literal.pos 231) (positive_of_descriptor s 4302 (.lex permutation10 126) (by rfl)) (lex_10_126_prefix s) (positive_select s 126) (lex_10_126_image s)

theorem lex_10_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.pos 126), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation10 126 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4301) (Sat.Literal.pos 126) (Sat.Literal.pos 231) (lex_10_126_prefix s) (positive_select s 126) (lex_10_126_image s)

theorem lex_10_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.pos 4301)] :=
  (lex_10_126_gate s).prop _ (List.Mem.head _)

theorem lex_10_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.neg 126), (Sat.Literal.pos 231)] :=
  (lex_10_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.pos 126), (Sat.Literal.neg 231)] :=
  (lex_10_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.neg 126), (Sat.Literal.neg 231), (Sat.Literal.pos 4302)] :=
  (lex_10_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4301), (Sat.Literal.pos 126), (Sat.Literal.pos 231), (Sat.Literal.pos 4302)] :=
  (lex_10_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4302) = lexBefore s permutation10 125 := by
  exact (positive_lex_of_descriptor s 4302 permutation10 126 (by rfl)).trans ((lex_skipped s permutation10 125 126 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation10 125) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation10 125 by rw [image10_eq]; rfl))

theorem lex_10_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4303) (Sat.Literal.pos 4302) (Sat.Literal.pos 125) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation10 125 (assignment s)
    (Sat.Literal.pos 4303) (Sat.Literal.pos 4302) (Sat.Literal.pos 125) (Sat.Literal.pos 215) (positive_of_descriptor s 4303 (.lex permutation10 125) (by rfl)) (lex_10_125_prefix s) (positive_select s 125) (lex_10_125_image s)

theorem lex_10_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.pos 125), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation10 125 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4302) (Sat.Literal.pos 125) (Sat.Literal.pos 215) (lex_10_125_prefix s) (positive_select s 125) (lex_10_125_image s)

theorem lex_10_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.pos 4302)] :=
  (lex_10_125_gate s).prop _ (List.Mem.head _)

theorem lex_10_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.neg 125), (Sat.Literal.pos 215)] :=
  (lex_10_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.pos 125), (Sat.Literal.neg 215)] :=
  (lex_10_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.neg 125), (Sat.Literal.neg 215), (Sat.Literal.pos 4303)] :=
  (lex_10_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4302), (Sat.Literal.pos 125), (Sat.Literal.pos 215), (Sat.Literal.pos 4303)] :=
  (lex_10_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4303) = lexBefore s permutation10 124 := by
  exact (positive_lex_of_descriptor s 4303 permutation10 125 (by rfl)).trans ((lex_skipped s permutation10 124 125 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation10 124) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation10 124 by rw [image10_eq]; rfl))

theorem lex_10_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4304) (Sat.Literal.pos 4303) (Sat.Literal.pos 124) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation10 124 (assignment s)
    (Sat.Literal.pos 4304) (Sat.Literal.pos 4303) (Sat.Literal.pos 124) (Sat.Literal.pos 199) (positive_of_descriptor s 4304 (.lex permutation10 124) (by rfl)) (lex_10_124_prefix s) (positive_select s 124) (lex_10_124_image s)

theorem lex_10_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.pos 124), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation10 124 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4303) (Sat.Literal.pos 124) (Sat.Literal.pos 199) (lex_10_124_prefix s) (positive_select s 124) (lex_10_124_image s)

theorem lex_10_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.pos 4303)] :=
  (lex_10_124_gate s).prop _ (List.Mem.head _)

theorem lex_10_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.neg 124), (Sat.Literal.pos 199)] :=
  (lex_10_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.pos 124), (Sat.Literal.neg 199)] :=
  (lex_10_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.neg 124), (Sat.Literal.neg 199), (Sat.Literal.pos 4304)] :=
  (lex_10_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4303), (Sat.Literal.pos 124), (Sat.Literal.pos 199), (Sat.Literal.pos 4304)] :=
  (lex_10_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4304) = lexBefore s permutation10 123 := by
  exact (positive_lex_of_descriptor s 4304 permutation10 124 (by rfl)).trans ((lex_skipped s permutation10 123 124 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation10 123) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation10 123 by rw [image10_eq]; rfl))

theorem lex_10_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4305) (Sat.Literal.pos 4304) (Sat.Literal.pos 123) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation10 123 (assignment s)
    (Sat.Literal.pos 4305) (Sat.Literal.pos 4304) (Sat.Literal.pos 123) (Sat.Literal.pos 183) (positive_of_descriptor s 4305 (.lex permutation10 123) (by rfl)) (lex_10_123_prefix s) (positive_select s 123) (lex_10_123_image s)

theorem lex_10_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.pos 123), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation10 123 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4304) (Sat.Literal.pos 123) (Sat.Literal.pos 183) (lex_10_123_prefix s) (positive_select s 123) (lex_10_123_image s)

theorem lex_10_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.pos 4304)] :=
  (lex_10_123_gate s).prop _ (List.Mem.head _)

theorem lex_10_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.neg 123), (Sat.Literal.pos 183)] :=
  (lex_10_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.pos 123), (Sat.Literal.neg 183)] :=
  (lex_10_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.neg 123), (Sat.Literal.neg 183), (Sat.Literal.pos 4305)] :=
  (lex_10_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4304), (Sat.Literal.pos 123), (Sat.Literal.pos 183), (Sat.Literal.pos 4305)] :=
  (lex_10_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4305) = lexBefore s permutation10 122 := by
  exact (positive_lex_of_descriptor s 4305 permutation10 123 (by rfl)).trans ((lex_skipped s permutation10 122 123 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation10 122) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation10 122 by rw [image10_eq]; rfl))

theorem lex_10_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4306) (Sat.Literal.pos 4305) (Sat.Literal.pos 122) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation10 122 (assignment s)
    (Sat.Literal.pos 4306) (Sat.Literal.pos 4305) (Sat.Literal.pos 122) (Sat.Literal.pos 167) (positive_of_descriptor s 4306 (.lex permutation10 122) (by rfl)) (lex_10_122_prefix s) (positive_select s 122) (lex_10_122_image s)

theorem lex_10_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.pos 122), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation10 122 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4305) (Sat.Literal.pos 122) (Sat.Literal.pos 167) (lex_10_122_prefix s) (positive_select s 122) (lex_10_122_image s)

theorem lex_10_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.pos 4305)] :=
  (lex_10_122_gate s).prop _ (List.Mem.head _)

theorem lex_10_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.neg 122), (Sat.Literal.pos 167)] :=
  (lex_10_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.pos 122), (Sat.Literal.neg 167)] :=
  (lex_10_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.neg 122), (Sat.Literal.neg 167), (Sat.Literal.pos 4306)] :=
  (lex_10_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4305), (Sat.Literal.pos 122), (Sat.Literal.pos 167), (Sat.Literal.pos 4306)] :=
  (lex_10_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4306) = lexBefore s permutation10 121 := by
  exact (positive_lex_of_descriptor s 4306 permutation10 122 (by rfl)).trans ((lex_skipped s permutation10 121 122 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation10 121) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation10 121 by rw [image10_eq]; rfl))

theorem lex_10_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4307) (Sat.Literal.pos 4306) (Sat.Literal.pos 121) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation10 121 (assignment s)
    (Sat.Literal.pos 4307) (Sat.Literal.pos 4306) (Sat.Literal.pos 121) (Sat.Literal.pos 151) (positive_of_descriptor s 4307 (.lex permutation10 121) (by rfl)) (lex_10_121_prefix s) (positive_select s 121) (lex_10_121_image s)

theorem lex_10_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.pos 121), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation10 121 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4306) (Sat.Literal.pos 121) (Sat.Literal.pos 151) (lex_10_121_prefix s) (positive_select s 121) (lex_10_121_image s)

theorem lex_10_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.pos 4306)] :=
  (lex_10_121_gate s).prop _ (List.Mem.head _)

theorem lex_10_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.neg 121), (Sat.Literal.pos 151)] :=
  (lex_10_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.pos 121), (Sat.Literal.neg 151)] :=
  (lex_10_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.neg 121), (Sat.Literal.neg 151), (Sat.Literal.pos 4307)] :=
  (lex_10_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4306), (Sat.Literal.pos 121), (Sat.Literal.pos 151), (Sat.Literal.pos 4307)] :=
  (lex_10_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4307) = lexBefore s permutation10 120 := by
  exact (positive_lex_of_descriptor s 4307 permutation10 121 (by rfl)).trans ((lex_skipped s permutation10 120 121 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation10 120) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation10 120 by rw [image10_eq]; rfl))

theorem lex_10_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4308) (Sat.Literal.pos 4307) (Sat.Literal.pos 120) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation10 120 (assignment s)
    (Sat.Literal.pos 4308) (Sat.Literal.pos 4307) (Sat.Literal.pos 120) (Sat.Literal.pos 135) (positive_of_descriptor s 4308 (.lex permutation10 120) (by rfl)) (lex_10_120_prefix s) (positive_select s 120) (lex_10_120_image s)

theorem lex_10_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.pos 120), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation10 120 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4307) (Sat.Literal.pos 120) (Sat.Literal.pos 135) (lex_10_120_prefix s) (positive_select s 120) (lex_10_120_image s)

theorem lex_10_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.pos 4307)] :=
  (lex_10_120_gate s).prop _ (List.Mem.head _)

theorem lex_10_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.neg 120), (Sat.Literal.pos 135)] :=
  (lex_10_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.pos 120), (Sat.Literal.neg 135)] :=
  (lex_10_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.neg 120), (Sat.Literal.neg 135), (Sat.Literal.pos 4308)] :=
  (lex_10_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4307), (Sat.Literal.pos 120), (Sat.Literal.pos 135), (Sat.Literal.pos 4308)] :=
  (lex_10_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4308) = lexBefore s permutation10 118 := by
  exact (positive_lex_of_descriptor s 4308 permutation10 120 (by rfl)).trans ((lex_skipped s permutation10 118 120 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 119 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation10 118) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation10 118 by rw [image10_eq]; rfl))

theorem lex_10_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4309) (Sat.Literal.pos 4308) (Sat.Literal.pos 118) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation10 118 (assignment s)
    (Sat.Literal.pos 4309) (Sat.Literal.pos 4308) (Sat.Literal.pos 118) (Sat.Literal.pos 103) (positive_of_descriptor s 4309 (.lex permutation10 118) (by rfl)) (lex_10_118_prefix s) (positive_select s 118) (lex_10_118_image s)

theorem lex_10_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.pos 118), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation10 118 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4308) (Sat.Literal.pos 118) (Sat.Literal.pos 103) (lex_10_118_prefix s) (positive_select s 118) (lex_10_118_image s)

theorem lex_10_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.pos 4308)] :=
  (lex_10_118_gate s).prop _ (List.Mem.head _)

theorem lex_10_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.neg 118), (Sat.Literal.pos 103)] :=
  (lex_10_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.pos 118), (Sat.Literal.neg 103)] :=
  (lex_10_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.neg 118), (Sat.Literal.neg 103), (Sat.Literal.pos 4309)] :=
  (lex_10_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4308), (Sat.Literal.pos 118), (Sat.Literal.pos 103), (Sat.Literal.pos 4309)] :=
  (lex_10_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4309) = lexBefore s permutation10 117 := by
  exact (positive_lex_of_descriptor s 4309 permutation10 118 (by rfl)).trans ((lex_skipped s permutation10 117 118 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation10 117) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation10 117 by rw [image10_eq]; rfl))

theorem lex_10_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4310) (Sat.Literal.pos 4309) (Sat.Literal.pos 117) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation10 117 (assignment s)
    (Sat.Literal.pos 4310) (Sat.Literal.pos 4309) (Sat.Literal.pos 117) (Sat.Literal.pos 87) (positive_of_descriptor s 4310 (.lex permutation10 117) (by rfl)) (lex_10_117_prefix s) (positive_select s 117) (lex_10_117_image s)

theorem lex_10_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.pos 117), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation10 117 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4309) (Sat.Literal.pos 117) (Sat.Literal.pos 87) (lex_10_117_prefix s) (positive_select s 117) (lex_10_117_image s)

theorem lex_10_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.pos 4309)] :=
  (lex_10_117_gate s).prop _ (List.Mem.head _)

theorem lex_10_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.neg 117), (Sat.Literal.pos 87)] :=
  (lex_10_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.pos 117), (Sat.Literal.neg 87)] :=
  (lex_10_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.neg 117), (Sat.Literal.neg 87), (Sat.Literal.pos 4310)] :=
  (lex_10_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4309), (Sat.Literal.pos 117), (Sat.Literal.pos 87), (Sat.Literal.pos 4310)] :=
  (lex_10_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4310) = lexBefore s permutation10 116 := by
  exact (positive_lex_of_descriptor s 4310 permutation10 117 (by rfl)).trans ((lex_skipped s permutation10 116 117 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation10 116) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation10 116 by rw [image10_eq]; rfl))

theorem lex_10_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4311) (Sat.Literal.pos 4310) (Sat.Literal.pos 116) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation10 116 (assignment s)
    (Sat.Literal.pos 4311) (Sat.Literal.pos 4310) (Sat.Literal.pos 116) (Sat.Literal.pos 71) (positive_of_descriptor s 4311 (.lex permutation10 116) (by rfl)) (lex_10_116_prefix s) (positive_select s 116) (lex_10_116_image s)

theorem lex_10_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.pos 116), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation10 116 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4310) (Sat.Literal.pos 116) (Sat.Literal.pos 71) (lex_10_116_prefix s) (positive_select s 116) (lex_10_116_image s)

theorem lex_10_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.pos 4310)] :=
  (lex_10_116_gate s).prop _ (List.Mem.head _)

theorem lex_10_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.neg 116), (Sat.Literal.pos 71)] :=
  (lex_10_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.pos 116), (Sat.Literal.neg 71)] :=
  (lex_10_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.neg 116), (Sat.Literal.neg 71), (Sat.Literal.pos 4311)] :=
  (lex_10_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4310), (Sat.Literal.pos 116), (Sat.Literal.pos 71), (Sat.Literal.pos 4311)] :=
  (lex_10_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4311) = lexBefore s permutation10 115 := by
  exact (positive_lex_of_descriptor s 4311 permutation10 116 (by rfl)).trans ((lex_skipped s permutation10 115 116 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation10 115) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation10 115 by rw [image10_eq]; rfl))

theorem lex_10_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4312) (Sat.Literal.pos 4311) (Sat.Literal.pos 115) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation10 115 (assignment s)
    (Sat.Literal.pos 4312) (Sat.Literal.pos 4311) (Sat.Literal.pos 115) (Sat.Literal.pos 55) (positive_of_descriptor s 4312 (.lex permutation10 115) (by rfl)) (lex_10_115_prefix s) (positive_select s 115) (lex_10_115_image s)

theorem lex_10_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.pos 115), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation10 115 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4311) (Sat.Literal.pos 115) (Sat.Literal.pos 55) (lex_10_115_prefix s) (positive_select s 115) (lex_10_115_image s)

theorem lex_10_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.pos 4311)] :=
  (lex_10_115_gate s).prop _ (List.Mem.head _)

theorem lex_10_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.neg 115), (Sat.Literal.pos 55)] :=
  (lex_10_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.pos 115), (Sat.Literal.neg 55)] :=
  (lex_10_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.neg 115), (Sat.Literal.neg 55), (Sat.Literal.pos 4312)] :=
  (lex_10_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4311), (Sat.Literal.pos 115), (Sat.Literal.pos 55), (Sat.Literal.pos 4312)] :=
  (lex_10_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4312) = lexBefore s permutation10 114 := by
  exact (positive_lex_of_descriptor s 4312 permutation10 115 (by rfl)).trans ((lex_skipped s permutation10 114 115 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation10 114) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation10 114 by rw [image10_eq]; rfl))

theorem lex_10_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4313) (Sat.Literal.pos 4312) (Sat.Literal.pos 114) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation10 114 (assignment s)
    (Sat.Literal.pos 4313) (Sat.Literal.pos 4312) (Sat.Literal.pos 114) (Sat.Literal.pos 39) (positive_of_descriptor s 4313 (.lex permutation10 114) (by rfl)) (lex_10_114_prefix s) (positive_select s 114) (lex_10_114_image s)

theorem lex_10_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.pos 114), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation10 114 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4312) (Sat.Literal.pos 114) (Sat.Literal.pos 39) (lex_10_114_prefix s) (positive_select s 114) (lex_10_114_image s)

theorem lex_10_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.pos 4312)] :=
  (lex_10_114_gate s).prop _ (List.Mem.head _)

theorem lex_10_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.neg 114), (Sat.Literal.pos 39)] :=
  (lex_10_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.pos 114), (Sat.Literal.neg 39)] :=
  (lex_10_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.neg 114), (Sat.Literal.neg 39), (Sat.Literal.pos 4313)] :=
  (lex_10_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4312), (Sat.Literal.pos 114), (Sat.Literal.pos 39), (Sat.Literal.pos 4313)] :=
  (lex_10_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4313) = lexBefore s permutation10 113 := by
  exact (positive_lex_of_descriptor s 4313 permutation10 114 (by rfl)).trans ((lex_skipped s permutation10 113 114 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation10 113) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation10 113 by rw [image10_eq]; rfl))

theorem lex_10_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4314) (Sat.Literal.pos 4313) (Sat.Literal.pos 113) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation10 113 (assignment s)
    (Sat.Literal.pos 4314) (Sat.Literal.pos 4313) (Sat.Literal.pos 113) (Sat.Literal.pos 23) (positive_of_descriptor s 4314 (.lex permutation10 113) (by rfl)) (lex_10_113_prefix s) (positive_select s 113) (lex_10_113_image s)

theorem lex_10_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.pos 113), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation10 113 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4313) (Sat.Literal.pos 113) (Sat.Literal.pos 23) (lex_10_113_prefix s) (positive_select s 113) (lex_10_113_image s)

theorem lex_10_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.pos 4313)] :=
  (lex_10_113_gate s).prop _ (List.Mem.head _)

theorem lex_10_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.neg 113), (Sat.Literal.pos 23)] :=
  (lex_10_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.pos 113), (Sat.Literal.neg 23)] :=
  (lex_10_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.neg 113), (Sat.Literal.neg 23), (Sat.Literal.pos 4314)] :=
  (lex_10_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4313), (Sat.Literal.pos 113), (Sat.Literal.pos 23), (Sat.Literal.pos 4314)] :=
  (lex_10_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4314) = lexBefore s permutation10 112 := by
  exact (positive_lex_of_descriptor s 4314 permutation10 113 (by rfl)).trans ((lex_skipped s permutation10 112 113 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation10 112) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation10 112 by rw [image10_eq]; rfl))

theorem lex_10_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4315) (Sat.Literal.pos 4314) (Sat.Literal.pos 112) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation10 112 (assignment s)
    (Sat.Literal.pos 4315) (Sat.Literal.pos 4314) (Sat.Literal.pos 112) (Sat.Literal.pos 7) (positive_of_descriptor s 4315 (.lex permutation10 112) (by rfl)) (lex_10_112_prefix s) (positive_select s 112) (lex_10_112_image s)

theorem lex_10_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.pos 112), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation10 112 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4314) (Sat.Literal.pos 112) (Sat.Literal.pos 7) (lex_10_112_prefix s) (positive_select s 112) (lex_10_112_image s)

theorem lex_10_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.pos 4314)] :=
  (lex_10_112_gate s).prop _ (List.Mem.head _)

theorem lex_10_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.neg 112), (Sat.Literal.pos 7)] :=
  (lex_10_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.pos 112), (Sat.Literal.neg 7)] :=
  (lex_10_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.neg 112), (Sat.Literal.neg 7), (Sat.Literal.pos 4315)] :=
  (lex_10_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4314), (Sat.Literal.pos 112), (Sat.Literal.pos 7), (Sat.Literal.pos 4315)] :=
  (lex_10_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4315) = lexBefore s permutation10 111 := by
  exact (positive_lex_of_descriptor s 4315 permutation10 112 (by rfl)).trans ((lex_skipped s permutation10 111 112 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation10 111) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation10 111 by rw [image10_eq]; rfl))

theorem lex_10_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4316) (Sat.Literal.pos 4315) (Sat.Literal.pos 111) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation10 111 (assignment s)
    (Sat.Literal.pos 4316) (Sat.Literal.pos 4315) (Sat.Literal.pos 111) (Sat.Literal.pos 246) (positive_of_descriptor s 4316 (.lex permutation10 111) (by rfl)) (lex_10_111_prefix s) (positive_select s 111) (lex_10_111_image s)

theorem lex_10_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.pos 111), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation10 111 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4315) (Sat.Literal.pos 111) (Sat.Literal.pos 246) (lex_10_111_prefix s) (positive_select s 111) (lex_10_111_image s)

theorem lex_10_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.pos 4315)] :=
  (lex_10_111_gate s).prop _ (List.Mem.head _)

theorem lex_10_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.neg 111), (Sat.Literal.pos 246)] :=
  (lex_10_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.pos 111), (Sat.Literal.neg 246)] :=
  (lex_10_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.neg 111), (Sat.Literal.neg 246), (Sat.Literal.pos 4316)] :=
  (lex_10_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4315), (Sat.Literal.pos 111), (Sat.Literal.pos 246), (Sat.Literal.pos 4316)] :=
  (lex_10_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4316) = lexBefore s permutation10 110 := by
  exact (positive_lex_of_descriptor s 4316 permutation10 111 (by rfl)).trans ((lex_skipped s permutation10 110 111 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation10 110) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation10 110 by rw [image10_eq]; rfl))

theorem lex_10_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4317) (Sat.Literal.pos 4316) (Sat.Literal.pos 110) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation10 110 (assignment s)
    (Sat.Literal.pos 4317) (Sat.Literal.pos 4316) (Sat.Literal.pos 110) (Sat.Literal.pos 230) (positive_of_descriptor s 4317 (.lex permutation10 110) (by rfl)) (lex_10_110_prefix s) (positive_select s 110) (lex_10_110_image s)

theorem lex_10_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.pos 110), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation10 110 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4316) (Sat.Literal.pos 110) (Sat.Literal.pos 230) (lex_10_110_prefix s) (positive_select s 110) (lex_10_110_image s)

theorem lex_10_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.pos 4316)] :=
  (lex_10_110_gate s).prop _ (List.Mem.head _)

theorem lex_10_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.neg 110), (Sat.Literal.pos 230)] :=
  (lex_10_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.pos 110), (Sat.Literal.neg 230)] :=
  (lex_10_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.neg 110), (Sat.Literal.neg 230), (Sat.Literal.pos 4317)] :=
  (lex_10_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4316), (Sat.Literal.pos 110), (Sat.Literal.pos 230), (Sat.Literal.pos 4317)] :=
  (lex_10_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4317) = lexBefore s permutation10 109 := by
  exact (positive_lex_of_descriptor s 4317 permutation10 110 (by rfl)).trans ((lex_skipped s permutation10 109 110 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation10 109) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation10 109 by rw [image10_eq]; rfl))

theorem lex_10_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4318) (Sat.Literal.pos 4317) (Sat.Literal.pos 109) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation10 109 (assignment s)
    (Sat.Literal.pos 4318) (Sat.Literal.pos 4317) (Sat.Literal.pos 109) (Sat.Literal.pos 214) (positive_of_descriptor s 4318 (.lex permutation10 109) (by rfl)) (lex_10_109_prefix s) (positive_select s 109) (lex_10_109_image s)

theorem lex_10_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.pos 109), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation10 109 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4317) (Sat.Literal.pos 109) (Sat.Literal.pos 214) (lex_10_109_prefix s) (positive_select s 109) (lex_10_109_image s)

theorem lex_10_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.pos 4317)] :=
  (lex_10_109_gate s).prop _ (List.Mem.head _)

theorem lex_10_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.neg 109), (Sat.Literal.pos 214)] :=
  (lex_10_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.pos 109), (Sat.Literal.neg 214)] :=
  (lex_10_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.neg 109), (Sat.Literal.neg 214), (Sat.Literal.pos 4318)] :=
  (lex_10_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4317), (Sat.Literal.pos 109), (Sat.Literal.pos 214), (Sat.Literal.pos 4318)] :=
  (lex_10_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4318) = lexBefore s permutation10 108 := by
  exact (positive_lex_of_descriptor s 4318 permutation10 109 (by rfl)).trans ((lex_skipped s permutation10 108 109 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation10 108) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation10 108 by rw [image10_eq]; rfl))

theorem lex_10_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4319) (Sat.Literal.pos 4318) (Sat.Literal.pos 108) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation10 108 (assignment s)
    (Sat.Literal.pos 4319) (Sat.Literal.pos 4318) (Sat.Literal.pos 108) (Sat.Literal.pos 198) (positive_of_descriptor s 4319 (.lex permutation10 108) (by rfl)) (lex_10_108_prefix s) (positive_select s 108) (lex_10_108_image s)

theorem lex_10_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.pos 108), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation10 108 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4318) (Sat.Literal.pos 108) (Sat.Literal.pos 198) (lex_10_108_prefix s) (positive_select s 108) (lex_10_108_image s)

theorem lex_10_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.pos 4318)] :=
  (lex_10_108_gate s).prop _ (List.Mem.head _)

theorem lex_10_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.neg 108), (Sat.Literal.pos 198)] :=
  (lex_10_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.pos 108), (Sat.Literal.neg 198)] :=
  (lex_10_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.neg 108), (Sat.Literal.neg 198), (Sat.Literal.pos 4319)] :=
  (lex_10_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4318), (Sat.Literal.pos 108), (Sat.Literal.pos 198), (Sat.Literal.pos 4319)] :=
  (lex_10_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4319) = lexBefore s permutation10 107 := by
  exact (positive_lex_of_descriptor s 4319 permutation10 108 (by rfl)).trans ((lex_skipped s permutation10 107 108 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation10 107) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation10 107 by rw [image10_eq]; rfl))

theorem lex_10_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4320) (Sat.Literal.pos 4319) (Sat.Literal.pos 107) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation10 107 (assignment s)
    (Sat.Literal.pos 4320) (Sat.Literal.pos 4319) (Sat.Literal.pos 107) (Sat.Literal.pos 182) (positive_of_descriptor s 4320 (.lex permutation10 107) (by rfl)) (lex_10_107_prefix s) (positive_select s 107) (lex_10_107_image s)

theorem lex_10_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.pos 107), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation10 107 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4319) (Sat.Literal.pos 107) (Sat.Literal.pos 182) (lex_10_107_prefix s) (positive_select s 107) (lex_10_107_image s)

theorem lex_10_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.pos 4319)] :=
  (lex_10_107_gate s).prop _ (List.Mem.head _)

theorem lex_10_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.neg 107), (Sat.Literal.pos 182)] :=
  (lex_10_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.pos 107), (Sat.Literal.neg 182)] :=
  (lex_10_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.neg 107), (Sat.Literal.neg 182), (Sat.Literal.pos 4320)] :=
  (lex_10_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4319), (Sat.Literal.pos 107), (Sat.Literal.pos 182), (Sat.Literal.pos 4320)] :=
  (lex_10_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4320) = lexBefore s permutation10 106 := by
  exact (positive_lex_of_descriptor s 4320 permutation10 107 (by rfl)).trans ((lex_skipped s permutation10 106 107 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation10 106) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation10 106 by rw [image10_eq]; rfl))

theorem lex_10_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4321) (Sat.Literal.pos 4320) (Sat.Literal.pos 106) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation10 106 (assignment s)
    (Sat.Literal.pos 4321) (Sat.Literal.pos 4320) (Sat.Literal.pos 106) (Sat.Literal.pos 166) (positive_of_descriptor s 4321 (.lex permutation10 106) (by rfl)) (lex_10_106_prefix s) (positive_select s 106) (lex_10_106_image s)

theorem lex_10_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.pos 106), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation10 106 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4320) (Sat.Literal.pos 106) (Sat.Literal.pos 166) (lex_10_106_prefix s) (positive_select s 106) (lex_10_106_image s)

theorem lex_10_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.pos 4320)] :=
  (lex_10_106_gate s).prop _ (List.Mem.head _)

theorem lex_10_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.neg 106), (Sat.Literal.pos 166)] :=
  (lex_10_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.pos 106), (Sat.Literal.neg 166)] :=
  (lex_10_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.neg 106), (Sat.Literal.neg 166), (Sat.Literal.pos 4321)] :=
  (lex_10_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4320), (Sat.Literal.pos 106), (Sat.Literal.pos 166), (Sat.Literal.pos 4321)] :=
  (lex_10_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4321) = lexBefore s permutation10 105 := by
  exact (positive_lex_of_descriptor s 4321 permutation10 106 (by rfl)).trans ((lex_skipped s permutation10 105 106 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation10 105) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation10 105 by rw [image10_eq]; rfl))

theorem lex_10_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4322) (Sat.Literal.pos 4321) (Sat.Literal.pos 105) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation10 105 (assignment s)
    (Sat.Literal.pos 4322) (Sat.Literal.pos 4321) (Sat.Literal.pos 105) (Sat.Literal.pos 150) (positive_of_descriptor s 4322 (.lex permutation10 105) (by rfl)) (lex_10_105_prefix s) (positive_select s 105) (lex_10_105_image s)

theorem lex_10_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.pos 105), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation10 105 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4321) (Sat.Literal.pos 105) (Sat.Literal.pos 150) (lex_10_105_prefix s) (positive_select s 105) (lex_10_105_image s)

theorem lex_10_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.pos 4321)] :=
  (lex_10_105_gate s).prop _ (List.Mem.head _)

theorem lex_10_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.neg 105), (Sat.Literal.pos 150)] :=
  (lex_10_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.pos 105), (Sat.Literal.neg 150)] :=
  (lex_10_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.neg 105), (Sat.Literal.neg 150), (Sat.Literal.pos 4322)] :=
  (lex_10_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4321), (Sat.Literal.pos 105), (Sat.Literal.pos 150), (Sat.Literal.pos 4322)] :=
  (lex_10_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4322) = lexBefore s permutation10 104 := by
  exact (positive_lex_of_descriptor s 4322 permutation10 105 (by rfl)).trans ((lex_skipped s permutation10 104 105 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation10 104) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation10 104 by rw [image10_eq]; rfl))

theorem lex_10_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4323) (Sat.Literal.pos 4322) (Sat.Literal.pos 104) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation10 104 (assignment s)
    (Sat.Literal.pos 4323) (Sat.Literal.pos 4322) (Sat.Literal.pos 104) (Sat.Literal.pos 134) (positive_of_descriptor s 4323 (.lex permutation10 104) (by rfl)) (lex_10_104_prefix s) (positive_select s 104) (lex_10_104_image s)

theorem lex_10_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.pos 104), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation10 104 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4322) (Sat.Literal.pos 104) (Sat.Literal.pos 134) (lex_10_104_prefix s) (positive_select s 104) (lex_10_104_image s)

theorem lex_10_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.pos 4322)] :=
  (lex_10_104_gate s).prop _ (List.Mem.head _)

theorem lex_10_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.neg 104), (Sat.Literal.pos 134)] :=
  (lex_10_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.pos 104), (Sat.Literal.neg 134)] :=
  (lex_10_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.neg 104), (Sat.Literal.neg 134), (Sat.Literal.pos 4323)] :=
  (lex_10_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4322), (Sat.Literal.pos 104), (Sat.Literal.pos 134), (Sat.Literal.pos 4323)] :=
  (lex_10_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4323) = lexBefore s permutation10 103 := by
  exact (positive_lex_of_descriptor s 4323 permutation10 104 (by rfl)).trans ((lex_skipped s permutation10 103 104 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation10 103) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation10 103 by rw [image10_eq]; rfl))

theorem lex_10_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4324) (Sat.Literal.pos 4323) (Sat.Literal.pos 103) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation10 103 (assignment s)
    (Sat.Literal.pos 4324) (Sat.Literal.pos 4323) (Sat.Literal.pos 103) (Sat.Literal.pos 118) (positive_of_descriptor s 4324 (.lex permutation10 103) (by rfl)) (lex_10_103_prefix s) (positive_select s 103) (lex_10_103_image s)

theorem lex_10_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.pos 103), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation10 103 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4323) (Sat.Literal.pos 103) (Sat.Literal.pos 118) (lex_10_103_prefix s) (positive_select s 103) (lex_10_103_image s)

theorem lex_10_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.pos 4323)] :=
  (lex_10_103_gate s).prop _ (List.Mem.head _)

theorem lex_10_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.neg 103), (Sat.Literal.pos 118)] :=
  (lex_10_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.pos 103), (Sat.Literal.neg 118)] :=
  (lex_10_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.neg 103), (Sat.Literal.neg 118), (Sat.Literal.pos 4324)] :=
  (lex_10_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4323), (Sat.Literal.pos 103), (Sat.Literal.pos 118), (Sat.Literal.pos 4324)] :=
  (lex_10_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_10_208_gate

end Crown.CertificateData
