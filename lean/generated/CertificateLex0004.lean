import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_3_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2924) = lexBefore s permutation3 215 := by
  exact (positive_lex_of_descriptor s 2924 permutation3 232 (by rfl)).trans ((lex_skipped s permutation3 215 232 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 216 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation3 215) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation3 215 by rw [image3_eq]; rfl))

theorem lex_3_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2925) (Sat.Literal.pos 2924) (Sat.Literal.pos 215) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation3 215 (assignment s)
    (Sat.Literal.pos 2925) (Sat.Literal.pos 2924) (Sat.Literal.pos 215) (Sat.Literal.pos 207) (positive_of_descriptor s 2925 (.lex permutation3 215) (by rfl)) (lex_3_215_prefix s) (positive_select s 215) (lex_3_215_image s)

theorem lex_3_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.pos 215), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation3 215 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2924) (Sat.Literal.pos 215) (Sat.Literal.pos 207) (lex_3_215_prefix s) (positive_select s 215) (lex_3_215_image s)

theorem lex_3_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.pos 2924)] :=
  (lex_3_215_gate s).prop _ (List.Mem.head _)

theorem lex_3_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.neg 215), (Sat.Literal.pos 207)] :=
  (lex_3_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.pos 215), (Sat.Literal.neg 207)] :=
  (lex_3_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.neg 215), (Sat.Literal.neg 207), (Sat.Literal.pos 2925)] :=
  (lex_3_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.pos 215), (Sat.Literal.pos 207), (Sat.Literal.pos 2925)] :=
  (lex_3_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2925) = lexBefore s permutation3 214 := by
  exact (positive_lex_of_descriptor s 2925 permutation3 215 (by rfl)).trans ((lex_skipped s permutation3 214 215 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation3 214) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation3 214 by rw [image3_eq]; rfl))

theorem lex_3_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2926) (Sat.Literal.pos 2925) (Sat.Literal.pos 214) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation3 214 (assignment s)
    (Sat.Literal.pos 2926) (Sat.Literal.pos 2925) (Sat.Literal.pos 214) (Sat.Literal.pos 206) (positive_of_descriptor s 2926 (.lex permutation3 214) (by rfl)) (lex_3_214_prefix s) (positive_select s 214) (lex_3_214_image s)

theorem lex_3_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.pos 214), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation3 214 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2925) (Sat.Literal.pos 214) (Sat.Literal.pos 206) (lex_3_214_prefix s) (positive_select s 214) (lex_3_214_image s)

theorem lex_3_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.pos 2925)] :=
  (lex_3_214_gate s).prop _ (List.Mem.head _)

theorem lex_3_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.neg 214), (Sat.Literal.pos 206)] :=
  (lex_3_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.pos 214), (Sat.Literal.neg 206)] :=
  (lex_3_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.neg 214), (Sat.Literal.neg 206), (Sat.Literal.pos 2926)] :=
  (lex_3_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2925), (Sat.Literal.pos 214), (Sat.Literal.pos 206), (Sat.Literal.pos 2926)] :=
  (lex_3_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2926) = lexBefore s permutation3 213 := by
  exact (positive_lex_of_descriptor s 2926 permutation3 214 (by rfl)).trans ((lex_skipped s permutation3 213 214 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation3 213) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation3 213 by rw [image3_eq]; rfl))

theorem lex_3_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2927) (Sat.Literal.pos 2926) (Sat.Literal.pos 213) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation3 213 (assignment s)
    (Sat.Literal.pos 2927) (Sat.Literal.pos 2926) (Sat.Literal.pos 213) (Sat.Literal.pos 205) (positive_of_descriptor s 2927 (.lex permutation3 213) (by rfl)) (lex_3_213_prefix s) (positive_select s 213) (lex_3_213_image s)

theorem lex_3_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.pos 213), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation3 213 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2926) (Sat.Literal.pos 213) (Sat.Literal.pos 205) (lex_3_213_prefix s) (positive_select s 213) (lex_3_213_image s)

theorem lex_3_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.pos 2926)] :=
  (lex_3_213_gate s).prop _ (List.Mem.head _)

theorem lex_3_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.neg 213), (Sat.Literal.pos 205)] :=
  (lex_3_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.pos 213), (Sat.Literal.neg 205)] :=
  (lex_3_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.neg 213), (Sat.Literal.neg 205), (Sat.Literal.pos 2927)] :=
  (lex_3_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2926), (Sat.Literal.pos 213), (Sat.Literal.pos 205), (Sat.Literal.pos 2927)] :=
  (lex_3_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2927) = lexBefore s permutation3 212 := by
  exact (positive_lex_of_descriptor s 2927 permutation3 213 (by rfl)).trans ((lex_skipped s permutation3 212 213 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation3 212) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation3 212 by rw [image3_eq]; rfl))

theorem lex_3_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2928) (Sat.Literal.pos 2927) (Sat.Literal.pos 212) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation3 212 (assignment s)
    (Sat.Literal.pos 2928) (Sat.Literal.pos 2927) (Sat.Literal.pos 212) (Sat.Literal.pos 204) (positive_of_descriptor s 2928 (.lex permutation3 212) (by rfl)) (lex_3_212_prefix s) (positive_select s 212) (lex_3_212_image s)

theorem lex_3_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.pos 212), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation3 212 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2927) (Sat.Literal.pos 212) (Sat.Literal.pos 204) (lex_3_212_prefix s) (positive_select s 212) (lex_3_212_image s)

theorem lex_3_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.pos 2927)] :=
  (lex_3_212_gate s).prop _ (List.Mem.head _)

theorem lex_3_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.neg 212), (Sat.Literal.pos 204)] :=
  (lex_3_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.pos 212), (Sat.Literal.neg 204)] :=
  (lex_3_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.neg 212), (Sat.Literal.neg 204), (Sat.Literal.pos 2928)] :=
  (lex_3_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2927), (Sat.Literal.pos 212), (Sat.Literal.pos 204), (Sat.Literal.pos 2928)] :=
  (lex_3_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2928) = lexBefore s permutation3 211 := by
  exact (positive_lex_of_descriptor s 2928 permutation3 212 (by rfl)).trans ((lex_skipped s permutation3 211 212 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation3 211) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation3 211 by rw [image3_eq]; rfl))

theorem lex_3_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2929) (Sat.Literal.pos 2928) (Sat.Literal.pos 211) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation3 211 (assignment s)
    (Sat.Literal.pos 2929) (Sat.Literal.pos 2928) (Sat.Literal.pos 211) (Sat.Literal.pos 203) (positive_of_descriptor s 2929 (.lex permutation3 211) (by rfl)) (lex_3_211_prefix s) (positive_select s 211) (lex_3_211_image s)

theorem lex_3_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.pos 211), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation3 211 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2928) (Sat.Literal.pos 211) (Sat.Literal.pos 203) (lex_3_211_prefix s) (positive_select s 211) (lex_3_211_image s)

theorem lex_3_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.pos 2928)] :=
  (lex_3_211_gate s).prop _ (List.Mem.head _)

theorem lex_3_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.neg 211), (Sat.Literal.pos 203)] :=
  (lex_3_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.pos 211), (Sat.Literal.neg 203)] :=
  (lex_3_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.neg 211), (Sat.Literal.neg 203), (Sat.Literal.pos 2929)] :=
  (lex_3_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2928), (Sat.Literal.pos 211), (Sat.Literal.pos 203), (Sat.Literal.pos 2929)] :=
  (lex_3_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2929) = lexBefore s permutation3 210 := by
  exact (positive_lex_of_descriptor s 2929 permutation3 211 (by rfl)).trans ((lex_skipped s permutation3 210 211 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation3 210) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation3 210 by rw [image3_eq]; rfl))

theorem lex_3_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2930) (Sat.Literal.pos 2929) (Sat.Literal.pos 210) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation3 210 (assignment s)
    (Sat.Literal.pos 2930) (Sat.Literal.pos 2929) (Sat.Literal.pos 210) (Sat.Literal.pos 202) (positive_of_descriptor s 2930 (.lex permutation3 210) (by rfl)) (lex_3_210_prefix s) (positive_select s 210) (lex_3_210_image s)

theorem lex_3_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.pos 210), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation3 210 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2929) (Sat.Literal.pos 210) (Sat.Literal.pos 202) (lex_3_210_prefix s) (positive_select s 210) (lex_3_210_image s)

theorem lex_3_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.pos 2929)] :=
  (lex_3_210_gate s).prop _ (List.Mem.head _)

theorem lex_3_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.neg 210), (Sat.Literal.pos 202)] :=
  (lex_3_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.pos 210), (Sat.Literal.neg 202)] :=
  (lex_3_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.neg 210), (Sat.Literal.neg 202), (Sat.Literal.pos 2930)] :=
  (lex_3_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2929), (Sat.Literal.pos 210), (Sat.Literal.pos 202), (Sat.Literal.pos 2930)] :=
  (lex_3_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2930) = lexBefore s permutation3 209 := by
  exact (positive_lex_of_descriptor s 2930 permutation3 210 (by rfl)).trans ((lex_skipped s permutation3 209 210 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation3 209) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation3 209 by rw [image3_eq]; rfl))

theorem lex_3_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2931) (Sat.Literal.pos 2930) (Sat.Literal.pos 209) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation3 209 (assignment s)
    (Sat.Literal.pos 2931) (Sat.Literal.pos 2930) (Sat.Literal.pos 209) (Sat.Literal.pos 201) (positive_of_descriptor s 2931 (.lex permutation3 209) (by rfl)) (lex_3_209_prefix s) (positive_select s 209) (lex_3_209_image s)

theorem lex_3_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.pos 209), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation3 209 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2930) (Sat.Literal.pos 209) (Sat.Literal.pos 201) (lex_3_209_prefix s) (positive_select s 209) (lex_3_209_image s)

theorem lex_3_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.pos 2930)] :=
  (lex_3_209_gate s).prop _ (List.Mem.head _)

theorem lex_3_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.neg 209), (Sat.Literal.pos 201)] :=
  (lex_3_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.pos 209), (Sat.Literal.neg 201)] :=
  (lex_3_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.neg 209), (Sat.Literal.neg 201), (Sat.Literal.pos 2931)] :=
  (lex_3_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2930), (Sat.Literal.pos 209), (Sat.Literal.pos 201), (Sat.Literal.pos 2931)] :=
  (lex_3_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2931) = lexBefore s permutation3 208 := by
  exact (positive_lex_of_descriptor s 2931 permutation3 209 (by rfl)).trans ((lex_skipped s permutation3 208 209 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation3 208) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation3 208 by rw [image3_eq]; rfl))

theorem lex_3_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2932) (Sat.Literal.pos 2931) (Sat.Literal.pos 208) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation3 208 (assignment s)
    (Sat.Literal.pos 2932) (Sat.Literal.pos 2931) (Sat.Literal.pos 208) (Sat.Literal.pos 200) (positive_of_descriptor s 2932 (.lex permutation3 208) (by rfl)) (lex_3_208_prefix s) (positive_select s 208) (lex_3_208_image s)

theorem lex_3_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.pos 208), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation3 208 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2931) (Sat.Literal.pos 208) (Sat.Literal.pos 200) (lex_3_208_prefix s) (positive_select s 208) (lex_3_208_image s)

theorem lex_3_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.pos 2931)] :=
  (lex_3_208_gate s).prop _ (List.Mem.head _)

theorem lex_3_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.neg 208), (Sat.Literal.pos 200)] :=
  (lex_3_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.pos 208), (Sat.Literal.neg 200)] :=
  (lex_3_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.neg 208), (Sat.Literal.neg 200), (Sat.Literal.pos 2932)] :=
  (lex_3_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2931), (Sat.Literal.pos 208), (Sat.Literal.pos 200), (Sat.Literal.pos 2932)] :=
  (lex_3_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2932) = lexBefore s permutation3 207 := by
  exact (positive_lex_of_descriptor s 2932 permutation3 208 (by rfl)).trans ((lex_skipped s permutation3 207 208 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation3 207) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation3 207 by rw [image3_eq]; rfl))

theorem lex_3_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2933) (Sat.Literal.pos 2932) (Sat.Literal.pos 207) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation3 207 (assignment s)
    (Sat.Literal.pos 2933) (Sat.Literal.pos 2932) (Sat.Literal.pos 207) (Sat.Literal.pos 215) (positive_of_descriptor s 2933 (.lex permutation3 207) (by rfl)) (lex_3_207_prefix s) (positive_select s 207) (lex_3_207_image s)

theorem lex_3_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.pos 207), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation3 207 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2932) (Sat.Literal.pos 207) (Sat.Literal.pos 215) (lex_3_207_prefix s) (positive_select s 207) (lex_3_207_image s)

theorem lex_3_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.pos 2932)] :=
  (lex_3_207_gate s).prop _ (List.Mem.head _)

theorem lex_3_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.neg 207), (Sat.Literal.pos 215)] :=
  (lex_3_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.pos 207), (Sat.Literal.neg 215)] :=
  (lex_3_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.neg 207), (Sat.Literal.neg 215), (Sat.Literal.pos 2933)] :=
  (lex_3_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2932), (Sat.Literal.pos 207), (Sat.Literal.pos 215), (Sat.Literal.pos 2933)] :=
  (lex_3_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2933) = lexBefore s permutation3 206 := by
  exact (positive_lex_of_descriptor s 2933 permutation3 207 (by rfl)).trans ((lex_skipped s permutation3 206 207 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation3 206) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation3 206 by rw [image3_eq]; rfl))

theorem lex_3_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2934) (Sat.Literal.pos 2933) (Sat.Literal.pos 206) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation3 206 (assignment s)
    (Sat.Literal.pos 2934) (Sat.Literal.pos 2933) (Sat.Literal.pos 206) (Sat.Literal.pos 214) (positive_of_descriptor s 2934 (.lex permutation3 206) (by rfl)) (lex_3_206_prefix s) (positive_select s 206) (lex_3_206_image s)

theorem lex_3_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.pos 206), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation3 206 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2933) (Sat.Literal.pos 206) (Sat.Literal.pos 214) (lex_3_206_prefix s) (positive_select s 206) (lex_3_206_image s)

theorem lex_3_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.pos 2933)] :=
  (lex_3_206_gate s).prop _ (List.Mem.head _)

theorem lex_3_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.neg 206), (Sat.Literal.pos 214)] :=
  (lex_3_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.pos 206), (Sat.Literal.neg 214)] :=
  (lex_3_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.neg 206), (Sat.Literal.neg 214), (Sat.Literal.pos 2934)] :=
  (lex_3_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2933), (Sat.Literal.pos 206), (Sat.Literal.pos 214), (Sat.Literal.pos 2934)] :=
  (lex_3_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2934) = lexBefore s permutation3 205 := by
  exact (positive_lex_of_descriptor s 2934 permutation3 206 (by rfl)).trans ((lex_skipped s permutation3 205 206 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation3 205) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation3 205 by rw [image3_eq]; rfl))

theorem lex_3_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2935) (Sat.Literal.pos 2934) (Sat.Literal.pos 205) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation3 205 (assignment s)
    (Sat.Literal.pos 2935) (Sat.Literal.pos 2934) (Sat.Literal.pos 205) (Sat.Literal.pos 213) (positive_of_descriptor s 2935 (.lex permutation3 205) (by rfl)) (lex_3_205_prefix s) (positive_select s 205) (lex_3_205_image s)

theorem lex_3_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.pos 205), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation3 205 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2934) (Sat.Literal.pos 205) (Sat.Literal.pos 213) (lex_3_205_prefix s) (positive_select s 205) (lex_3_205_image s)

theorem lex_3_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.pos 2934)] :=
  (lex_3_205_gate s).prop _ (List.Mem.head _)

theorem lex_3_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.neg 205), (Sat.Literal.pos 213)] :=
  (lex_3_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.pos 205), (Sat.Literal.neg 213)] :=
  (lex_3_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.neg 205), (Sat.Literal.neg 213), (Sat.Literal.pos 2935)] :=
  (lex_3_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2934), (Sat.Literal.pos 205), (Sat.Literal.pos 213), (Sat.Literal.pos 2935)] :=
  (lex_3_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2935) = lexBefore s permutation3 204 := by
  exact (positive_lex_of_descriptor s 2935 permutation3 205 (by rfl)).trans ((lex_skipped s permutation3 204 205 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation3 204) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation3 204 by rw [image3_eq]; rfl))

theorem lex_3_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2936) (Sat.Literal.pos 2935) (Sat.Literal.pos 204) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation3 204 (assignment s)
    (Sat.Literal.pos 2936) (Sat.Literal.pos 2935) (Sat.Literal.pos 204) (Sat.Literal.pos 212) (positive_of_descriptor s 2936 (.lex permutation3 204) (by rfl)) (lex_3_204_prefix s) (positive_select s 204) (lex_3_204_image s)

theorem lex_3_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.pos 204), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation3 204 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2935) (Sat.Literal.pos 204) (Sat.Literal.pos 212) (lex_3_204_prefix s) (positive_select s 204) (lex_3_204_image s)

theorem lex_3_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.pos 2935)] :=
  (lex_3_204_gate s).prop _ (List.Mem.head _)

theorem lex_3_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.neg 204), (Sat.Literal.pos 212)] :=
  (lex_3_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.pos 204), (Sat.Literal.neg 212)] :=
  (lex_3_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.neg 204), (Sat.Literal.neg 212), (Sat.Literal.pos 2936)] :=
  (lex_3_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2935), (Sat.Literal.pos 204), (Sat.Literal.pos 212), (Sat.Literal.pos 2936)] :=
  (lex_3_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2936) = lexBefore s permutation3 203 := by
  exact (positive_lex_of_descriptor s 2936 permutation3 204 (by rfl)).trans ((lex_skipped s permutation3 203 204 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation3 203) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation3 203 by rw [image3_eq]; rfl))

theorem lex_3_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2937) (Sat.Literal.pos 2936) (Sat.Literal.pos 203) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation3 203 (assignment s)
    (Sat.Literal.pos 2937) (Sat.Literal.pos 2936) (Sat.Literal.pos 203) (Sat.Literal.pos 211) (positive_of_descriptor s 2937 (.lex permutation3 203) (by rfl)) (lex_3_203_prefix s) (positive_select s 203) (lex_3_203_image s)

theorem lex_3_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.pos 203), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation3 203 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2936) (Sat.Literal.pos 203) (Sat.Literal.pos 211) (lex_3_203_prefix s) (positive_select s 203) (lex_3_203_image s)

theorem lex_3_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.pos 2936)] :=
  (lex_3_203_gate s).prop _ (List.Mem.head _)

theorem lex_3_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.neg 203), (Sat.Literal.pos 211)] :=
  (lex_3_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.pos 203), (Sat.Literal.neg 211)] :=
  (lex_3_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.neg 203), (Sat.Literal.neg 211), (Sat.Literal.pos 2937)] :=
  (lex_3_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2936), (Sat.Literal.pos 203), (Sat.Literal.pos 211), (Sat.Literal.pos 2937)] :=
  (lex_3_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2937) = lexBefore s permutation3 202 := by
  exact (positive_lex_of_descriptor s 2937 permutation3 203 (by rfl)).trans ((lex_skipped s permutation3 202 203 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation3 202) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation3 202 by rw [image3_eq]; rfl))

theorem lex_3_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2938) (Sat.Literal.pos 2937) (Sat.Literal.pos 202) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation3 202 (assignment s)
    (Sat.Literal.pos 2938) (Sat.Literal.pos 2937) (Sat.Literal.pos 202) (Sat.Literal.pos 210) (positive_of_descriptor s 2938 (.lex permutation3 202) (by rfl)) (lex_3_202_prefix s) (positive_select s 202) (lex_3_202_image s)

theorem lex_3_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.pos 202), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation3 202 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2937) (Sat.Literal.pos 202) (Sat.Literal.pos 210) (lex_3_202_prefix s) (positive_select s 202) (lex_3_202_image s)

theorem lex_3_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.pos 2937)] :=
  (lex_3_202_gate s).prop _ (List.Mem.head _)

theorem lex_3_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.neg 202), (Sat.Literal.pos 210)] :=
  (lex_3_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.pos 202), (Sat.Literal.neg 210)] :=
  (lex_3_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.neg 202), (Sat.Literal.neg 210), (Sat.Literal.pos 2938)] :=
  (lex_3_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2937), (Sat.Literal.pos 202), (Sat.Literal.pos 210), (Sat.Literal.pos 2938)] :=
  (lex_3_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2938) = lexBefore s permutation3 201 := by
  exact (positive_lex_of_descriptor s 2938 permutation3 202 (by rfl)).trans ((lex_skipped s permutation3 201 202 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation3 201) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation3 201 by rw [image3_eq]; rfl))

theorem lex_3_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2939) (Sat.Literal.pos 2938) (Sat.Literal.pos 201) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation3 201 (assignment s)
    (Sat.Literal.pos 2939) (Sat.Literal.pos 2938) (Sat.Literal.pos 201) (Sat.Literal.pos 209) (positive_of_descriptor s 2939 (.lex permutation3 201) (by rfl)) (lex_3_201_prefix s) (positive_select s 201) (lex_3_201_image s)

theorem lex_3_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.pos 201), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation3 201 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2938) (Sat.Literal.pos 201) (Sat.Literal.pos 209) (lex_3_201_prefix s) (positive_select s 201) (lex_3_201_image s)

theorem lex_3_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.pos 2938)] :=
  (lex_3_201_gate s).prop _ (List.Mem.head _)

theorem lex_3_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.neg 201), (Sat.Literal.pos 209)] :=
  (lex_3_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.pos 201), (Sat.Literal.neg 209)] :=
  (lex_3_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.neg 201), (Sat.Literal.neg 209), (Sat.Literal.pos 2939)] :=
  (lex_3_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2938), (Sat.Literal.pos 201), (Sat.Literal.pos 209), (Sat.Literal.pos 2939)] :=
  (lex_3_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2939) = lexBefore s permutation3 200 := by
  exact (positive_lex_of_descriptor s 2939 permutation3 201 (by rfl)).trans ((lex_skipped s permutation3 200 201 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation3 200) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation3 200 by rw [image3_eq]; rfl))

theorem lex_3_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2940) (Sat.Literal.pos 2939) (Sat.Literal.pos 200) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation3 200 (assignment s)
    (Sat.Literal.pos 2940) (Sat.Literal.pos 2939) (Sat.Literal.pos 200) (Sat.Literal.pos 208) (positive_of_descriptor s 2940 (.lex permutation3 200) (by rfl)) (lex_3_200_prefix s) (positive_select s 200) (lex_3_200_image s)

theorem lex_3_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.pos 200), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation3 200 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2939) (Sat.Literal.pos 200) (Sat.Literal.pos 208) (lex_3_200_prefix s) (positive_select s 200) (lex_3_200_image s)

theorem lex_3_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.pos 2939)] :=
  (lex_3_200_gate s).prop _ (List.Mem.head _)

theorem lex_3_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.neg 200), (Sat.Literal.pos 208)] :=
  (lex_3_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.pos 200), (Sat.Literal.neg 208)] :=
  (lex_3_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.neg 200), (Sat.Literal.neg 208), (Sat.Literal.pos 2940)] :=
  (lex_3_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2939), (Sat.Literal.pos 200), (Sat.Literal.pos 208), (Sat.Literal.pos 2940)] :=
  (lex_3_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2940) = lexBefore s permutation3 183 := by
  exact (positive_lex_of_descriptor s 2940 permutation3 200 (by rfl)).trans ((lex_skipped s permutation3 183 200 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 184 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation3 183) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation3 183 by rw [image3_eq]; rfl))

theorem lex_3_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2941) (Sat.Literal.pos 2940) (Sat.Literal.pos 183) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation3 183 (assignment s)
    (Sat.Literal.pos 2941) (Sat.Literal.pos 2940) (Sat.Literal.pos 183) (Sat.Literal.pos 175) (positive_of_descriptor s 2941 (.lex permutation3 183) (by rfl)) (lex_3_183_prefix s) (positive_select s 183) (lex_3_183_image s)

theorem lex_3_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.pos 183), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation3 183 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2940) (Sat.Literal.pos 183) (Sat.Literal.pos 175) (lex_3_183_prefix s) (positive_select s 183) (lex_3_183_image s)

theorem lex_3_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.pos 2940)] :=
  (lex_3_183_gate s).prop _ (List.Mem.head _)

theorem lex_3_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.neg 183), (Sat.Literal.pos 175)] :=
  (lex_3_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.pos 183), (Sat.Literal.neg 175)] :=
  (lex_3_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.neg 183), (Sat.Literal.neg 175), (Sat.Literal.pos 2941)] :=
  (lex_3_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2940), (Sat.Literal.pos 183), (Sat.Literal.pos 175), (Sat.Literal.pos 2941)] :=
  (lex_3_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2941) = lexBefore s permutation3 182 := by
  exact (positive_lex_of_descriptor s 2941 permutation3 183 (by rfl)).trans ((lex_skipped s permutation3 182 183 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation3 182) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation3 182 by rw [image3_eq]; rfl))

theorem lex_3_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2942) (Sat.Literal.pos 2941) (Sat.Literal.pos 182) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation3 182 (assignment s)
    (Sat.Literal.pos 2942) (Sat.Literal.pos 2941) (Sat.Literal.pos 182) (Sat.Literal.pos 174) (positive_of_descriptor s 2942 (.lex permutation3 182) (by rfl)) (lex_3_182_prefix s) (positive_select s 182) (lex_3_182_image s)

theorem lex_3_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.pos 182), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation3 182 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2941) (Sat.Literal.pos 182) (Sat.Literal.pos 174) (lex_3_182_prefix s) (positive_select s 182) (lex_3_182_image s)

theorem lex_3_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.pos 2941)] :=
  (lex_3_182_gate s).prop _ (List.Mem.head _)

theorem lex_3_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.neg 182), (Sat.Literal.pos 174)] :=
  (lex_3_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.pos 182), (Sat.Literal.neg 174)] :=
  (lex_3_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.neg 182), (Sat.Literal.neg 174), (Sat.Literal.pos 2942)] :=
  (lex_3_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2941), (Sat.Literal.pos 182), (Sat.Literal.pos 174), (Sat.Literal.pos 2942)] :=
  (lex_3_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2942) = lexBefore s permutation3 181 := by
  exact (positive_lex_of_descriptor s 2942 permutation3 182 (by rfl)).trans ((lex_skipped s permutation3 181 182 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation3 181) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation3 181 by rw [image3_eq]; rfl))

theorem lex_3_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2943) (Sat.Literal.pos 2942) (Sat.Literal.pos 181) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation3 181 (assignment s)
    (Sat.Literal.pos 2943) (Sat.Literal.pos 2942) (Sat.Literal.pos 181) (Sat.Literal.pos 173) (positive_of_descriptor s 2943 (.lex permutation3 181) (by rfl)) (lex_3_181_prefix s) (positive_select s 181) (lex_3_181_image s)

theorem lex_3_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.pos 181), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation3 181 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2942) (Sat.Literal.pos 181) (Sat.Literal.pos 173) (lex_3_181_prefix s) (positive_select s 181) (lex_3_181_image s)

theorem lex_3_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.pos 2942)] :=
  (lex_3_181_gate s).prop _ (List.Mem.head _)

theorem lex_3_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.neg 181), (Sat.Literal.pos 173)] :=
  (lex_3_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.pos 181), (Sat.Literal.neg 173)] :=
  (lex_3_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.neg 181), (Sat.Literal.neg 173), (Sat.Literal.pos 2943)] :=
  (lex_3_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2942), (Sat.Literal.pos 181), (Sat.Literal.pos 173), (Sat.Literal.pos 2943)] :=
  (lex_3_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2943) = lexBefore s permutation3 180 := by
  exact (positive_lex_of_descriptor s 2943 permutation3 181 (by rfl)).trans ((lex_skipped s permutation3 180 181 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation3 180) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation3 180 by rw [image3_eq]; rfl))

theorem lex_3_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2944) (Sat.Literal.pos 2943) (Sat.Literal.pos 180) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation3 180 (assignment s)
    (Sat.Literal.pos 2944) (Sat.Literal.pos 2943) (Sat.Literal.pos 180) (Sat.Literal.pos 172) (positive_of_descriptor s 2944 (.lex permutation3 180) (by rfl)) (lex_3_180_prefix s) (positive_select s 180) (lex_3_180_image s)

theorem lex_3_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.pos 180), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation3 180 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2943) (Sat.Literal.pos 180) (Sat.Literal.pos 172) (lex_3_180_prefix s) (positive_select s 180) (lex_3_180_image s)

theorem lex_3_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.pos 2943)] :=
  (lex_3_180_gate s).prop _ (List.Mem.head _)

theorem lex_3_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.neg 180), (Sat.Literal.pos 172)] :=
  (lex_3_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.pos 180), (Sat.Literal.neg 172)] :=
  (lex_3_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.neg 180), (Sat.Literal.neg 172), (Sat.Literal.pos 2944)] :=
  (lex_3_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2943), (Sat.Literal.pos 180), (Sat.Literal.pos 172), (Sat.Literal.pos 2944)] :=
  (lex_3_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2944) = lexBefore s permutation3 179 := by
  exact (positive_lex_of_descriptor s 2944 permutation3 180 (by rfl)).trans ((lex_skipped s permutation3 179 180 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation3 179) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation3 179 by rw [image3_eq]; rfl))

theorem lex_3_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2945) (Sat.Literal.pos 2944) (Sat.Literal.pos 179) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation3 179 (assignment s)
    (Sat.Literal.pos 2945) (Sat.Literal.pos 2944) (Sat.Literal.pos 179) (Sat.Literal.pos 171) (positive_of_descriptor s 2945 (.lex permutation3 179) (by rfl)) (lex_3_179_prefix s) (positive_select s 179) (lex_3_179_image s)

theorem lex_3_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.pos 179), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation3 179 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2944) (Sat.Literal.pos 179) (Sat.Literal.pos 171) (lex_3_179_prefix s) (positive_select s 179) (lex_3_179_image s)

theorem lex_3_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.pos 2944)] :=
  (lex_3_179_gate s).prop _ (List.Mem.head _)

theorem lex_3_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.neg 179), (Sat.Literal.pos 171)] :=
  (lex_3_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.pos 179), (Sat.Literal.neg 171)] :=
  (lex_3_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.neg 179), (Sat.Literal.neg 171), (Sat.Literal.pos 2945)] :=
  (lex_3_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2944), (Sat.Literal.pos 179), (Sat.Literal.pos 171), (Sat.Literal.pos 2945)] :=
  (lex_3_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2945) = lexBefore s permutation3 178 := by
  exact (positive_lex_of_descriptor s 2945 permutation3 179 (by rfl)).trans ((lex_skipped s permutation3 178 179 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation3 178) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation3 178 by rw [image3_eq]; rfl))

theorem lex_3_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2946) (Sat.Literal.pos 2945) (Sat.Literal.pos 178) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation3 178 (assignment s)
    (Sat.Literal.pos 2946) (Sat.Literal.pos 2945) (Sat.Literal.pos 178) (Sat.Literal.pos 170) (positive_of_descriptor s 2946 (.lex permutation3 178) (by rfl)) (lex_3_178_prefix s) (positive_select s 178) (lex_3_178_image s)

theorem lex_3_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.pos 178), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation3 178 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2945) (Sat.Literal.pos 178) (Sat.Literal.pos 170) (lex_3_178_prefix s) (positive_select s 178) (lex_3_178_image s)

theorem lex_3_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.pos 2945)] :=
  (lex_3_178_gate s).prop _ (List.Mem.head _)

theorem lex_3_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.neg 178), (Sat.Literal.pos 170)] :=
  (lex_3_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.pos 178), (Sat.Literal.neg 170)] :=
  (lex_3_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.neg 178), (Sat.Literal.neg 170), (Sat.Literal.pos 2946)] :=
  (lex_3_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2945), (Sat.Literal.pos 178), (Sat.Literal.pos 170), (Sat.Literal.pos 2946)] :=
  (lex_3_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2946) = lexBefore s permutation3 177 := by
  exact (positive_lex_of_descriptor s 2946 permutation3 178 (by rfl)).trans ((lex_skipped s permutation3 177 178 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation3 177) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation3 177 by rw [image3_eq]; rfl))

theorem lex_3_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2947) (Sat.Literal.pos 2946) (Sat.Literal.pos 177) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation3 177 (assignment s)
    (Sat.Literal.pos 2947) (Sat.Literal.pos 2946) (Sat.Literal.pos 177) (Sat.Literal.pos 169) (positive_of_descriptor s 2947 (.lex permutation3 177) (by rfl)) (lex_3_177_prefix s) (positive_select s 177) (lex_3_177_image s)

theorem lex_3_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.pos 177), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation3 177 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2946) (Sat.Literal.pos 177) (Sat.Literal.pos 169) (lex_3_177_prefix s) (positive_select s 177) (lex_3_177_image s)

theorem lex_3_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.pos 2946)] :=
  (lex_3_177_gate s).prop _ (List.Mem.head _)

theorem lex_3_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.neg 177), (Sat.Literal.pos 169)] :=
  (lex_3_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.pos 177), (Sat.Literal.neg 169)] :=
  (lex_3_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.neg 177), (Sat.Literal.neg 169), (Sat.Literal.pos 2947)] :=
  (lex_3_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2946), (Sat.Literal.pos 177), (Sat.Literal.pos 169), (Sat.Literal.pos 2947)] :=
  (lex_3_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2947) = lexBefore s permutation3 176 := by
  exact (positive_lex_of_descriptor s 2947 permutation3 177 (by rfl)).trans ((lex_skipped s permutation3 176 177 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation3 176) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation3 176 by rw [image3_eq]; rfl))

theorem lex_3_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2948) (Sat.Literal.pos 2947) (Sat.Literal.pos 176) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation3 176 (assignment s)
    (Sat.Literal.pos 2948) (Sat.Literal.pos 2947) (Sat.Literal.pos 176) (Sat.Literal.pos 168) (positive_of_descriptor s 2948 (.lex permutation3 176) (by rfl)) (lex_3_176_prefix s) (positive_select s 176) (lex_3_176_image s)

theorem lex_3_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.pos 176), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation3 176 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2947) (Sat.Literal.pos 176) (Sat.Literal.pos 168) (lex_3_176_prefix s) (positive_select s 176) (lex_3_176_image s)

theorem lex_3_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.pos 2947)] :=
  (lex_3_176_gate s).prop _ (List.Mem.head _)

theorem lex_3_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.neg 176), (Sat.Literal.pos 168)] :=
  (lex_3_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.pos 176), (Sat.Literal.neg 168)] :=
  (lex_3_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.neg 176), (Sat.Literal.neg 168), (Sat.Literal.pos 2948)] :=
  (lex_3_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2947), (Sat.Literal.pos 176), (Sat.Literal.pos 168), (Sat.Literal.pos 2948)] :=
  (lex_3_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2948) = lexBefore s permutation3 175 := by
  exact (positive_lex_of_descriptor s 2948 permutation3 176 (by rfl)).trans ((lex_skipped s permutation3 175 176 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation3 175) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation3 175 by rw [image3_eq]; rfl))

theorem lex_3_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2949) (Sat.Literal.pos 2948) (Sat.Literal.pos 175) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation3 175 (assignment s)
    (Sat.Literal.pos 2949) (Sat.Literal.pos 2948) (Sat.Literal.pos 175) (Sat.Literal.pos 183) (positive_of_descriptor s 2949 (.lex permutation3 175) (by rfl)) (lex_3_175_prefix s) (positive_select s 175) (lex_3_175_image s)

theorem lex_3_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.pos 175), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation3 175 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2948) (Sat.Literal.pos 175) (Sat.Literal.pos 183) (lex_3_175_prefix s) (positive_select s 175) (lex_3_175_image s)

theorem lex_3_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.pos 2948)] :=
  (lex_3_175_gate s).prop _ (List.Mem.head _)

theorem lex_3_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.neg 175), (Sat.Literal.pos 183)] :=
  (lex_3_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.pos 175), (Sat.Literal.neg 183)] :=
  (lex_3_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.neg 175), (Sat.Literal.neg 183), (Sat.Literal.pos 2949)] :=
  (lex_3_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2948), (Sat.Literal.pos 175), (Sat.Literal.pos 183), (Sat.Literal.pos 2949)] :=
  (lex_3_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2949) = lexBefore s permutation3 174 := by
  exact (positive_lex_of_descriptor s 2949 permutation3 175 (by rfl)).trans ((lex_skipped s permutation3 174 175 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation3 174) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation3 174 by rw [image3_eq]; rfl))

theorem lex_3_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2950) (Sat.Literal.pos 2949) (Sat.Literal.pos 174) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation3 174 (assignment s)
    (Sat.Literal.pos 2950) (Sat.Literal.pos 2949) (Sat.Literal.pos 174) (Sat.Literal.pos 182) (positive_of_descriptor s 2950 (.lex permutation3 174) (by rfl)) (lex_3_174_prefix s) (positive_select s 174) (lex_3_174_image s)

theorem lex_3_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.pos 174), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation3 174 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2949) (Sat.Literal.pos 174) (Sat.Literal.pos 182) (lex_3_174_prefix s) (positive_select s 174) (lex_3_174_image s)

theorem lex_3_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.pos 2949)] :=
  (lex_3_174_gate s).prop _ (List.Mem.head _)

theorem lex_3_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.neg 174), (Sat.Literal.pos 182)] :=
  (lex_3_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.pos 174), (Sat.Literal.neg 182)] :=
  (lex_3_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.neg 174), (Sat.Literal.neg 182), (Sat.Literal.pos 2950)] :=
  (lex_3_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2949), (Sat.Literal.pos 174), (Sat.Literal.pos 182), (Sat.Literal.pos 2950)] :=
  (lex_3_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2950) = lexBefore s permutation3 173 := by
  exact (positive_lex_of_descriptor s 2950 permutation3 174 (by rfl)).trans ((lex_skipped s permutation3 173 174 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation3 173) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation3 173 by rw [image3_eq]; rfl))

theorem lex_3_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2951) (Sat.Literal.pos 2950) (Sat.Literal.pos 173) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation3 173 (assignment s)
    (Sat.Literal.pos 2951) (Sat.Literal.pos 2950) (Sat.Literal.pos 173) (Sat.Literal.pos 181) (positive_of_descriptor s 2951 (.lex permutation3 173) (by rfl)) (lex_3_173_prefix s) (positive_select s 173) (lex_3_173_image s)

theorem lex_3_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.pos 173), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation3 173 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2950) (Sat.Literal.pos 173) (Sat.Literal.pos 181) (lex_3_173_prefix s) (positive_select s 173) (lex_3_173_image s)

theorem lex_3_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.pos 2950)] :=
  (lex_3_173_gate s).prop _ (List.Mem.head _)

theorem lex_3_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.neg 173), (Sat.Literal.pos 181)] :=
  (lex_3_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.pos 173), (Sat.Literal.neg 181)] :=
  (lex_3_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.neg 173), (Sat.Literal.neg 181), (Sat.Literal.pos 2951)] :=
  (lex_3_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2950), (Sat.Literal.pos 173), (Sat.Literal.pos 181), (Sat.Literal.pos 2951)] :=
  (lex_3_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2951) = lexBefore s permutation3 172 := by
  exact (positive_lex_of_descriptor s 2951 permutation3 173 (by rfl)).trans ((lex_skipped s permutation3 172 173 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation3 172) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation3 172 by rw [image3_eq]; rfl))

theorem lex_3_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2952) (Sat.Literal.pos 2951) (Sat.Literal.pos 172) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation3 172 (assignment s)
    (Sat.Literal.pos 2952) (Sat.Literal.pos 2951) (Sat.Literal.pos 172) (Sat.Literal.pos 180) (positive_of_descriptor s 2952 (.lex permutation3 172) (by rfl)) (lex_3_172_prefix s) (positive_select s 172) (lex_3_172_image s)

theorem lex_3_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.pos 172), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation3 172 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2951) (Sat.Literal.pos 172) (Sat.Literal.pos 180) (lex_3_172_prefix s) (positive_select s 172) (lex_3_172_image s)

theorem lex_3_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.pos 2951)] :=
  (lex_3_172_gate s).prop _ (List.Mem.head _)

theorem lex_3_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.neg 172), (Sat.Literal.pos 180)] :=
  (lex_3_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.pos 172), (Sat.Literal.neg 180)] :=
  (lex_3_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.neg 172), (Sat.Literal.neg 180), (Sat.Literal.pos 2952)] :=
  (lex_3_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2951), (Sat.Literal.pos 172), (Sat.Literal.pos 180), (Sat.Literal.pos 2952)] :=
  (lex_3_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2952) = lexBefore s permutation3 171 := by
  exact (positive_lex_of_descriptor s 2952 permutation3 172 (by rfl)).trans ((lex_skipped s permutation3 171 172 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation3 171) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation3 171 by rw [image3_eq]; rfl))

theorem lex_3_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2953) (Sat.Literal.pos 2952) (Sat.Literal.pos 171) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation3 171 (assignment s)
    (Sat.Literal.pos 2953) (Sat.Literal.pos 2952) (Sat.Literal.pos 171) (Sat.Literal.pos 179) (positive_of_descriptor s 2953 (.lex permutation3 171) (by rfl)) (lex_3_171_prefix s) (positive_select s 171) (lex_3_171_image s)

theorem lex_3_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.pos 171), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation3 171 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2952) (Sat.Literal.pos 171) (Sat.Literal.pos 179) (lex_3_171_prefix s) (positive_select s 171) (lex_3_171_image s)

theorem lex_3_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.pos 2952)] :=
  (lex_3_171_gate s).prop _ (List.Mem.head _)

theorem lex_3_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.neg 171), (Sat.Literal.pos 179)] :=
  (lex_3_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.pos 171), (Sat.Literal.neg 179)] :=
  (lex_3_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.neg 171), (Sat.Literal.neg 179), (Sat.Literal.pos 2953)] :=
  (lex_3_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2952), (Sat.Literal.pos 171), (Sat.Literal.pos 179), (Sat.Literal.pos 2953)] :=
  (lex_3_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2953) = lexBefore s permutation3 170 := by
  exact (positive_lex_of_descriptor s 2953 permutation3 171 (by rfl)).trans ((lex_skipped s permutation3 170 171 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation3 170) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation3 170 by rw [image3_eq]; rfl))

theorem lex_3_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2954) (Sat.Literal.pos 2953) (Sat.Literal.pos 170) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation3 170 (assignment s)
    (Sat.Literal.pos 2954) (Sat.Literal.pos 2953) (Sat.Literal.pos 170) (Sat.Literal.pos 178) (positive_of_descriptor s 2954 (.lex permutation3 170) (by rfl)) (lex_3_170_prefix s) (positive_select s 170) (lex_3_170_image s)

theorem lex_3_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.pos 170), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation3 170 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2953) (Sat.Literal.pos 170) (Sat.Literal.pos 178) (lex_3_170_prefix s) (positive_select s 170) (lex_3_170_image s)

theorem lex_3_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.pos 2953)] :=
  (lex_3_170_gate s).prop _ (List.Mem.head _)

theorem lex_3_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.neg 170), (Sat.Literal.pos 178)] :=
  (lex_3_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.pos 170), (Sat.Literal.neg 178)] :=
  (lex_3_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.neg 170), (Sat.Literal.neg 178), (Sat.Literal.pos 2954)] :=
  (lex_3_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2953), (Sat.Literal.pos 170), (Sat.Literal.pos 178), (Sat.Literal.pos 2954)] :=
  (lex_3_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2954) = lexBefore s permutation3 169 := by
  exact (positive_lex_of_descriptor s 2954 permutation3 170 (by rfl)).trans ((lex_skipped s permutation3 169 170 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation3 169) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation3 169 by rw [image3_eq]; rfl))

theorem lex_3_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2955) (Sat.Literal.pos 2954) (Sat.Literal.pos 169) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation3 169 (assignment s)
    (Sat.Literal.pos 2955) (Sat.Literal.pos 2954) (Sat.Literal.pos 169) (Sat.Literal.pos 177) (positive_of_descriptor s 2955 (.lex permutation3 169) (by rfl)) (lex_3_169_prefix s) (positive_select s 169) (lex_3_169_image s)

theorem lex_3_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.pos 169), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation3 169 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2954) (Sat.Literal.pos 169) (Sat.Literal.pos 177) (lex_3_169_prefix s) (positive_select s 169) (lex_3_169_image s)

theorem lex_3_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.pos 2954)] :=
  (lex_3_169_gate s).prop _ (List.Mem.head _)

theorem lex_3_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.neg 169), (Sat.Literal.pos 177)] :=
  (lex_3_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.pos 169), (Sat.Literal.neg 177)] :=
  (lex_3_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.neg 169), (Sat.Literal.neg 177), (Sat.Literal.pos 2955)] :=
  (lex_3_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2954), (Sat.Literal.pos 169), (Sat.Literal.pos 177), (Sat.Literal.pos 2955)] :=
  (lex_3_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2955) = lexBefore s permutation3 168 := by
  exact (positive_lex_of_descriptor s 2955 permutation3 169 (by rfl)).trans ((lex_skipped s permutation3 168 169 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation3 168) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation3 168 by rw [image3_eq]; rfl))

theorem lex_3_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2956) (Sat.Literal.pos 2955) (Sat.Literal.pos 168) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation3 168 (assignment s)
    (Sat.Literal.pos 2956) (Sat.Literal.pos 2955) (Sat.Literal.pos 168) (Sat.Literal.pos 176) (positive_of_descriptor s 2956 (.lex permutation3 168) (by rfl)) (lex_3_168_prefix s) (positive_select s 168) (lex_3_168_image s)

theorem lex_3_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.pos 168), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation3 168 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2955) (Sat.Literal.pos 168) (Sat.Literal.pos 176) (lex_3_168_prefix s) (positive_select s 168) (lex_3_168_image s)

theorem lex_3_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.pos 2955)] :=
  (lex_3_168_gate s).prop _ (List.Mem.head _)

theorem lex_3_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.neg 168), (Sat.Literal.pos 176)] :=
  (lex_3_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.pos 168), (Sat.Literal.neg 176)] :=
  (lex_3_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.neg 168), (Sat.Literal.neg 176), (Sat.Literal.pos 2956)] :=
  (lex_3_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2955), (Sat.Literal.pos 168), (Sat.Literal.pos 176), (Sat.Literal.pos 2956)] :=
  (lex_3_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2956) = lexBefore s permutation3 151 := by
  exact (positive_lex_of_descriptor s 2956 permutation3 168 (by rfl)).trans ((lex_skipped s permutation3 151 168 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 152 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation3 151) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation3 151 by rw [image3_eq]; rfl))

theorem lex_3_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2957) (Sat.Literal.pos 2956) (Sat.Literal.pos 151) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation3 151 (assignment s)
    (Sat.Literal.pos 2957) (Sat.Literal.pos 2956) (Sat.Literal.pos 151) (Sat.Literal.pos 143) (positive_of_descriptor s 2957 (.lex permutation3 151) (by rfl)) (lex_3_151_prefix s) (positive_select s 151) (lex_3_151_image s)

theorem lex_3_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.pos 151), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation3 151 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2956) (Sat.Literal.pos 151) (Sat.Literal.pos 143) (lex_3_151_prefix s) (positive_select s 151) (lex_3_151_image s)

theorem lex_3_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.pos 2956)] :=
  (lex_3_151_gate s).prop _ (List.Mem.head _)

theorem lex_3_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.neg 151), (Sat.Literal.pos 143)] :=
  (lex_3_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.pos 151), (Sat.Literal.neg 143)] :=
  (lex_3_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.neg 151), (Sat.Literal.neg 143), (Sat.Literal.pos 2957)] :=
  (lex_3_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2956), (Sat.Literal.pos 151), (Sat.Literal.pos 143), (Sat.Literal.pos 2957)] :=
  (lex_3_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2957) = lexBefore s permutation3 150 := by
  exact (positive_lex_of_descriptor s 2957 permutation3 151 (by rfl)).trans ((lex_skipped s permutation3 150 151 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation3 150) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation3 150 by rw [image3_eq]; rfl))

theorem lex_3_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2958) (Sat.Literal.pos 2957) (Sat.Literal.pos 150) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation3 150 (assignment s)
    (Sat.Literal.pos 2958) (Sat.Literal.pos 2957) (Sat.Literal.pos 150) (Sat.Literal.pos 142) (positive_of_descriptor s 2958 (.lex permutation3 150) (by rfl)) (lex_3_150_prefix s) (positive_select s 150) (lex_3_150_image s)

theorem lex_3_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.pos 150), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation3 150 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2957) (Sat.Literal.pos 150) (Sat.Literal.pos 142) (lex_3_150_prefix s) (positive_select s 150) (lex_3_150_image s)

theorem lex_3_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.pos 2957)] :=
  (lex_3_150_gate s).prop _ (List.Mem.head _)

theorem lex_3_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.neg 150), (Sat.Literal.pos 142)] :=
  (lex_3_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.pos 150), (Sat.Literal.neg 142)] :=
  (lex_3_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.neg 150), (Sat.Literal.neg 142), (Sat.Literal.pos 2958)] :=
  (lex_3_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2957), (Sat.Literal.pos 150), (Sat.Literal.pos 142), (Sat.Literal.pos 2958)] :=
  (lex_3_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2958) = lexBefore s permutation3 149 := by
  exact (positive_lex_of_descriptor s 2958 permutation3 150 (by rfl)).trans ((lex_skipped s permutation3 149 150 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation3 149) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation3 149 by rw [image3_eq]; rfl))

theorem lex_3_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2959) (Sat.Literal.pos 2958) (Sat.Literal.pos 149) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation3 149 (assignment s)
    (Sat.Literal.pos 2959) (Sat.Literal.pos 2958) (Sat.Literal.pos 149) (Sat.Literal.pos 141) (positive_of_descriptor s 2959 (.lex permutation3 149) (by rfl)) (lex_3_149_prefix s) (positive_select s 149) (lex_3_149_image s)

theorem lex_3_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.pos 149), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation3 149 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2958) (Sat.Literal.pos 149) (Sat.Literal.pos 141) (lex_3_149_prefix s) (positive_select s 149) (lex_3_149_image s)

theorem lex_3_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.pos 2958)] :=
  (lex_3_149_gate s).prop _ (List.Mem.head _)

theorem lex_3_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.neg 149), (Sat.Literal.pos 141)] :=
  (lex_3_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.pos 149), (Sat.Literal.neg 141)] :=
  (lex_3_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.neg 149), (Sat.Literal.neg 141), (Sat.Literal.pos 2959)] :=
  (lex_3_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2958), (Sat.Literal.pos 149), (Sat.Literal.pos 141), (Sat.Literal.pos 2959)] :=
  (lex_3_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2959) = lexBefore s permutation3 148 := by
  exact (positive_lex_of_descriptor s 2959 permutation3 149 (by rfl)).trans ((lex_skipped s permutation3 148 149 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation3 148) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation3 148 by rw [image3_eq]; rfl))

theorem lex_3_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2960) (Sat.Literal.pos 2959) (Sat.Literal.pos 148) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation3 148 (assignment s)
    (Sat.Literal.pos 2960) (Sat.Literal.pos 2959) (Sat.Literal.pos 148) (Sat.Literal.pos 140) (positive_of_descriptor s 2960 (.lex permutation3 148) (by rfl)) (lex_3_148_prefix s) (positive_select s 148) (lex_3_148_image s)

theorem lex_3_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.pos 148), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation3 148 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2959) (Sat.Literal.pos 148) (Sat.Literal.pos 140) (lex_3_148_prefix s) (positive_select s 148) (lex_3_148_image s)

theorem lex_3_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.pos 2959)] :=
  (lex_3_148_gate s).prop _ (List.Mem.head _)

theorem lex_3_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.neg 148), (Sat.Literal.pos 140)] :=
  (lex_3_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.pos 148), (Sat.Literal.neg 140)] :=
  (lex_3_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.neg 148), (Sat.Literal.neg 140), (Sat.Literal.pos 2960)] :=
  (lex_3_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2959), (Sat.Literal.pos 148), (Sat.Literal.pos 140), (Sat.Literal.pos 2960)] :=
  (lex_3_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2960) = lexBefore s permutation3 147 := by
  exact (positive_lex_of_descriptor s 2960 permutation3 148 (by rfl)).trans ((lex_skipped s permutation3 147 148 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation3 147) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation3 147 by rw [image3_eq]; rfl))

theorem lex_3_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2961) (Sat.Literal.pos 2960) (Sat.Literal.pos 147) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation3 147 (assignment s)
    (Sat.Literal.pos 2961) (Sat.Literal.pos 2960) (Sat.Literal.pos 147) (Sat.Literal.pos 139) (positive_of_descriptor s 2961 (.lex permutation3 147) (by rfl)) (lex_3_147_prefix s) (positive_select s 147) (lex_3_147_image s)

theorem lex_3_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.pos 147), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation3 147 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2960) (Sat.Literal.pos 147) (Sat.Literal.pos 139) (lex_3_147_prefix s) (positive_select s 147) (lex_3_147_image s)

theorem lex_3_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.pos 2960)] :=
  (lex_3_147_gate s).prop _ (List.Mem.head _)

theorem lex_3_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.neg 147), (Sat.Literal.pos 139)] :=
  (lex_3_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.pos 147), (Sat.Literal.neg 139)] :=
  (lex_3_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.neg 147), (Sat.Literal.neg 139), (Sat.Literal.pos 2961)] :=
  (lex_3_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2960), (Sat.Literal.pos 147), (Sat.Literal.pos 139), (Sat.Literal.pos 2961)] :=
  (lex_3_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2961) = lexBefore s permutation3 146 := by
  exact (positive_lex_of_descriptor s 2961 permutation3 147 (by rfl)).trans ((lex_skipped s permutation3 146 147 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation3 146) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation3 146 by rw [image3_eq]; rfl))

theorem lex_3_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2962) (Sat.Literal.pos 2961) (Sat.Literal.pos 146) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation3 146 (assignment s)
    (Sat.Literal.pos 2962) (Sat.Literal.pos 2961) (Sat.Literal.pos 146) (Sat.Literal.pos 138) (positive_of_descriptor s 2962 (.lex permutation3 146) (by rfl)) (lex_3_146_prefix s) (positive_select s 146) (lex_3_146_image s)

theorem lex_3_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.pos 146), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation3 146 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2961) (Sat.Literal.pos 146) (Sat.Literal.pos 138) (lex_3_146_prefix s) (positive_select s 146) (lex_3_146_image s)

theorem lex_3_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.pos 2961)] :=
  (lex_3_146_gate s).prop _ (List.Mem.head _)

theorem lex_3_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.neg 146), (Sat.Literal.pos 138)] :=
  (lex_3_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.pos 146), (Sat.Literal.neg 138)] :=
  (lex_3_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.neg 146), (Sat.Literal.neg 138), (Sat.Literal.pos 2962)] :=
  (lex_3_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2961), (Sat.Literal.pos 146), (Sat.Literal.pos 138), (Sat.Literal.pos 2962)] :=
  (lex_3_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2962) = lexBefore s permutation3 145 := by
  exact (positive_lex_of_descriptor s 2962 permutation3 146 (by rfl)).trans ((lex_skipped s permutation3 145 146 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation3 145) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation3 145 by rw [image3_eq]; rfl))

theorem lex_3_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2963) (Sat.Literal.pos 2962) (Sat.Literal.pos 145) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation3 145 (assignment s)
    (Sat.Literal.pos 2963) (Sat.Literal.pos 2962) (Sat.Literal.pos 145) (Sat.Literal.pos 137) (positive_of_descriptor s 2963 (.lex permutation3 145) (by rfl)) (lex_3_145_prefix s) (positive_select s 145) (lex_3_145_image s)

theorem lex_3_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.pos 145), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation3 145 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2962) (Sat.Literal.pos 145) (Sat.Literal.pos 137) (lex_3_145_prefix s) (positive_select s 145) (lex_3_145_image s)

theorem lex_3_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.pos 2962)] :=
  (lex_3_145_gate s).prop _ (List.Mem.head _)

theorem lex_3_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.neg 145), (Sat.Literal.pos 137)] :=
  (lex_3_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.pos 145), (Sat.Literal.neg 137)] :=
  (lex_3_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.neg 145), (Sat.Literal.neg 137), (Sat.Literal.pos 2963)] :=
  (lex_3_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2962), (Sat.Literal.pos 145), (Sat.Literal.pos 137), (Sat.Literal.pos 2963)] :=
  (lex_3_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2963) = lexBefore s permutation3 144 := by
  exact (positive_lex_of_descriptor s 2963 permutation3 145 (by rfl)).trans ((lex_skipped s permutation3 144 145 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation3 144) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation3 144 by rw [image3_eq]; rfl))

theorem lex_3_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2964) (Sat.Literal.pos 2963) (Sat.Literal.pos 144) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation3 144 (assignment s)
    (Sat.Literal.pos 2964) (Sat.Literal.pos 2963) (Sat.Literal.pos 144) (Sat.Literal.pos 136) (positive_of_descriptor s 2964 (.lex permutation3 144) (by rfl)) (lex_3_144_prefix s) (positive_select s 144) (lex_3_144_image s)

theorem lex_3_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.pos 144), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation3 144 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2963) (Sat.Literal.pos 144) (Sat.Literal.pos 136) (lex_3_144_prefix s) (positive_select s 144) (lex_3_144_image s)

theorem lex_3_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.pos 2963)] :=
  (lex_3_144_gate s).prop _ (List.Mem.head _)

theorem lex_3_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.neg 144), (Sat.Literal.pos 136)] :=
  (lex_3_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.pos 144), (Sat.Literal.neg 136)] :=
  (lex_3_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.neg 144), (Sat.Literal.neg 136), (Sat.Literal.pos 2964)] :=
  (lex_3_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2963), (Sat.Literal.pos 144), (Sat.Literal.pos 136), (Sat.Literal.pos 2964)] :=
  (lex_3_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2964) = lexBefore s permutation3 143 := by
  exact (positive_lex_of_descriptor s 2964 permutation3 144 (by rfl)).trans ((lex_skipped s permutation3 143 144 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation3 143) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation3 143 by rw [image3_eq]; rfl))

theorem lex_3_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2965) (Sat.Literal.pos 2964) (Sat.Literal.pos 143) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation3 143 (assignment s)
    (Sat.Literal.pos 2965) (Sat.Literal.pos 2964) (Sat.Literal.pos 143) (Sat.Literal.pos 151) (positive_of_descriptor s 2965 (.lex permutation3 143) (by rfl)) (lex_3_143_prefix s) (positive_select s 143) (lex_3_143_image s)

theorem lex_3_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.pos 143), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation3 143 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2964) (Sat.Literal.pos 143) (Sat.Literal.pos 151) (lex_3_143_prefix s) (positive_select s 143) (lex_3_143_image s)

theorem lex_3_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.pos 2964)] :=
  (lex_3_143_gate s).prop _ (List.Mem.head _)

theorem lex_3_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.neg 143), (Sat.Literal.pos 151)] :=
  (lex_3_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.pos 143), (Sat.Literal.neg 151)] :=
  (lex_3_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.neg 143), (Sat.Literal.neg 151), (Sat.Literal.pos 2965)] :=
  (lex_3_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2964), (Sat.Literal.pos 143), (Sat.Literal.pos 151), (Sat.Literal.pos 2965)] :=
  (lex_3_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2965) = lexBefore s permutation3 142 := by
  exact (positive_lex_of_descriptor s 2965 permutation3 143 (by rfl)).trans ((lex_skipped s permutation3 142 143 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation3 142) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation3 142 by rw [image3_eq]; rfl))

theorem lex_3_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2966) (Sat.Literal.pos 2965) (Sat.Literal.pos 142) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation3 142 (assignment s)
    (Sat.Literal.pos 2966) (Sat.Literal.pos 2965) (Sat.Literal.pos 142) (Sat.Literal.pos 150) (positive_of_descriptor s 2966 (.lex permutation3 142) (by rfl)) (lex_3_142_prefix s) (positive_select s 142) (lex_3_142_image s)

theorem lex_3_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.pos 142), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation3 142 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2965) (Sat.Literal.pos 142) (Sat.Literal.pos 150) (lex_3_142_prefix s) (positive_select s 142) (lex_3_142_image s)

theorem lex_3_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.pos 2965)] :=
  (lex_3_142_gate s).prop _ (List.Mem.head _)

theorem lex_3_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.neg 142), (Sat.Literal.pos 150)] :=
  (lex_3_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.pos 142), (Sat.Literal.neg 150)] :=
  (lex_3_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.neg 142), (Sat.Literal.neg 150), (Sat.Literal.pos 2966)] :=
  (lex_3_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2965), (Sat.Literal.pos 142), (Sat.Literal.pos 150), (Sat.Literal.pos 2966)] :=
  (lex_3_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2966) = lexBefore s permutation3 141 := by
  exact (positive_lex_of_descriptor s 2966 permutation3 142 (by rfl)).trans ((lex_skipped s permutation3 141 142 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation3 141) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation3 141 by rw [image3_eq]; rfl))

theorem lex_3_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2967) (Sat.Literal.pos 2966) (Sat.Literal.pos 141) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation3 141 (assignment s)
    (Sat.Literal.pos 2967) (Sat.Literal.pos 2966) (Sat.Literal.pos 141) (Sat.Literal.pos 149) (positive_of_descriptor s 2967 (.lex permutation3 141) (by rfl)) (lex_3_141_prefix s) (positive_select s 141) (lex_3_141_image s)

theorem lex_3_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.pos 141), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation3 141 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2966) (Sat.Literal.pos 141) (Sat.Literal.pos 149) (lex_3_141_prefix s) (positive_select s 141) (lex_3_141_image s)

theorem lex_3_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.pos 2966)] :=
  (lex_3_141_gate s).prop _ (List.Mem.head _)

theorem lex_3_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.neg 141), (Sat.Literal.pos 149)] :=
  (lex_3_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.pos 141), (Sat.Literal.neg 149)] :=
  (lex_3_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.neg 141), (Sat.Literal.neg 149), (Sat.Literal.pos 2967)] :=
  (lex_3_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2966), (Sat.Literal.pos 141), (Sat.Literal.pos 149), (Sat.Literal.pos 2967)] :=
  (lex_3_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2967) = lexBefore s permutation3 140 := by
  exact (positive_lex_of_descriptor s 2967 permutation3 141 (by rfl)).trans ((lex_skipped s permutation3 140 141 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation3 140) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation3 140 by rw [image3_eq]; rfl))

theorem lex_3_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2968) (Sat.Literal.pos 2967) (Sat.Literal.pos 140) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation3 140 (assignment s)
    (Sat.Literal.pos 2968) (Sat.Literal.pos 2967) (Sat.Literal.pos 140) (Sat.Literal.pos 148) (positive_of_descriptor s 2968 (.lex permutation3 140) (by rfl)) (lex_3_140_prefix s) (positive_select s 140) (lex_3_140_image s)

theorem lex_3_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.pos 140), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation3 140 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2967) (Sat.Literal.pos 140) (Sat.Literal.pos 148) (lex_3_140_prefix s) (positive_select s 140) (lex_3_140_image s)

theorem lex_3_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.pos 2967)] :=
  (lex_3_140_gate s).prop _ (List.Mem.head _)

theorem lex_3_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.neg 140), (Sat.Literal.pos 148)] :=
  (lex_3_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.pos 140), (Sat.Literal.neg 148)] :=
  (lex_3_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.neg 140), (Sat.Literal.neg 148), (Sat.Literal.pos 2968)] :=
  (lex_3_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2967), (Sat.Literal.pos 140), (Sat.Literal.pos 148), (Sat.Literal.pos 2968)] :=
  (lex_3_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2968) = lexBefore s permutation3 139 := by
  exact (positive_lex_of_descriptor s 2968 permutation3 140 (by rfl)).trans ((lex_skipped s permutation3 139 140 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation3 139) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation3 139 by rw [image3_eq]; rfl))

theorem lex_3_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2969) (Sat.Literal.pos 2968) (Sat.Literal.pos 139) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation3 139 (assignment s)
    (Sat.Literal.pos 2969) (Sat.Literal.pos 2968) (Sat.Literal.pos 139) (Sat.Literal.pos 147) (positive_of_descriptor s 2969 (.lex permutation3 139) (by rfl)) (lex_3_139_prefix s) (positive_select s 139) (lex_3_139_image s)

theorem lex_3_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.pos 139), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation3 139 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2968) (Sat.Literal.pos 139) (Sat.Literal.pos 147) (lex_3_139_prefix s) (positive_select s 139) (lex_3_139_image s)

theorem lex_3_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.pos 2968)] :=
  (lex_3_139_gate s).prop _ (List.Mem.head _)

theorem lex_3_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.neg 139), (Sat.Literal.pos 147)] :=
  (lex_3_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.pos 139), (Sat.Literal.neg 147)] :=
  (lex_3_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.neg 139), (Sat.Literal.neg 147), (Sat.Literal.pos 2969)] :=
  (lex_3_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2968), (Sat.Literal.pos 139), (Sat.Literal.pos 147), (Sat.Literal.pos 2969)] :=
  (lex_3_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2969) = lexBefore s permutation3 138 := by
  exact (positive_lex_of_descriptor s 2969 permutation3 139 (by rfl)).trans ((lex_skipped s permutation3 138 139 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation3 138) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation3 138 by rw [image3_eq]; rfl))

theorem lex_3_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2970) (Sat.Literal.pos 2969) (Sat.Literal.pos 138) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation3 138 (assignment s)
    (Sat.Literal.pos 2970) (Sat.Literal.pos 2969) (Sat.Literal.pos 138) (Sat.Literal.pos 146) (positive_of_descriptor s 2970 (.lex permutation3 138) (by rfl)) (lex_3_138_prefix s) (positive_select s 138) (lex_3_138_image s)

theorem lex_3_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.pos 138), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation3 138 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2969) (Sat.Literal.pos 138) (Sat.Literal.pos 146) (lex_3_138_prefix s) (positive_select s 138) (lex_3_138_image s)

theorem lex_3_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.pos 2969)] :=
  (lex_3_138_gate s).prop _ (List.Mem.head _)

theorem lex_3_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.neg 138), (Sat.Literal.pos 146)] :=
  (lex_3_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.pos 138), (Sat.Literal.neg 146)] :=
  (lex_3_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.neg 138), (Sat.Literal.neg 146), (Sat.Literal.pos 2970)] :=
  (lex_3_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2969), (Sat.Literal.pos 138), (Sat.Literal.pos 146), (Sat.Literal.pos 2970)] :=
  (lex_3_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2970) = lexBefore s permutation3 137 := by
  exact (positive_lex_of_descriptor s 2970 permutation3 138 (by rfl)).trans ((lex_skipped s permutation3 137 138 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation3 137) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation3 137 by rw [image3_eq]; rfl))

theorem lex_3_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2971) (Sat.Literal.pos 2970) (Sat.Literal.pos 137) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation3 137 (assignment s)
    (Sat.Literal.pos 2971) (Sat.Literal.pos 2970) (Sat.Literal.pos 137) (Sat.Literal.pos 145) (positive_of_descriptor s 2971 (.lex permutation3 137) (by rfl)) (lex_3_137_prefix s) (positive_select s 137) (lex_3_137_image s)

theorem lex_3_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.pos 137), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation3 137 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2970) (Sat.Literal.pos 137) (Sat.Literal.pos 145) (lex_3_137_prefix s) (positive_select s 137) (lex_3_137_image s)

theorem lex_3_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.pos 2970)] :=
  (lex_3_137_gate s).prop _ (List.Mem.head _)

theorem lex_3_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.neg 137), (Sat.Literal.pos 145)] :=
  (lex_3_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.pos 137), (Sat.Literal.neg 145)] :=
  (lex_3_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.neg 137), (Sat.Literal.neg 145), (Sat.Literal.pos 2971)] :=
  (lex_3_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2970), (Sat.Literal.pos 137), (Sat.Literal.pos 145), (Sat.Literal.pos 2971)] :=
  (lex_3_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2971) = lexBefore s permutation3 136 := by
  exact (positive_lex_of_descriptor s 2971 permutation3 137 (by rfl)).trans ((lex_skipped s permutation3 136 137 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation3 136) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation3 136 by rw [image3_eq]; rfl))

theorem lex_3_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2972) (Sat.Literal.pos 2971) (Sat.Literal.pos 136) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation3 136 (assignment s)
    (Sat.Literal.pos 2972) (Sat.Literal.pos 2971) (Sat.Literal.pos 136) (Sat.Literal.pos 144) (positive_of_descriptor s 2972 (.lex permutation3 136) (by rfl)) (lex_3_136_prefix s) (positive_select s 136) (lex_3_136_image s)

theorem lex_3_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.pos 136), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation3 136 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2971) (Sat.Literal.pos 136) (Sat.Literal.pos 144) (lex_3_136_prefix s) (positive_select s 136) (lex_3_136_image s)

theorem lex_3_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.pos 2971)] :=
  (lex_3_136_gate s).prop _ (List.Mem.head _)

theorem lex_3_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.neg 136), (Sat.Literal.pos 144)] :=
  (lex_3_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.pos 136), (Sat.Literal.neg 144)] :=
  (lex_3_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.neg 136), (Sat.Literal.neg 144), (Sat.Literal.pos 2972)] :=
  (lex_3_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2971), (Sat.Literal.pos 136), (Sat.Literal.pos 144), (Sat.Literal.pos 2972)] :=
  (lex_3_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2972) = lexBefore s permutation3 119 := by
  exact (positive_lex_of_descriptor s 2972 permutation3 136 (by rfl)).trans ((lex_skipped s permutation3 119 136 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 120 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation3 119) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation3 119 by rw [image3_eq]; rfl))

theorem lex_3_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2973) (Sat.Literal.pos 2972) (Sat.Literal.pos 119) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation3 119 (assignment s)
    (Sat.Literal.pos 2973) (Sat.Literal.pos 2972) (Sat.Literal.pos 119) (Sat.Literal.pos 111) (positive_of_descriptor s 2973 (.lex permutation3 119) (by rfl)) (lex_3_119_prefix s) (positive_select s 119) (lex_3_119_image s)

theorem lex_3_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.pos 119), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation3 119 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2972) (Sat.Literal.pos 119) (Sat.Literal.pos 111) (lex_3_119_prefix s) (positive_select s 119) (lex_3_119_image s)

theorem lex_3_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.pos 2972)] :=
  (lex_3_119_gate s).prop _ (List.Mem.head _)

theorem lex_3_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.neg 119), (Sat.Literal.pos 111)] :=
  (lex_3_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.pos 119), (Sat.Literal.neg 111)] :=
  (lex_3_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.neg 119), (Sat.Literal.neg 111), (Sat.Literal.pos 2973)] :=
  (lex_3_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2972), (Sat.Literal.pos 119), (Sat.Literal.pos 111), (Sat.Literal.pos 2973)] :=
  (lex_3_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2973) = lexBefore s permutation3 118 := by
  exact (positive_lex_of_descriptor s 2973 permutation3 119 (by rfl)).trans ((lex_skipped s permutation3 118 119 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation3 118) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation3 118 by rw [image3_eq]; rfl))

theorem lex_3_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2974) (Sat.Literal.pos 2973) (Sat.Literal.pos 118) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation3 118 (assignment s)
    (Sat.Literal.pos 2974) (Sat.Literal.pos 2973) (Sat.Literal.pos 118) (Sat.Literal.pos 110) (positive_of_descriptor s 2974 (.lex permutation3 118) (by rfl)) (lex_3_118_prefix s) (positive_select s 118) (lex_3_118_image s)

theorem lex_3_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.pos 118), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation3 118 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2973) (Sat.Literal.pos 118) (Sat.Literal.pos 110) (lex_3_118_prefix s) (positive_select s 118) (lex_3_118_image s)

theorem lex_3_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.pos 2973)] :=
  (lex_3_118_gate s).prop _ (List.Mem.head _)

theorem lex_3_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.neg 118), (Sat.Literal.pos 110)] :=
  (lex_3_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.pos 118), (Sat.Literal.neg 110)] :=
  (lex_3_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.neg 118), (Sat.Literal.neg 110), (Sat.Literal.pos 2974)] :=
  (lex_3_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2973), (Sat.Literal.pos 118), (Sat.Literal.pos 110), (Sat.Literal.pos 2974)] :=
  (lex_3_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2974) = lexBefore s permutation3 117 := by
  exact (positive_lex_of_descriptor s 2974 permutation3 118 (by rfl)).trans ((lex_skipped s permutation3 117 118 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation3 117) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation3 117 by rw [image3_eq]; rfl))

theorem lex_3_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2975) (Sat.Literal.pos 2974) (Sat.Literal.pos 117) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation3 117 (assignment s)
    (Sat.Literal.pos 2975) (Sat.Literal.pos 2974) (Sat.Literal.pos 117) (Sat.Literal.pos 109) (positive_of_descriptor s 2975 (.lex permutation3 117) (by rfl)) (lex_3_117_prefix s) (positive_select s 117) (lex_3_117_image s)

theorem lex_3_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.pos 117), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation3 117 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2974) (Sat.Literal.pos 117) (Sat.Literal.pos 109) (lex_3_117_prefix s) (positive_select s 117) (lex_3_117_image s)

theorem lex_3_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.pos 2974)] :=
  (lex_3_117_gate s).prop _ (List.Mem.head _)

theorem lex_3_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.neg 117), (Sat.Literal.pos 109)] :=
  (lex_3_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.pos 117), (Sat.Literal.neg 109)] :=
  (lex_3_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.neg 117), (Sat.Literal.neg 109), (Sat.Literal.pos 2975)] :=
  (lex_3_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2974), (Sat.Literal.pos 117), (Sat.Literal.pos 109), (Sat.Literal.pos 2975)] :=
  (lex_3_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2975) = lexBefore s permutation3 116 := by
  exact (positive_lex_of_descriptor s 2975 permutation3 117 (by rfl)).trans ((lex_skipped s permutation3 116 117 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation3 116) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation3 116 by rw [image3_eq]; rfl))

theorem lex_3_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2976) (Sat.Literal.pos 2975) (Sat.Literal.pos 116) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation3 116 (assignment s)
    (Sat.Literal.pos 2976) (Sat.Literal.pos 2975) (Sat.Literal.pos 116) (Sat.Literal.pos 108) (positive_of_descriptor s 2976 (.lex permutation3 116) (by rfl)) (lex_3_116_prefix s) (positive_select s 116) (lex_3_116_image s)

theorem lex_3_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.pos 116), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation3 116 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2975) (Sat.Literal.pos 116) (Sat.Literal.pos 108) (lex_3_116_prefix s) (positive_select s 116) (lex_3_116_image s)

theorem lex_3_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.pos 2975)] :=
  (lex_3_116_gate s).prop _ (List.Mem.head _)

theorem lex_3_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.neg 116), (Sat.Literal.pos 108)] :=
  (lex_3_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.pos 116), (Sat.Literal.neg 108)] :=
  (lex_3_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.neg 116), (Sat.Literal.neg 108), (Sat.Literal.pos 2976)] :=
  (lex_3_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2975), (Sat.Literal.pos 116), (Sat.Literal.pos 108), (Sat.Literal.pos 2976)] :=
  (lex_3_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2976) = lexBefore s permutation3 115 := by
  exact (positive_lex_of_descriptor s 2976 permutation3 116 (by rfl)).trans ((lex_skipped s permutation3 115 116 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation3 115) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation3 115 by rw [image3_eq]; rfl))

theorem lex_3_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2977) (Sat.Literal.pos 2976) (Sat.Literal.pos 115) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation3 115 (assignment s)
    (Sat.Literal.pos 2977) (Sat.Literal.pos 2976) (Sat.Literal.pos 115) (Sat.Literal.pos 107) (positive_of_descriptor s 2977 (.lex permutation3 115) (by rfl)) (lex_3_115_prefix s) (positive_select s 115) (lex_3_115_image s)

theorem lex_3_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.pos 115), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation3 115 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2976) (Sat.Literal.pos 115) (Sat.Literal.pos 107) (lex_3_115_prefix s) (positive_select s 115) (lex_3_115_image s)

theorem lex_3_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.pos 2976)] :=
  (lex_3_115_gate s).prop _ (List.Mem.head _)

theorem lex_3_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.neg 115), (Sat.Literal.pos 107)] :=
  (lex_3_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.pos 115), (Sat.Literal.neg 107)] :=
  (lex_3_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.neg 115), (Sat.Literal.neg 107), (Sat.Literal.pos 2977)] :=
  (lex_3_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2976), (Sat.Literal.pos 115), (Sat.Literal.pos 107), (Sat.Literal.pos 2977)] :=
  (lex_3_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2977) = lexBefore s permutation3 114 := by
  exact (positive_lex_of_descriptor s 2977 permutation3 115 (by rfl)).trans ((lex_skipped s permutation3 114 115 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation3 114) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation3 114 by rw [image3_eq]; rfl))

theorem lex_3_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2978) (Sat.Literal.pos 2977) (Sat.Literal.pos 114) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation3 114 (assignment s)
    (Sat.Literal.pos 2978) (Sat.Literal.pos 2977) (Sat.Literal.pos 114) (Sat.Literal.pos 106) (positive_of_descriptor s 2978 (.lex permutation3 114) (by rfl)) (lex_3_114_prefix s) (positive_select s 114) (lex_3_114_image s)

theorem lex_3_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.pos 114), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation3 114 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2977) (Sat.Literal.pos 114) (Sat.Literal.pos 106) (lex_3_114_prefix s) (positive_select s 114) (lex_3_114_image s)

theorem lex_3_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.pos 2977)] :=
  (lex_3_114_gate s).prop _ (List.Mem.head _)

theorem lex_3_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.neg 114), (Sat.Literal.pos 106)] :=
  (lex_3_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.pos 114), (Sat.Literal.neg 106)] :=
  (lex_3_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.neg 114), (Sat.Literal.neg 106), (Sat.Literal.pos 2978)] :=
  (lex_3_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2977), (Sat.Literal.pos 114), (Sat.Literal.pos 106), (Sat.Literal.pos 2978)] :=
  (lex_3_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2978) = lexBefore s permutation3 113 := by
  exact (positive_lex_of_descriptor s 2978 permutation3 114 (by rfl)).trans ((lex_skipped s permutation3 113 114 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation3 113) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation3 113 by rw [image3_eq]; rfl))

theorem lex_3_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2979) (Sat.Literal.pos 2978) (Sat.Literal.pos 113) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation3 113 (assignment s)
    (Sat.Literal.pos 2979) (Sat.Literal.pos 2978) (Sat.Literal.pos 113) (Sat.Literal.pos 105) (positive_of_descriptor s 2979 (.lex permutation3 113) (by rfl)) (lex_3_113_prefix s) (positive_select s 113) (lex_3_113_image s)

theorem lex_3_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.pos 113), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation3 113 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2978) (Sat.Literal.pos 113) (Sat.Literal.pos 105) (lex_3_113_prefix s) (positive_select s 113) (lex_3_113_image s)

theorem lex_3_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.pos 2978)] :=
  (lex_3_113_gate s).prop _ (List.Mem.head _)

theorem lex_3_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.neg 113), (Sat.Literal.pos 105)] :=
  (lex_3_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.pos 113), (Sat.Literal.neg 105)] :=
  (lex_3_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.neg 113), (Sat.Literal.neg 105), (Sat.Literal.pos 2979)] :=
  (lex_3_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2978), (Sat.Literal.pos 113), (Sat.Literal.pos 105), (Sat.Literal.pos 2979)] :=
  (lex_3_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2979) = lexBefore s permutation3 112 := by
  exact (positive_lex_of_descriptor s 2979 permutation3 113 (by rfl)).trans ((lex_skipped s permutation3 112 113 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation3 112) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation3 112 by rw [image3_eq]; rfl))

theorem lex_3_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2980) (Sat.Literal.pos 2979) (Sat.Literal.pos 112) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation3 112 (assignment s)
    (Sat.Literal.pos 2980) (Sat.Literal.pos 2979) (Sat.Literal.pos 112) (Sat.Literal.pos 104) (positive_of_descriptor s 2980 (.lex permutation3 112) (by rfl)) (lex_3_112_prefix s) (positive_select s 112) (lex_3_112_image s)

theorem lex_3_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.pos 112), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation3 112 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2979) (Sat.Literal.pos 112) (Sat.Literal.pos 104) (lex_3_112_prefix s) (positive_select s 112) (lex_3_112_image s)

theorem lex_3_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.pos 2979)] :=
  (lex_3_112_gate s).prop _ (List.Mem.head _)

theorem lex_3_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.neg 112), (Sat.Literal.pos 104)] :=
  (lex_3_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.pos 112), (Sat.Literal.neg 104)] :=
  (lex_3_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.neg 112), (Sat.Literal.neg 104), (Sat.Literal.pos 2980)] :=
  (lex_3_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2979), (Sat.Literal.pos 112), (Sat.Literal.pos 104), (Sat.Literal.pos 2980)] :=
  (lex_3_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2980) = lexBefore s permutation3 111 := by
  exact (positive_lex_of_descriptor s 2980 permutation3 112 (by rfl)).trans ((lex_skipped s permutation3 111 112 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation3 111) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation3 111 by rw [image3_eq]; rfl))

theorem lex_3_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2981) (Sat.Literal.pos 2980) (Sat.Literal.pos 111) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation3 111 (assignment s)
    (Sat.Literal.pos 2981) (Sat.Literal.pos 2980) (Sat.Literal.pos 111) (Sat.Literal.pos 119) (positive_of_descriptor s 2981 (.lex permutation3 111) (by rfl)) (lex_3_111_prefix s) (positive_select s 111) (lex_3_111_image s)

theorem lex_3_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.pos 111), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation3 111 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2980) (Sat.Literal.pos 111) (Sat.Literal.pos 119) (lex_3_111_prefix s) (positive_select s 111) (lex_3_111_image s)

theorem lex_3_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.pos 2980)] :=
  (lex_3_111_gate s).prop _ (List.Mem.head _)

theorem lex_3_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.neg 111), (Sat.Literal.pos 119)] :=
  (lex_3_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.pos 111), (Sat.Literal.neg 119)] :=
  (lex_3_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.neg 111), (Sat.Literal.neg 119), (Sat.Literal.pos 2981)] :=
  (lex_3_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2980), (Sat.Literal.pos 111), (Sat.Literal.pos 119), (Sat.Literal.pos 2981)] :=
  (lex_3_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2981) = lexBefore s permutation3 110 := by
  exact (positive_lex_of_descriptor s 2981 permutation3 111 (by rfl)).trans ((lex_skipped s permutation3 110 111 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation3 110) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation3 110 by rw [image3_eq]; rfl))

theorem lex_3_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2982) (Sat.Literal.pos 2981) (Sat.Literal.pos 110) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation3 110 (assignment s)
    (Sat.Literal.pos 2982) (Sat.Literal.pos 2981) (Sat.Literal.pos 110) (Sat.Literal.pos 118) (positive_of_descriptor s 2982 (.lex permutation3 110) (by rfl)) (lex_3_110_prefix s) (positive_select s 110) (lex_3_110_image s)

theorem lex_3_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.pos 110), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation3 110 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2981) (Sat.Literal.pos 110) (Sat.Literal.pos 118) (lex_3_110_prefix s) (positive_select s 110) (lex_3_110_image s)

theorem lex_3_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.pos 2981)] :=
  (lex_3_110_gate s).prop _ (List.Mem.head _)

theorem lex_3_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.neg 110), (Sat.Literal.pos 118)] :=
  (lex_3_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.pos 110), (Sat.Literal.neg 118)] :=
  (lex_3_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.neg 110), (Sat.Literal.neg 118), (Sat.Literal.pos 2982)] :=
  (lex_3_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2981), (Sat.Literal.pos 110), (Sat.Literal.pos 118), (Sat.Literal.pos 2982)] :=
  (lex_3_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2982) = lexBefore s permutation3 109 := by
  exact (positive_lex_of_descriptor s 2982 permutation3 110 (by rfl)).trans ((lex_skipped s permutation3 109 110 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation3 109) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation3 109 by rw [image3_eq]; rfl))

theorem lex_3_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2983) (Sat.Literal.pos 2982) (Sat.Literal.pos 109) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation3 109 (assignment s)
    (Sat.Literal.pos 2983) (Sat.Literal.pos 2982) (Sat.Literal.pos 109) (Sat.Literal.pos 117) (positive_of_descriptor s 2983 (.lex permutation3 109) (by rfl)) (lex_3_109_prefix s) (positive_select s 109) (lex_3_109_image s)

theorem lex_3_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.pos 109), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation3 109 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2982) (Sat.Literal.pos 109) (Sat.Literal.pos 117) (lex_3_109_prefix s) (positive_select s 109) (lex_3_109_image s)

theorem lex_3_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.pos 2982)] :=
  (lex_3_109_gate s).prop _ (List.Mem.head _)

theorem lex_3_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.neg 109), (Sat.Literal.pos 117)] :=
  (lex_3_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.pos 109), (Sat.Literal.neg 117)] :=
  (lex_3_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.neg 109), (Sat.Literal.neg 117), (Sat.Literal.pos 2983)] :=
  (lex_3_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2982), (Sat.Literal.pos 109), (Sat.Literal.pos 117), (Sat.Literal.pos 2983)] :=
  (lex_3_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2983) = lexBefore s permutation3 108 := by
  exact (positive_lex_of_descriptor s 2983 permutation3 109 (by rfl)).trans ((lex_skipped s permutation3 108 109 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation3 108) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation3 108 by rw [image3_eq]; rfl))

theorem lex_3_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2984) (Sat.Literal.pos 2983) (Sat.Literal.pos 108) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation3 108 (assignment s)
    (Sat.Literal.pos 2984) (Sat.Literal.pos 2983) (Sat.Literal.pos 108) (Sat.Literal.pos 116) (positive_of_descriptor s 2984 (.lex permutation3 108) (by rfl)) (lex_3_108_prefix s) (positive_select s 108) (lex_3_108_image s)

theorem lex_3_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.pos 108), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation3 108 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2983) (Sat.Literal.pos 108) (Sat.Literal.pos 116) (lex_3_108_prefix s) (positive_select s 108) (lex_3_108_image s)

theorem lex_3_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.pos 2983)] :=
  (lex_3_108_gate s).prop _ (List.Mem.head _)

theorem lex_3_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.neg 108), (Sat.Literal.pos 116)] :=
  (lex_3_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.pos 108), (Sat.Literal.neg 116)] :=
  (lex_3_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.neg 108), (Sat.Literal.neg 116), (Sat.Literal.pos 2984)] :=
  (lex_3_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2983), (Sat.Literal.pos 108), (Sat.Literal.pos 116), (Sat.Literal.pos 2984)] :=
  (lex_3_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2984) = lexBefore s permutation3 107 := by
  exact (positive_lex_of_descriptor s 2984 permutation3 108 (by rfl)).trans ((lex_skipped s permutation3 107 108 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation3 107) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation3 107 by rw [image3_eq]; rfl))

theorem lex_3_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2985) (Sat.Literal.pos 2984) (Sat.Literal.pos 107) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation3 107 (assignment s)
    (Sat.Literal.pos 2985) (Sat.Literal.pos 2984) (Sat.Literal.pos 107) (Sat.Literal.pos 115) (positive_of_descriptor s 2985 (.lex permutation3 107) (by rfl)) (lex_3_107_prefix s) (positive_select s 107) (lex_3_107_image s)

theorem lex_3_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.pos 107), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation3 107 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2984) (Sat.Literal.pos 107) (Sat.Literal.pos 115) (lex_3_107_prefix s) (positive_select s 107) (lex_3_107_image s)

theorem lex_3_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.pos 2984)] :=
  (lex_3_107_gate s).prop _ (List.Mem.head _)

theorem lex_3_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.neg 107), (Sat.Literal.pos 115)] :=
  (lex_3_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.pos 107), (Sat.Literal.neg 115)] :=
  (lex_3_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.neg 107), (Sat.Literal.neg 115), (Sat.Literal.pos 2985)] :=
  (lex_3_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2984), (Sat.Literal.pos 107), (Sat.Literal.pos 115), (Sat.Literal.pos 2985)] :=
  (lex_3_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2985) = lexBefore s permutation3 106 := by
  exact (positive_lex_of_descriptor s 2985 permutation3 107 (by rfl)).trans ((lex_skipped s permutation3 106 107 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation3 106) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation3 106 by rw [image3_eq]; rfl))

theorem lex_3_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2986) (Sat.Literal.pos 2985) (Sat.Literal.pos 106) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation3 106 (assignment s)
    (Sat.Literal.pos 2986) (Sat.Literal.pos 2985) (Sat.Literal.pos 106) (Sat.Literal.pos 114) (positive_of_descriptor s 2986 (.lex permutation3 106) (by rfl)) (lex_3_106_prefix s) (positive_select s 106) (lex_3_106_image s)

theorem lex_3_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.pos 106), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation3 106 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2985) (Sat.Literal.pos 106) (Sat.Literal.pos 114) (lex_3_106_prefix s) (positive_select s 106) (lex_3_106_image s)

theorem lex_3_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.pos 2985)] :=
  (lex_3_106_gate s).prop _ (List.Mem.head _)

theorem lex_3_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.neg 106), (Sat.Literal.pos 114)] :=
  (lex_3_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.pos 106), (Sat.Literal.neg 114)] :=
  (lex_3_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.neg 106), (Sat.Literal.neg 114), (Sat.Literal.pos 2986)] :=
  (lex_3_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2985), (Sat.Literal.pos 106), (Sat.Literal.pos 114), (Sat.Literal.pos 2986)] :=
  (lex_3_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2986) = lexBefore s permutation3 105 := by
  exact (positive_lex_of_descriptor s 2986 permutation3 106 (by rfl)).trans ((lex_skipped s permutation3 105 106 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation3 105) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation3 105 by rw [image3_eq]; rfl))

theorem lex_3_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2987) (Sat.Literal.pos 2986) (Sat.Literal.pos 105) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation3 105 (assignment s)
    (Sat.Literal.pos 2987) (Sat.Literal.pos 2986) (Sat.Literal.pos 105) (Sat.Literal.pos 113) (positive_of_descriptor s 2987 (.lex permutation3 105) (by rfl)) (lex_3_105_prefix s) (positive_select s 105) (lex_3_105_image s)

theorem lex_3_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.pos 105), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation3 105 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2986) (Sat.Literal.pos 105) (Sat.Literal.pos 113) (lex_3_105_prefix s) (positive_select s 105) (lex_3_105_image s)

theorem lex_3_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.pos 2986)] :=
  (lex_3_105_gate s).prop _ (List.Mem.head _)

theorem lex_3_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.neg 105), (Sat.Literal.pos 113)] :=
  (lex_3_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.pos 105), (Sat.Literal.neg 113)] :=
  (lex_3_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.neg 105), (Sat.Literal.neg 113), (Sat.Literal.pos 2987)] :=
  (lex_3_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2986), (Sat.Literal.pos 105), (Sat.Literal.pos 113), (Sat.Literal.pos 2987)] :=
  (lex_3_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2987) = lexBefore s permutation3 104 := by
  exact (positive_lex_of_descriptor s 2987 permutation3 105 (by rfl)).trans ((lex_skipped s permutation3 104 105 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation3 104) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation3 104 by rw [image3_eq]; rfl))

theorem lex_3_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2988) (Sat.Literal.pos 2987) (Sat.Literal.pos 104) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation3 104 (assignment s)
    (Sat.Literal.pos 2988) (Sat.Literal.pos 2987) (Sat.Literal.pos 104) (Sat.Literal.pos 112) (positive_of_descriptor s 2988 (.lex permutation3 104) (by rfl)) (lex_3_104_prefix s) (positive_select s 104) (lex_3_104_image s)

theorem lex_3_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.pos 104), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation3 104 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2987) (Sat.Literal.pos 104) (Sat.Literal.pos 112) (lex_3_104_prefix s) (positive_select s 104) (lex_3_104_image s)

theorem lex_3_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.pos 2987)] :=
  (lex_3_104_gate s).prop _ (List.Mem.head _)

theorem lex_3_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.neg 104), (Sat.Literal.pos 112)] :=
  (lex_3_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.pos 104), (Sat.Literal.neg 112)] :=
  (lex_3_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.neg 104), (Sat.Literal.neg 112), (Sat.Literal.pos 2988)] :=
  (lex_3_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2987), (Sat.Literal.pos 104), (Sat.Literal.pos 112), (Sat.Literal.pos 2988)] :=
  (lex_3_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2988) = lexBefore s permutation3 87 := by
  exact (positive_lex_of_descriptor s 2988 permutation3 104 (by rfl)).trans ((lex_skipped s permutation3 87 104 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 88 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation3 87) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation3 87 by rw [image3_eq]; rfl))

theorem lex_3_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2989) (Sat.Literal.pos 2988) (Sat.Literal.pos 87) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation3 87 (assignment s)
    (Sat.Literal.pos 2989) (Sat.Literal.pos 2988) (Sat.Literal.pos 87) (Sat.Literal.pos 79) (positive_of_descriptor s 2989 (.lex permutation3 87) (by rfl)) (lex_3_87_prefix s) (positive_select s 87) (lex_3_87_image s)

theorem lex_3_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.pos 87), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation3 87 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2988) (Sat.Literal.pos 87) (Sat.Literal.pos 79) (lex_3_87_prefix s) (positive_select s 87) (lex_3_87_image s)

theorem lex_3_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.pos 2988)] :=
  (lex_3_87_gate s).prop _ (List.Mem.head _)

theorem lex_3_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.neg 87), (Sat.Literal.pos 79)] :=
  (lex_3_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.pos 87), (Sat.Literal.neg 79)] :=
  (lex_3_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.neg 87), (Sat.Literal.neg 79), (Sat.Literal.pos 2989)] :=
  (lex_3_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2988), (Sat.Literal.pos 87), (Sat.Literal.pos 79), (Sat.Literal.pos 2989)] :=
  (lex_3_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2989) = lexBefore s permutation3 86 := by
  exact (positive_lex_of_descriptor s 2989 permutation3 87 (by rfl)).trans ((lex_skipped s permutation3 86 87 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation3 86) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation3 86 by rw [image3_eq]; rfl))

theorem lex_3_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2990) (Sat.Literal.pos 2989) (Sat.Literal.pos 86) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation3 86 (assignment s)
    (Sat.Literal.pos 2990) (Sat.Literal.pos 2989) (Sat.Literal.pos 86) (Sat.Literal.pos 78) (positive_of_descriptor s 2990 (.lex permutation3 86) (by rfl)) (lex_3_86_prefix s) (positive_select s 86) (lex_3_86_image s)

theorem lex_3_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.pos 86), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation3 86 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2989) (Sat.Literal.pos 86) (Sat.Literal.pos 78) (lex_3_86_prefix s) (positive_select s 86) (lex_3_86_image s)

theorem lex_3_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.pos 2989)] :=
  (lex_3_86_gate s).prop _ (List.Mem.head _)

theorem lex_3_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.neg 86), (Sat.Literal.pos 78)] :=
  (lex_3_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.pos 86), (Sat.Literal.neg 78)] :=
  (lex_3_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.neg 86), (Sat.Literal.neg 78), (Sat.Literal.pos 2990)] :=
  (lex_3_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2989), (Sat.Literal.pos 86), (Sat.Literal.pos 78), (Sat.Literal.pos 2990)] :=
  (lex_3_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2990) = lexBefore s permutation3 85 := by
  exact (positive_lex_of_descriptor s 2990 permutation3 86 (by rfl)).trans ((lex_skipped s permutation3 85 86 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation3 85) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation3 85 by rw [image3_eq]; rfl))

theorem lex_3_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2991) (Sat.Literal.pos 2990) (Sat.Literal.pos 85) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation3 85 (assignment s)
    (Sat.Literal.pos 2991) (Sat.Literal.pos 2990) (Sat.Literal.pos 85) (Sat.Literal.pos 77) (positive_of_descriptor s 2991 (.lex permutation3 85) (by rfl)) (lex_3_85_prefix s) (positive_select s 85) (lex_3_85_image s)

theorem lex_3_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.pos 85), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation3 85 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2990) (Sat.Literal.pos 85) (Sat.Literal.pos 77) (lex_3_85_prefix s) (positive_select s 85) (lex_3_85_image s)

theorem lex_3_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.pos 2990)] :=
  (lex_3_85_gate s).prop _ (List.Mem.head _)

theorem lex_3_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.neg 85), (Sat.Literal.pos 77)] :=
  (lex_3_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.pos 85), (Sat.Literal.neg 77)] :=
  (lex_3_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.neg 85), (Sat.Literal.neg 77), (Sat.Literal.pos 2991)] :=
  (lex_3_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2990), (Sat.Literal.pos 85), (Sat.Literal.pos 77), (Sat.Literal.pos 2991)] :=
  (lex_3_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2991) = lexBefore s permutation3 84 := by
  exact (positive_lex_of_descriptor s 2991 permutation3 85 (by rfl)).trans ((lex_skipped s permutation3 84 85 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation3 84) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation3 84 by rw [image3_eq]; rfl))

theorem lex_3_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2992) (Sat.Literal.pos 2991) (Sat.Literal.pos 84) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation3 84 (assignment s)
    (Sat.Literal.pos 2992) (Sat.Literal.pos 2991) (Sat.Literal.pos 84) (Sat.Literal.pos 76) (positive_of_descriptor s 2992 (.lex permutation3 84) (by rfl)) (lex_3_84_prefix s) (positive_select s 84) (lex_3_84_image s)

theorem lex_3_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.pos 84), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation3 84 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2991) (Sat.Literal.pos 84) (Sat.Literal.pos 76) (lex_3_84_prefix s) (positive_select s 84) (lex_3_84_image s)

theorem lex_3_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.pos 2991)] :=
  (lex_3_84_gate s).prop _ (List.Mem.head _)

theorem lex_3_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.neg 84), (Sat.Literal.pos 76)] :=
  (lex_3_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.pos 84), (Sat.Literal.neg 76)] :=
  (lex_3_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.neg 84), (Sat.Literal.neg 76), (Sat.Literal.pos 2992)] :=
  (lex_3_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2991), (Sat.Literal.pos 84), (Sat.Literal.pos 76), (Sat.Literal.pos 2992)] :=
  (lex_3_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2992) = lexBefore s permutation3 83 := by
  exact (positive_lex_of_descriptor s 2992 permutation3 84 (by rfl)).trans ((lex_skipped s permutation3 83 84 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation3 83) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation3 83 by rw [image3_eq]; rfl))

theorem lex_3_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2993) (Sat.Literal.pos 2992) (Sat.Literal.pos 83) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation3 83 (assignment s)
    (Sat.Literal.pos 2993) (Sat.Literal.pos 2992) (Sat.Literal.pos 83) (Sat.Literal.pos 75) (positive_of_descriptor s 2993 (.lex permutation3 83) (by rfl)) (lex_3_83_prefix s) (positive_select s 83) (lex_3_83_image s)

theorem lex_3_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.pos 83), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation3 83 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2992) (Sat.Literal.pos 83) (Sat.Literal.pos 75) (lex_3_83_prefix s) (positive_select s 83) (lex_3_83_image s)

theorem lex_3_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.pos 2992)] :=
  (lex_3_83_gate s).prop _ (List.Mem.head _)

theorem lex_3_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.neg 83), (Sat.Literal.pos 75)] :=
  (lex_3_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.pos 83), (Sat.Literal.neg 75)] :=
  (lex_3_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.neg 83), (Sat.Literal.neg 75), (Sat.Literal.pos 2993)] :=
  (lex_3_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2992), (Sat.Literal.pos 83), (Sat.Literal.pos 75), (Sat.Literal.pos 2993)] :=
  (lex_3_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2993) = lexBefore s permutation3 82 := by
  exact (positive_lex_of_descriptor s 2993 permutation3 83 (by rfl)).trans ((lex_skipped s permutation3 82 83 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation3 82) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation3 82 by rw [image3_eq]; rfl))

theorem lex_3_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2994) (Sat.Literal.pos 2993) (Sat.Literal.pos 82) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation3 82 (assignment s)
    (Sat.Literal.pos 2994) (Sat.Literal.pos 2993) (Sat.Literal.pos 82) (Sat.Literal.pos 74) (positive_of_descriptor s 2994 (.lex permutation3 82) (by rfl)) (lex_3_82_prefix s) (positive_select s 82) (lex_3_82_image s)

theorem lex_3_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.pos 82), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation3 82 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2993) (Sat.Literal.pos 82) (Sat.Literal.pos 74) (lex_3_82_prefix s) (positive_select s 82) (lex_3_82_image s)

theorem lex_3_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.pos 2993)] :=
  (lex_3_82_gate s).prop _ (List.Mem.head _)

theorem lex_3_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.neg 82), (Sat.Literal.pos 74)] :=
  (lex_3_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.pos 82), (Sat.Literal.neg 74)] :=
  (lex_3_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.neg 82), (Sat.Literal.neg 74), (Sat.Literal.pos 2994)] :=
  (lex_3_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2993), (Sat.Literal.pos 82), (Sat.Literal.pos 74), (Sat.Literal.pos 2994)] :=
  (lex_3_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2994) = lexBefore s permutation3 81 := by
  exact (positive_lex_of_descriptor s 2994 permutation3 82 (by rfl)).trans ((lex_skipped s permutation3 81 82 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation3 81) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation3 81 by rw [image3_eq]; rfl))

theorem lex_3_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2995) (Sat.Literal.pos 2994) (Sat.Literal.pos 81) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation3 81 (assignment s)
    (Sat.Literal.pos 2995) (Sat.Literal.pos 2994) (Sat.Literal.pos 81) (Sat.Literal.pos 73) (positive_of_descriptor s 2995 (.lex permutation3 81) (by rfl)) (lex_3_81_prefix s) (positive_select s 81) (lex_3_81_image s)

theorem lex_3_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.pos 81), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation3 81 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2994) (Sat.Literal.pos 81) (Sat.Literal.pos 73) (lex_3_81_prefix s) (positive_select s 81) (lex_3_81_image s)

theorem lex_3_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.pos 2994)] :=
  (lex_3_81_gate s).prop _ (List.Mem.head _)

theorem lex_3_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.neg 81), (Sat.Literal.pos 73)] :=
  (lex_3_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.pos 81), (Sat.Literal.neg 73)] :=
  (lex_3_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.neg 81), (Sat.Literal.neg 73), (Sat.Literal.pos 2995)] :=
  (lex_3_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2994), (Sat.Literal.pos 81), (Sat.Literal.pos 73), (Sat.Literal.pos 2995)] :=
  (lex_3_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2995) = lexBefore s permutation3 80 := by
  exact (positive_lex_of_descriptor s 2995 permutation3 81 (by rfl)).trans ((lex_skipped s permutation3 80 81 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation3 80) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation3 80 by rw [image3_eq]; rfl))

theorem lex_3_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2996) (Sat.Literal.pos 2995) (Sat.Literal.pos 80) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation3 80 (assignment s)
    (Sat.Literal.pos 2996) (Sat.Literal.pos 2995) (Sat.Literal.pos 80) (Sat.Literal.pos 72) (positive_of_descriptor s 2996 (.lex permutation3 80) (by rfl)) (lex_3_80_prefix s) (positive_select s 80) (lex_3_80_image s)

theorem lex_3_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.pos 80), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation3 80 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2995) (Sat.Literal.pos 80) (Sat.Literal.pos 72) (lex_3_80_prefix s) (positive_select s 80) (lex_3_80_image s)

theorem lex_3_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.pos 2995)] :=
  (lex_3_80_gate s).prop _ (List.Mem.head _)

theorem lex_3_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.neg 80), (Sat.Literal.pos 72)] :=
  (lex_3_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.pos 80), (Sat.Literal.neg 72)] :=
  (lex_3_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.neg 80), (Sat.Literal.neg 72), (Sat.Literal.pos 2996)] :=
  (lex_3_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2995), (Sat.Literal.pos 80), (Sat.Literal.pos 72), (Sat.Literal.pos 2996)] :=
  (lex_3_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2996) = lexBefore s permutation3 79 := by
  exact (positive_lex_of_descriptor s 2996 permutation3 80 (by rfl)).trans ((lex_skipped s permutation3 79 80 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation3 79) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation3 79 by rw [image3_eq]; rfl))

theorem lex_3_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2997) (Sat.Literal.pos 2996) (Sat.Literal.pos 79) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation3 79 (assignment s)
    (Sat.Literal.pos 2997) (Sat.Literal.pos 2996) (Sat.Literal.pos 79) (Sat.Literal.pos 87) (positive_of_descriptor s 2997 (.lex permutation3 79) (by rfl)) (lex_3_79_prefix s) (positive_select s 79) (lex_3_79_image s)

theorem lex_3_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.pos 79), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation3 79 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2996) (Sat.Literal.pos 79) (Sat.Literal.pos 87) (lex_3_79_prefix s) (positive_select s 79) (lex_3_79_image s)

theorem lex_3_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.pos 2996)] :=
  (lex_3_79_gate s).prop _ (List.Mem.head _)

theorem lex_3_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.neg 79), (Sat.Literal.pos 87)] :=
  (lex_3_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.pos 79), (Sat.Literal.neg 87)] :=
  (lex_3_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.neg 79), (Sat.Literal.neg 87), (Sat.Literal.pos 2997)] :=
  (lex_3_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2996), (Sat.Literal.pos 79), (Sat.Literal.pos 87), (Sat.Literal.pos 2997)] :=
  (lex_3_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2997) = lexBefore s permutation3 78 := by
  exact (positive_lex_of_descriptor s 2997 permutation3 79 (by rfl)).trans ((lex_skipped s permutation3 78 79 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation3 78) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation3 78 by rw [image3_eq]; rfl))

theorem lex_3_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2998) (Sat.Literal.pos 2997) (Sat.Literal.pos 78) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation3 78 (assignment s)
    (Sat.Literal.pos 2998) (Sat.Literal.pos 2997) (Sat.Literal.pos 78) (Sat.Literal.pos 86) (positive_of_descriptor s 2998 (.lex permutation3 78) (by rfl)) (lex_3_78_prefix s) (positive_select s 78) (lex_3_78_image s)

theorem lex_3_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.pos 78), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation3 78 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2997) (Sat.Literal.pos 78) (Sat.Literal.pos 86) (lex_3_78_prefix s) (positive_select s 78) (lex_3_78_image s)

theorem lex_3_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.pos 2997)] :=
  (lex_3_78_gate s).prop _ (List.Mem.head _)

theorem lex_3_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.neg 78), (Sat.Literal.pos 86)] :=
  (lex_3_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.pos 78), (Sat.Literal.neg 86)] :=
  (lex_3_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.neg 78), (Sat.Literal.neg 86), (Sat.Literal.pos 2998)] :=
  (lex_3_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2997), (Sat.Literal.pos 78), (Sat.Literal.pos 86), (Sat.Literal.pos 2998)] :=
  (lex_3_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2998) = lexBefore s permutation3 77 := by
  exact (positive_lex_of_descriptor s 2998 permutation3 78 (by rfl)).trans ((lex_skipped s permutation3 77 78 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation3 77) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation3 77 by rw [image3_eq]; rfl))

theorem lex_3_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2999) (Sat.Literal.pos 2998) (Sat.Literal.pos 77) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation3 77 (assignment s)
    (Sat.Literal.pos 2999) (Sat.Literal.pos 2998) (Sat.Literal.pos 77) (Sat.Literal.pos 85) (positive_of_descriptor s 2999 (.lex permutation3 77) (by rfl)) (lex_3_77_prefix s) (positive_select s 77) (lex_3_77_image s)

theorem lex_3_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.pos 77), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation3 77 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2998) (Sat.Literal.pos 77) (Sat.Literal.pos 85) (lex_3_77_prefix s) (positive_select s 77) (lex_3_77_image s)

theorem lex_3_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.pos 2998)] :=
  (lex_3_77_gate s).prop _ (List.Mem.head _)

theorem lex_3_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.neg 77), (Sat.Literal.pos 85)] :=
  (lex_3_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.pos 77), (Sat.Literal.neg 85)] :=
  (lex_3_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.neg 77), (Sat.Literal.neg 85), (Sat.Literal.pos 2999)] :=
  (lex_3_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2998), (Sat.Literal.pos 77), (Sat.Literal.pos 85), (Sat.Literal.pos 2999)] :=
  (lex_3_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2999) = lexBefore s permutation3 76 := by
  exact (positive_lex_of_descriptor s 2999 permutation3 77 (by rfl)).trans ((lex_skipped s permutation3 76 77 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation3 76) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation3 76 by rw [image3_eq]; rfl))

theorem lex_3_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3000) (Sat.Literal.pos 2999) (Sat.Literal.pos 76) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation3 76 (assignment s)
    (Sat.Literal.pos 3000) (Sat.Literal.pos 2999) (Sat.Literal.pos 76) (Sat.Literal.pos 84) (positive_of_descriptor s 3000 (.lex permutation3 76) (by rfl)) (lex_3_76_prefix s) (positive_select s 76) (lex_3_76_image s)

theorem lex_3_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.pos 76), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation3 76 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2999) (Sat.Literal.pos 76) (Sat.Literal.pos 84) (lex_3_76_prefix s) (positive_select s 76) (lex_3_76_image s)

theorem lex_3_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.pos 2999)] :=
  (lex_3_76_gate s).prop _ (List.Mem.head _)

theorem lex_3_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.neg 76), (Sat.Literal.pos 84)] :=
  (lex_3_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.pos 76), (Sat.Literal.neg 84)] :=
  (lex_3_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.neg 76), (Sat.Literal.neg 84), (Sat.Literal.pos 3000)] :=
  (lex_3_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2999), (Sat.Literal.pos 76), (Sat.Literal.pos 84), (Sat.Literal.pos 3000)] :=
  (lex_3_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3000) = lexBefore s permutation3 75 := by
  exact (positive_lex_of_descriptor s 3000 permutation3 76 (by rfl)).trans ((lex_skipped s permutation3 75 76 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation3 75) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation3 75 by rw [image3_eq]; rfl))

theorem lex_3_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3001) (Sat.Literal.pos 3000) (Sat.Literal.pos 75) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation3 75 (assignment s)
    (Sat.Literal.pos 3001) (Sat.Literal.pos 3000) (Sat.Literal.pos 75) (Sat.Literal.pos 83) (positive_of_descriptor s 3001 (.lex permutation3 75) (by rfl)) (lex_3_75_prefix s) (positive_select s 75) (lex_3_75_image s)

theorem lex_3_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.pos 75), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation3 75 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3000) (Sat.Literal.pos 75) (Sat.Literal.pos 83) (lex_3_75_prefix s) (positive_select s 75) (lex_3_75_image s)

theorem lex_3_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.pos 3000)] :=
  (lex_3_75_gate s).prop _ (List.Mem.head _)

theorem lex_3_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.neg 75), (Sat.Literal.pos 83)] :=
  (lex_3_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.pos 75), (Sat.Literal.neg 83)] :=
  (lex_3_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.neg 75), (Sat.Literal.neg 83), (Sat.Literal.pos 3001)] :=
  (lex_3_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3000), (Sat.Literal.pos 75), (Sat.Literal.pos 83), (Sat.Literal.pos 3001)] :=
  (lex_3_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3001) = lexBefore s permutation3 74 := by
  exact (positive_lex_of_descriptor s 3001 permutation3 75 (by rfl)).trans ((lex_skipped s permutation3 74 75 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation3 74) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation3 74 by rw [image3_eq]; rfl))

theorem lex_3_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3002) (Sat.Literal.pos 3001) (Sat.Literal.pos 74) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation3 74 (assignment s)
    (Sat.Literal.pos 3002) (Sat.Literal.pos 3001) (Sat.Literal.pos 74) (Sat.Literal.pos 82) (positive_of_descriptor s 3002 (.lex permutation3 74) (by rfl)) (lex_3_74_prefix s) (positive_select s 74) (lex_3_74_image s)

theorem lex_3_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.pos 74), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation3 74 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3001) (Sat.Literal.pos 74) (Sat.Literal.pos 82) (lex_3_74_prefix s) (positive_select s 74) (lex_3_74_image s)

theorem lex_3_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.pos 3001)] :=
  (lex_3_74_gate s).prop _ (List.Mem.head _)

theorem lex_3_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.neg 74), (Sat.Literal.pos 82)] :=
  (lex_3_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.pos 74), (Sat.Literal.neg 82)] :=
  (lex_3_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.neg 74), (Sat.Literal.neg 82), (Sat.Literal.pos 3002)] :=
  (lex_3_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3001), (Sat.Literal.pos 74), (Sat.Literal.pos 82), (Sat.Literal.pos 3002)] :=
  (lex_3_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3002) = lexBefore s permutation3 73 := by
  exact (positive_lex_of_descriptor s 3002 permutation3 74 (by rfl)).trans ((lex_skipped s permutation3 73 74 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation3 73) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation3 73 by rw [image3_eq]; rfl))

theorem lex_3_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3003) (Sat.Literal.pos 3002) (Sat.Literal.pos 73) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation3 73 (assignment s)
    (Sat.Literal.pos 3003) (Sat.Literal.pos 3002) (Sat.Literal.pos 73) (Sat.Literal.pos 81) (positive_of_descriptor s 3003 (.lex permutation3 73) (by rfl)) (lex_3_73_prefix s) (positive_select s 73) (lex_3_73_image s)

theorem lex_3_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.pos 73), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation3 73 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3002) (Sat.Literal.pos 73) (Sat.Literal.pos 81) (lex_3_73_prefix s) (positive_select s 73) (lex_3_73_image s)

theorem lex_3_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.pos 3002)] :=
  (lex_3_73_gate s).prop _ (List.Mem.head _)

theorem lex_3_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.neg 73), (Sat.Literal.pos 81)] :=
  (lex_3_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.pos 73), (Sat.Literal.neg 81)] :=
  (lex_3_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.neg 73), (Sat.Literal.neg 81), (Sat.Literal.pos 3003)] :=
  (lex_3_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3002), (Sat.Literal.pos 73), (Sat.Literal.pos 81), (Sat.Literal.pos 3003)] :=
  (lex_3_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3003) = lexBefore s permutation3 72 := by
  exact (positive_lex_of_descriptor s 3003 permutation3 73 (by rfl)).trans ((lex_skipped s permutation3 72 73 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation3 72) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation3 72 by rw [image3_eq]; rfl))

theorem lex_3_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3004) (Sat.Literal.pos 3003) (Sat.Literal.pos 72) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation3 72 (assignment s)
    (Sat.Literal.pos 3004) (Sat.Literal.pos 3003) (Sat.Literal.pos 72) (Sat.Literal.pos 80) (positive_of_descriptor s 3004 (.lex permutation3 72) (by rfl)) (lex_3_72_prefix s) (positive_select s 72) (lex_3_72_image s)

theorem lex_3_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.pos 72), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation3 72 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3003) (Sat.Literal.pos 72) (Sat.Literal.pos 80) (lex_3_72_prefix s) (positive_select s 72) (lex_3_72_image s)

theorem lex_3_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.pos 3003)] :=
  (lex_3_72_gate s).prop _ (List.Mem.head _)

theorem lex_3_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.neg 72), (Sat.Literal.pos 80)] :=
  (lex_3_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.pos 72), (Sat.Literal.neg 80)] :=
  (lex_3_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.neg 72), (Sat.Literal.neg 80), (Sat.Literal.pos 3004)] :=
  (lex_3_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3003), (Sat.Literal.pos 72), (Sat.Literal.pos 80), (Sat.Literal.pos 3004)] :=
  (lex_3_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3004) = lexBefore s permutation3 55 := by
  exact (positive_lex_of_descriptor s 3004 permutation3 72 (by rfl)).trans ((lex_skipped s permutation3 55 72 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 56 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation3 55) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation3 55 by rw [image3_eq]; rfl))

theorem lex_3_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3005) (Sat.Literal.pos 3004) (Sat.Literal.pos 55) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation3 55 (assignment s)
    (Sat.Literal.pos 3005) (Sat.Literal.pos 3004) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (positive_of_descriptor s 3005 (.lex permutation3 55) (by rfl)) (lex_3_55_prefix s) (positive_select s 55) (lex_3_55_image s)

theorem lex_3_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation3 55 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3004) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (lex_3_55_prefix s) (positive_select s 55) (lex_3_55_image s)

theorem lex_3_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.pos 3004)] :=
  (lex_3_55_gate s).prop _ (List.Mem.head _)

theorem lex_3_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.neg 55), (Sat.Literal.pos 47)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.neg 55), (Sat.Literal.neg 47), (Sat.Literal.pos 3005)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3004), (Sat.Literal.pos 55), (Sat.Literal.pos 47), (Sat.Literal.pos 3005)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3005) = lexBefore s permutation3 54 := by
  exact (positive_lex_of_descriptor s 3005 permutation3 55 (by rfl)).trans ((lex_skipped s permutation3 54 55 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation3 54) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation3 54 by rw [image3_eq]; rfl))

theorem lex_3_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3006) (Sat.Literal.pos 3005) (Sat.Literal.pos 54) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation3 54 (assignment s)
    (Sat.Literal.pos 3006) (Sat.Literal.pos 3005) (Sat.Literal.pos 54) (Sat.Literal.pos 46) (positive_of_descriptor s 3006 (.lex permutation3 54) (by rfl)) (lex_3_54_prefix s) (positive_select s 54) (lex_3_54_image s)

theorem lex_3_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.pos 54), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation3 54 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3005) (Sat.Literal.pos 54) (Sat.Literal.pos 46) (lex_3_54_prefix s) (positive_select s 54) (lex_3_54_image s)

theorem lex_3_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.pos 3005)] :=
  (lex_3_54_gate s).prop _ (List.Mem.head _)

theorem lex_3_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.neg 54), (Sat.Literal.pos 46)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.pos 54), (Sat.Literal.neg 46)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.neg 54), (Sat.Literal.neg 46), (Sat.Literal.pos 3006)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3005), (Sat.Literal.pos 54), (Sat.Literal.pos 46), (Sat.Literal.pos 3006)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3006) = lexBefore s permutation3 53 := by
  exact (positive_lex_of_descriptor s 3006 permutation3 54 (by rfl)).trans ((lex_skipped s permutation3 53 54 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation3 53) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation3 53 by rw [image3_eq]; rfl))

theorem lex_3_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3007) (Sat.Literal.pos 3006) (Sat.Literal.pos 53) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation3 53 (assignment s)
    (Sat.Literal.pos 3007) (Sat.Literal.pos 3006) (Sat.Literal.pos 53) (Sat.Literal.pos 45) (positive_of_descriptor s 3007 (.lex permutation3 53) (by rfl)) (lex_3_53_prefix s) (positive_select s 53) (lex_3_53_image s)

theorem lex_3_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.pos 53), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation3 53 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3006) (Sat.Literal.pos 53) (Sat.Literal.pos 45) (lex_3_53_prefix s) (positive_select s 53) (lex_3_53_image s)

theorem lex_3_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.pos 3006)] :=
  (lex_3_53_gate s).prop _ (List.Mem.head _)

theorem lex_3_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.neg 53), (Sat.Literal.pos 45)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.pos 53), (Sat.Literal.neg 45)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.neg 53), (Sat.Literal.neg 45), (Sat.Literal.pos 3007)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3006), (Sat.Literal.pos 53), (Sat.Literal.pos 45), (Sat.Literal.pos 3007)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3007) = lexBefore s permutation3 52 := by
  exact (positive_lex_of_descriptor s 3007 permutation3 53 (by rfl)).trans ((lex_skipped s permutation3 52 53 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation3 52) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation3 52 by rw [image3_eq]; rfl))

theorem lex_3_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3008) (Sat.Literal.pos 3007) (Sat.Literal.pos 52) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation3 52 (assignment s)
    (Sat.Literal.pos 3008) (Sat.Literal.pos 3007) (Sat.Literal.pos 52) (Sat.Literal.pos 44) (positive_of_descriptor s 3008 (.lex permutation3 52) (by rfl)) (lex_3_52_prefix s) (positive_select s 52) (lex_3_52_image s)

theorem lex_3_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.pos 52), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation3 52 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3007) (Sat.Literal.pos 52) (Sat.Literal.pos 44) (lex_3_52_prefix s) (positive_select s 52) (lex_3_52_image s)

theorem lex_3_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.pos 3007)] :=
  (lex_3_52_gate s).prop _ (List.Mem.head _)

theorem lex_3_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.neg 52), (Sat.Literal.pos 44)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.pos 52), (Sat.Literal.neg 44)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.neg 52), (Sat.Literal.neg 44), (Sat.Literal.pos 3008)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3007), (Sat.Literal.pos 52), (Sat.Literal.pos 44), (Sat.Literal.pos 3008)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3008) = lexBefore s permutation3 51 := by
  exact (positive_lex_of_descriptor s 3008 permutation3 52 (by rfl)).trans ((lex_skipped s permutation3 51 52 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation3 51) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation3 51 by rw [image3_eq]; rfl))

theorem lex_3_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3009) (Sat.Literal.pos 3008) (Sat.Literal.pos 51) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation3 51 (assignment s)
    (Sat.Literal.pos 3009) (Sat.Literal.pos 3008) (Sat.Literal.pos 51) (Sat.Literal.pos 43) (positive_of_descriptor s 3009 (.lex permutation3 51) (by rfl)) (lex_3_51_prefix s) (positive_select s 51) (lex_3_51_image s)

theorem lex_3_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.pos 51), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation3 51 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3008) (Sat.Literal.pos 51) (Sat.Literal.pos 43) (lex_3_51_prefix s) (positive_select s 51) (lex_3_51_image s)

theorem lex_3_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.pos 3008)] :=
  (lex_3_51_gate s).prop _ (List.Mem.head _)

theorem lex_3_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.neg 51), (Sat.Literal.pos 43)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.pos 51), (Sat.Literal.neg 43)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.neg 51), (Sat.Literal.neg 43), (Sat.Literal.pos 3009)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3008), (Sat.Literal.pos 51), (Sat.Literal.pos 43), (Sat.Literal.pos 3009)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3009) = lexBefore s permutation3 50 := by
  exact (positive_lex_of_descriptor s 3009 permutation3 51 (by rfl)).trans ((lex_skipped s permutation3 50 51 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation3 50) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation3 50 by rw [image3_eq]; rfl))

theorem lex_3_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3010) (Sat.Literal.pos 3009) (Sat.Literal.pos 50) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation3 50 (assignment s)
    (Sat.Literal.pos 3010) (Sat.Literal.pos 3009) (Sat.Literal.pos 50) (Sat.Literal.pos 42) (positive_of_descriptor s 3010 (.lex permutation3 50) (by rfl)) (lex_3_50_prefix s) (positive_select s 50) (lex_3_50_image s)

theorem lex_3_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.pos 50), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation3 50 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3009) (Sat.Literal.pos 50) (Sat.Literal.pos 42) (lex_3_50_prefix s) (positive_select s 50) (lex_3_50_image s)

theorem lex_3_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.pos 3009)] :=
  (lex_3_50_gate s).prop _ (List.Mem.head _)

theorem lex_3_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.neg 50), (Sat.Literal.pos 42)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.pos 50), (Sat.Literal.neg 42)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.neg 50), (Sat.Literal.neg 42), (Sat.Literal.pos 3010)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3009), (Sat.Literal.pos 50), (Sat.Literal.pos 42), (Sat.Literal.pos 3010)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3010) = lexBefore s permutation3 49 := by
  exact (positive_lex_of_descriptor s 3010 permutation3 50 (by rfl)).trans ((lex_skipped s permutation3 49 50 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation3 49) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation3 49 by rw [image3_eq]; rfl))

theorem lex_3_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3011) (Sat.Literal.pos 3010) (Sat.Literal.pos 49) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation3 49 (assignment s)
    (Sat.Literal.pos 3011) (Sat.Literal.pos 3010) (Sat.Literal.pos 49) (Sat.Literal.pos 41) (positive_of_descriptor s 3011 (.lex permutation3 49) (by rfl)) (lex_3_49_prefix s) (positive_select s 49) (lex_3_49_image s)

theorem lex_3_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.pos 49), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation3 49 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3010) (Sat.Literal.pos 49) (Sat.Literal.pos 41) (lex_3_49_prefix s) (positive_select s 49) (lex_3_49_image s)

theorem lex_3_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.pos 3010)] :=
  (lex_3_49_gate s).prop _ (List.Mem.head _)

theorem lex_3_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.neg 49), (Sat.Literal.pos 41)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.pos 49), (Sat.Literal.neg 41)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.neg 49), (Sat.Literal.neg 41), (Sat.Literal.pos 3011)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3010), (Sat.Literal.pos 49), (Sat.Literal.pos 41), (Sat.Literal.pos 3011)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3011) = lexBefore s permutation3 48 := by
  exact (positive_lex_of_descriptor s 3011 permutation3 49 (by rfl)).trans ((lex_skipped s permutation3 48 49 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation3 48) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation3 48 by rw [image3_eq]; rfl))

theorem lex_3_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3012) (Sat.Literal.pos 3011) (Sat.Literal.pos 48) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation3 48 (assignment s)
    (Sat.Literal.pos 3012) (Sat.Literal.pos 3011) (Sat.Literal.pos 48) (Sat.Literal.pos 40) (positive_of_descriptor s 3012 (.lex permutation3 48) (by rfl)) (lex_3_48_prefix s) (positive_select s 48) (lex_3_48_image s)

theorem lex_3_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.pos 48), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation3 48 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3011) (Sat.Literal.pos 48) (Sat.Literal.pos 40) (lex_3_48_prefix s) (positive_select s 48) (lex_3_48_image s)

theorem lex_3_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.pos 3011)] :=
  (lex_3_48_gate s).prop _ (List.Mem.head _)

theorem lex_3_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.neg 48), (Sat.Literal.pos 40)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.pos 48), (Sat.Literal.neg 40)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.neg 48), (Sat.Literal.neg 40), (Sat.Literal.pos 3012)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3011), (Sat.Literal.pos 48), (Sat.Literal.pos 40), (Sat.Literal.pos 3012)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3012) = lexBefore s permutation3 47 := by
  exact (positive_lex_of_descriptor s 3012 permutation3 48 (by rfl)).trans ((lex_skipped s permutation3 47 48 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation3 47) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation3 47 by rw [image3_eq]; rfl))

theorem lex_3_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3013) (Sat.Literal.pos 3012) (Sat.Literal.pos 47) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation3 47 (assignment s)
    (Sat.Literal.pos 3013) (Sat.Literal.pos 3012) (Sat.Literal.pos 47) (Sat.Literal.pos 55) (positive_of_descriptor s 3013 (.lex permutation3 47) (by rfl)) (lex_3_47_prefix s) (positive_select s 47) (lex_3_47_image s)

theorem lex_3_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.pos 47), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation3 47 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3012) (Sat.Literal.pos 47) (Sat.Literal.pos 55) (lex_3_47_prefix s) (positive_select s 47) (lex_3_47_image s)

theorem lex_3_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.pos 3012)] :=
  (lex_3_47_gate s).prop _ (List.Mem.head _)

theorem lex_3_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.neg 47), (Sat.Literal.pos 55)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.pos 47), (Sat.Literal.neg 55)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.neg 47), (Sat.Literal.neg 55), (Sat.Literal.pos 3013)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3012), (Sat.Literal.pos 47), (Sat.Literal.pos 55), (Sat.Literal.pos 3013)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3013) = lexBefore s permutation3 46 := by
  exact (positive_lex_of_descriptor s 3013 permutation3 47 (by rfl)).trans ((lex_skipped s permutation3 46 47 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation3 46) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation3 46 by rw [image3_eq]; rfl))

theorem lex_3_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3014) (Sat.Literal.pos 3013) (Sat.Literal.pos 46) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation3 46 (assignment s)
    (Sat.Literal.pos 3014) (Sat.Literal.pos 3013) (Sat.Literal.pos 46) (Sat.Literal.pos 54) (positive_of_descriptor s 3014 (.lex permutation3 46) (by rfl)) (lex_3_46_prefix s) (positive_select s 46) (lex_3_46_image s)

theorem lex_3_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.pos 46), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation3 46 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3013) (Sat.Literal.pos 46) (Sat.Literal.pos 54) (lex_3_46_prefix s) (positive_select s 46) (lex_3_46_image s)

theorem lex_3_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.pos 3013)] :=
  (lex_3_46_gate s).prop _ (List.Mem.head _)

theorem lex_3_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.neg 46), (Sat.Literal.pos 54)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.pos 46), (Sat.Literal.neg 54)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.neg 46), (Sat.Literal.neg 54), (Sat.Literal.pos 3014)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3013), (Sat.Literal.pos 46), (Sat.Literal.pos 54), (Sat.Literal.pos 3014)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3014) = lexBefore s permutation3 45 := by
  exact (positive_lex_of_descriptor s 3014 permutation3 46 (by rfl)).trans ((lex_skipped s permutation3 45 46 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation3 45) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation3 45 by rw [image3_eq]; rfl))

theorem lex_3_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3015) (Sat.Literal.pos 3014) (Sat.Literal.pos 45) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation3 45 (assignment s)
    (Sat.Literal.pos 3015) (Sat.Literal.pos 3014) (Sat.Literal.pos 45) (Sat.Literal.pos 53) (positive_of_descriptor s 3015 (.lex permutation3 45) (by rfl)) (lex_3_45_prefix s) (positive_select s 45) (lex_3_45_image s)

theorem lex_3_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.pos 45), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation3 45 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3014) (Sat.Literal.pos 45) (Sat.Literal.pos 53) (lex_3_45_prefix s) (positive_select s 45) (lex_3_45_image s)

theorem lex_3_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.pos 3014)] :=
  (lex_3_45_gate s).prop _ (List.Mem.head _)

theorem lex_3_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.neg 45), (Sat.Literal.pos 53)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.pos 45), (Sat.Literal.neg 53)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.neg 45), (Sat.Literal.neg 53), (Sat.Literal.pos 3015)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3014), (Sat.Literal.pos 45), (Sat.Literal.pos 53), (Sat.Literal.pos 3015)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3015) = lexBefore s permutation3 44 := by
  exact (positive_lex_of_descriptor s 3015 permutation3 45 (by rfl)).trans ((lex_skipped s permutation3 44 45 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation3 44) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation3 44 by rw [image3_eq]; rfl))

theorem lex_3_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3016) (Sat.Literal.pos 3015) (Sat.Literal.pos 44) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation3 44 (assignment s)
    (Sat.Literal.pos 3016) (Sat.Literal.pos 3015) (Sat.Literal.pos 44) (Sat.Literal.pos 52) (positive_of_descriptor s 3016 (.lex permutation3 44) (by rfl)) (lex_3_44_prefix s) (positive_select s 44) (lex_3_44_image s)

theorem lex_3_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.pos 44), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation3 44 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3015) (Sat.Literal.pos 44) (Sat.Literal.pos 52) (lex_3_44_prefix s) (positive_select s 44) (lex_3_44_image s)

theorem lex_3_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.pos 3015)] :=
  (lex_3_44_gate s).prop _ (List.Mem.head _)

theorem lex_3_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.neg 44), (Sat.Literal.pos 52)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.pos 44), (Sat.Literal.neg 52)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.neg 44), (Sat.Literal.neg 52), (Sat.Literal.pos 3016)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3015), (Sat.Literal.pos 44), (Sat.Literal.pos 52), (Sat.Literal.pos 3016)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3016) = lexBefore s permutation3 43 := by
  exact (positive_lex_of_descriptor s 3016 permutation3 44 (by rfl)).trans ((lex_skipped s permutation3 43 44 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation3 43) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation3 43 by rw [image3_eq]; rfl))

theorem lex_3_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3017) (Sat.Literal.pos 3016) (Sat.Literal.pos 43) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation3 43 (assignment s)
    (Sat.Literal.pos 3017) (Sat.Literal.pos 3016) (Sat.Literal.pos 43) (Sat.Literal.pos 51) (positive_of_descriptor s 3017 (.lex permutation3 43) (by rfl)) (lex_3_43_prefix s) (positive_select s 43) (lex_3_43_image s)

theorem lex_3_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.pos 43), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation3 43 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3016) (Sat.Literal.pos 43) (Sat.Literal.pos 51) (lex_3_43_prefix s) (positive_select s 43) (lex_3_43_image s)

theorem lex_3_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.pos 3016)] :=
  (lex_3_43_gate s).prop _ (List.Mem.head _)

theorem lex_3_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.neg 43), (Sat.Literal.pos 51)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.pos 43), (Sat.Literal.neg 51)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.neg 43), (Sat.Literal.neg 51), (Sat.Literal.pos 3017)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3016), (Sat.Literal.pos 43), (Sat.Literal.pos 51), (Sat.Literal.pos 3017)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3017) = lexBefore s permutation3 42 := by
  exact (positive_lex_of_descriptor s 3017 permutation3 43 (by rfl)).trans ((lex_skipped s permutation3 42 43 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation3 42) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation3 42 by rw [image3_eq]; rfl))

theorem lex_3_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3018) (Sat.Literal.pos 3017) (Sat.Literal.pos 42) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation3 42 (assignment s)
    (Sat.Literal.pos 3018) (Sat.Literal.pos 3017) (Sat.Literal.pos 42) (Sat.Literal.pos 50) (positive_of_descriptor s 3018 (.lex permutation3 42) (by rfl)) (lex_3_42_prefix s) (positive_select s 42) (lex_3_42_image s)

theorem lex_3_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.pos 42), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation3 42 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3017) (Sat.Literal.pos 42) (Sat.Literal.pos 50) (lex_3_42_prefix s) (positive_select s 42) (lex_3_42_image s)

theorem lex_3_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.pos 3017)] :=
  (lex_3_42_gate s).prop _ (List.Mem.head _)

theorem lex_3_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.neg 42), (Sat.Literal.pos 50)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.pos 42), (Sat.Literal.neg 50)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.neg 42), (Sat.Literal.neg 50), (Sat.Literal.pos 3018)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3017), (Sat.Literal.pos 42), (Sat.Literal.pos 50), (Sat.Literal.pos 3018)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3018) = lexBefore s permutation3 41 := by
  exact (positive_lex_of_descriptor s 3018 permutation3 42 (by rfl)).trans ((lex_skipped s permutation3 41 42 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation3 41) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation3 41 by rw [image3_eq]; rfl))

theorem lex_3_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3019) (Sat.Literal.pos 3018) (Sat.Literal.pos 41) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation3 41 (assignment s)
    (Sat.Literal.pos 3019) (Sat.Literal.pos 3018) (Sat.Literal.pos 41) (Sat.Literal.pos 49) (positive_of_descriptor s 3019 (.lex permutation3 41) (by rfl)) (lex_3_41_prefix s) (positive_select s 41) (lex_3_41_image s)

theorem lex_3_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.pos 41), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation3 41 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3018) (Sat.Literal.pos 41) (Sat.Literal.pos 49) (lex_3_41_prefix s) (positive_select s 41) (lex_3_41_image s)

theorem lex_3_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.pos 3018)] :=
  (lex_3_41_gate s).prop _ (List.Mem.head _)

theorem lex_3_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.neg 41), (Sat.Literal.pos 49)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.pos 41), (Sat.Literal.neg 49)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.neg 41), (Sat.Literal.neg 49), (Sat.Literal.pos 3019)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3018), (Sat.Literal.pos 41), (Sat.Literal.pos 49), (Sat.Literal.pos 3019)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3019) = lexBefore s permutation3 40 := by
  exact (positive_lex_of_descriptor s 3019 permutation3 41 (by rfl)).trans ((lex_skipped s permutation3 40 41 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation3 40) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation3 40 by rw [image3_eq]; rfl))

theorem lex_3_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3020) (Sat.Literal.pos 3019) (Sat.Literal.pos 40) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation3 40 (assignment s)
    (Sat.Literal.pos 3020) (Sat.Literal.pos 3019) (Sat.Literal.pos 40) (Sat.Literal.pos 48) (positive_of_descriptor s 3020 (.lex permutation3 40) (by rfl)) (lex_3_40_prefix s) (positive_select s 40) (lex_3_40_image s)

theorem lex_3_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.pos 40), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation3 40 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3019) (Sat.Literal.pos 40) (Sat.Literal.pos 48) (lex_3_40_prefix s) (positive_select s 40) (lex_3_40_image s)

theorem lex_3_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.pos 3019)] :=
  (lex_3_40_gate s).prop _ (List.Mem.head _)

theorem lex_3_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.neg 40), (Sat.Literal.pos 48)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.pos 40), (Sat.Literal.neg 48)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.neg 40), (Sat.Literal.neg 48), (Sat.Literal.pos 3020)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3019), (Sat.Literal.pos 40), (Sat.Literal.pos 48), (Sat.Literal.pos 3020)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3020) = lexBefore s permutation3 23 := by
  exact (positive_lex_of_descriptor s 3020 permutation3 40 (by rfl)).trans ((lex_skipped s permutation3 23 40 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 24 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation3 23) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation3 23 by rw [image3_eq]; rfl))

theorem lex_3_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3021) (Sat.Literal.pos 3020) (Sat.Literal.pos 23) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation3 23 (assignment s)
    (Sat.Literal.pos 3021) (Sat.Literal.pos 3020) (Sat.Literal.pos 23) (Sat.Literal.pos 15) (positive_of_descriptor s 3021 (.lex permutation3 23) (by rfl)) (lex_3_23_prefix s) (positive_select s 23) (lex_3_23_image s)

theorem lex_3_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.pos 23), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation3 23 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3020) (Sat.Literal.pos 23) (Sat.Literal.pos 15) (lex_3_23_prefix s) (positive_select s 23) (lex_3_23_image s)

theorem lex_3_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.pos 3020)] :=
  (lex_3_23_gate s).prop _ (List.Mem.head _)

theorem lex_3_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.neg 23), (Sat.Literal.pos 15)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.pos 23), (Sat.Literal.neg 15)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.neg 23), (Sat.Literal.neg 15), (Sat.Literal.pos 3021)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3020), (Sat.Literal.pos 23), (Sat.Literal.pos 15), (Sat.Literal.pos 3021)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3021) = lexBefore s permutation3 22 := by
  exact (positive_lex_of_descriptor s 3021 permutation3 23 (by rfl)).trans ((lex_skipped s permutation3 22 23 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation3 22) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation3 22 by rw [image3_eq]; rfl))

theorem lex_3_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3022) (Sat.Literal.pos 3021) (Sat.Literal.pos 22) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation3 22 (assignment s)
    (Sat.Literal.pos 3022) (Sat.Literal.pos 3021) (Sat.Literal.pos 22) (Sat.Literal.pos 14) (positive_of_descriptor s 3022 (.lex permutation3 22) (by rfl)) (lex_3_22_prefix s) (positive_select s 22) (lex_3_22_image s)

theorem lex_3_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.pos 22), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation3 22 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3021) (Sat.Literal.pos 22) (Sat.Literal.pos 14) (lex_3_22_prefix s) (positive_select s 22) (lex_3_22_image s)

theorem lex_3_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.pos 3021)] :=
  (lex_3_22_gate s).prop _ (List.Mem.head _)

theorem lex_3_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.neg 22), (Sat.Literal.pos 14)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.pos 22), (Sat.Literal.neg 14)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.neg 22), (Sat.Literal.neg 14), (Sat.Literal.pos 3022)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3021), (Sat.Literal.pos 22), (Sat.Literal.pos 14), (Sat.Literal.pos 3022)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3022) = lexBefore s permutation3 21 := by
  exact (positive_lex_of_descriptor s 3022 permutation3 22 (by rfl)).trans ((lex_skipped s permutation3 21 22 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation3 21) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation3 21 by rw [image3_eq]; rfl))

theorem lex_3_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3023) (Sat.Literal.pos 3022) (Sat.Literal.pos 21) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation3 21 (assignment s)
    (Sat.Literal.pos 3023) (Sat.Literal.pos 3022) (Sat.Literal.pos 21) (Sat.Literal.pos 13) (positive_of_descriptor s 3023 (.lex permutation3 21) (by rfl)) (lex_3_21_prefix s) (positive_select s 21) (lex_3_21_image s)

theorem lex_3_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.pos 21), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation3 21 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3022) (Sat.Literal.pos 21) (Sat.Literal.pos 13) (lex_3_21_prefix s) (positive_select s 21) (lex_3_21_image s)

theorem lex_3_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.pos 3022)] :=
  (lex_3_21_gate s).prop _ (List.Mem.head _)

theorem lex_3_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.neg 21), (Sat.Literal.pos 13)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.pos 21), (Sat.Literal.neg 13)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.neg 21), (Sat.Literal.neg 13), (Sat.Literal.pos 3023)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3022), (Sat.Literal.pos 21), (Sat.Literal.pos 13), (Sat.Literal.pos 3023)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3023) = lexBefore s permutation3 20 := by
  exact (positive_lex_of_descriptor s 3023 permutation3 21 (by rfl)).trans ((lex_skipped s permutation3 20 21 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation3 20) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation3 20 by rw [image3_eq]; rfl))

theorem lex_3_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3024) (Sat.Literal.pos 3023) (Sat.Literal.pos 20) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation3 20 (assignment s)
    (Sat.Literal.pos 3024) (Sat.Literal.pos 3023) (Sat.Literal.pos 20) (Sat.Literal.pos 12) (positive_of_descriptor s 3024 (.lex permutation3 20) (by rfl)) (lex_3_20_prefix s) (positive_select s 20) (lex_3_20_image s)

theorem lex_3_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.pos 20), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation3 20 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 3023) (Sat.Literal.pos 20) (Sat.Literal.pos 12) (lex_3_20_prefix s) (positive_select s 20) (lex_3_20_image s)

theorem lex_3_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.pos 3023)] :=
  (lex_3_20_gate s).prop _ (List.Mem.head _)

theorem lex_3_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.neg 20), (Sat.Literal.pos 12)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3024), (Sat.Literal.pos 20), (Sat.Literal.neg 12)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.neg 20), (Sat.Literal.neg 12), (Sat.Literal.pos 3024)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3023), (Sat.Literal.pos 20), (Sat.Literal.pos 12), (Sat.Literal.pos 3024)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_3_215_gate

end Crown.CertificateData
