import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_5_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3224) = lexBefore s permutation5 163 := by
  exact (positive_lex_of_descriptor s 3224 permutation5 164 (by rfl)).trans ((lex_skipped s permutation5 163 164 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation5 163) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation5 163 by rw [image5_eq]; rfl))

theorem lex_5_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3225) (Sat.Literal.pos 3224) (Sat.Literal.pos 163) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation5 163 (assignment s)
    (Sat.Literal.pos 3225) (Sat.Literal.pos 3224) (Sat.Literal.pos 163) (Sat.Literal.pos 195) (positive_of_descriptor s 3225 (.lex permutation5 163) (by rfl)) (lex_5_163_prefix s) (positive_select s 163) (lex_5_163_image s)

theorem lex_5_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.pos 163), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation5 163 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3224) (Sat.Literal.pos 163) (Sat.Literal.pos 195) (lex_5_163_prefix s) (positive_select s 163) (lex_5_163_image s)

theorem lex_5_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.pos 3224)] :=
  (lex_5_163_gate s).prop _ (List.Mem.head _)

theorem lex_5_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.neg 163), (Sat.Literal.pos 195)] :=
  (lex_5_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.pos 163), (Sat.Literal.neg 195)] :=
  (lex_5_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.neg 163), (Sat.Literal.neg 195), (Sat.Literal.pos 3225)] :=
  (lex_5_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.pos 163), (Sat.Literal.pos 195), (Sat.Literal.pos 3225)] :=
  (lex_5_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3225) = lexBefore s permutation5 162 := by
  exact (positive_lex_of_descriptor s 3225 permutation5 163 (by rfl)).trans ((lex_skipped s permutation5 162 163 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation5 162) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation5 162 by rw [image5_eq]; rfl))

theorem lex_5_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3226) (Sat.Literal.pos 3225) (Sat.Literal.pos 162) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation5 162 (assignment s)
    (Sat.Literal.pos 3226) (Sat.Literal.pos 3225) (Sat.Literal.pos 162) (Sat.Literal.pos 194) (positive_of_descriptor s 3226 (.lex permutation5 162) (by rfl)) (lex_5_162_prefix s) (positive_select s 162) (lex_5_162_image s)

theorem lex_5_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.pos 162), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation5 162 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3225) (Sat.Literal.pos 162) (Sat.Literal.pos 194) (lex_5_162_prefix s) (positive_select s 162) (lex_5_162_image s)

theorem lex_5_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.pos 3225)] :=
  (lex_5_162_gate s).prop _ (List.Mem.head _)

theorem lex_5_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.neg 162), (Sat.Literal.pos 194)] :=
  (lex_5_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.pos 162), (Sat.Literal.neg 194)] :=
  (lex_5_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.neg 162), (Sat.Literal.neg 194), (Sat.Literal.pos 3226)] :=
  (lex_5_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3225), (Sat.Literal.pos 162), (Sat.Literal.pos 194), (Sat.Literal.pos 3226)] :=
  (lex_5_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3226) = lexBefore s permutation5 161 := by
  exact (positive_lex_of_descriptor s 3226 permutation5 162 (by rfl)).trans ((lex_skipped s permutation5 161 162 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation5 161) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation5 161 by rw [image5_eq]; rfl))

theorem lex_5_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3227) (Sat.Literal.pos 3226) (Sat.Literal.pos 161) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation5 161 (assignment s)
    (Sat.Literal.pos 3227) (Sat.Literal.pos 3226) (Sat.Literal.pos 161) (Sat.Literal.pos 193) (positive_of_descriptor s 3227 (.lex permutation5 161) (by rfl)) (lex_5_161_prefix s) (positive_select s 161) (lex_5_161_image s)

theorem lex_5_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.pos 161), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation5 161 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3226) (Sat.Literal.pos 161) (Sat.Literal.pos 193) (lex_5_161_prefix s) (positive_select s 161) (lex_5_161_image s)

theorem lex_5_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.pos 3226)] :=
  (lex_5_161_gate s).prop _ (List.Mem.head _)

theorem lex_5_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.neg 161), (Sat.Literal.pos 193)] :=
  (lex_5_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.pos 161), (Sat.Literal.neg 193)] :=
  (lex_5_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.neg 161), (Sat.Literal.neg 193), (Sat.Literal.pos 3227)] :=
  (lex_5_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3226), (Sat.Literal.pos 161), (Sat.Literal.pos 193), (Sat.Literal.pos 3227)] :=
  (lex_5_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3227) = lexBefore s permutation5 160 := by
  exact (positive_lex_of_descriptor s 3227 permutation5 161 (by rfl)).trans ((lex_skipped s permutation5 160 161 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation5 160) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation5 160 by rw [image5_eq]; rfl))

theorem lex_5_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3228) (Sat.Literal.pos 3227) (Sat.Literal.pos 160) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation5 160 (assignment s)
    (Sat.Literal.pos 3228) (Sat.Literal.pos 3227) (Sat.Literal.pos 160) (Sat.Literal.pos 192) (positive_of_descriptor s 3228 (.lex permutation5 160) (by rfl)) (lex_5_160_prefix s) (positive_select s 160) (lex_5_160_image s)

theorem lex_5_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.pos 160), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation5 160 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3227) (Sat.Literal.pos 160) (Sat.Literal.pos 192) (lex_5_160_prefix s) (positive_select s 160) (lex_5_160_image s)

theorem lex_5_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.pos 3227)] :=
  (lex_5_160_gate s).prop _ (List.Mem.head _)

theorem lex_5_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.neg 160), (Sat.Literal.pos 192)] :=
  (lex_5_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.pos 160), (Sat.Literal.neg 192)] :=
  (lex_5_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.neg 160), (Sat.Literal.neg 192), (Sat.Literal.pos 3228)] :=
  (lex_5_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3227), (Sat.Literal.pos 160), (Sat.Literal.pos 192), (Sat.Literal.pos 3228)] :=
  (lex_5_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3228) = lexBefore s permutation5 95 := by
  exact (positive_lex_of_descriptor s 3228 permutation5 160 (by rfl)).trans ((lex_skipped s permutation5 95 160 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 96 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation5 95) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation5 95 by rw [image5_eq]; rfl))

theorem lex_5_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3229) (Sat.Literal.pos 3228) (Sat.Literal.pos 95) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation5 95 (assignment s)
    (Sat.Literal.pos 3229) (Sat.Literal.pos 3228) (Sat.Literal.pos 95) (Sat.Literal.pos 63) (positive_of_descriptor s 3229 (.lex permutation5 95) (by rfl)) (lex_5_95_prefix s) (positive_select s 95) (lex_5_95_image s)

theorem lex_5_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.pos 95), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation5 95 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3228) (Sat.Literal.pos 95) (Sat.Literal.pos 63) (lex_5_95_prefix s) (positive_select s 95) (lex_5_95_image s)

theorem lex_5_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.pos 3228)] :=
  (lex_5_95_gate s).prop _ (List.Mem.head _)

theorem lex_5_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.neg 95), (Sat.Literal.pos 63)] :=
  (lex_5_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.pos 95), (Sat.Literal.neg 63)] :=
  (lex_5_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.neg 95), (Sat.Literal.neg 63), (Sat.Literal.pos 3229)] :=
  (lex_5_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3228), (Sat.Literal.pos 95), (Sat.Literal.pos 63), (Sat.Literal.pos 3229)] :=
  (lex_5_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3229) = lexBefore s permutation5 94 := by
  exact (positive_lex_of_descriptor s 3229 permutation5 95 (by rfl)).trans ((lex_skipped s permutation5 94 95 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation5 94) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation5 94 by rw [image5_eq]; rfl))

theorem lex_5_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3230) (Sat.Literal.pos 3229) (Sat.Literal.pos 94) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation5 94 (assignment s)
    (Sat.Literal.pos 3230) (Sat.Literal.pos 3229) (Sat.Literal.pos 94) (Sat.Literal.pos 62) (positive_of_descriptor s 3230 (.lex permutation5 94) (by rfl)) (lex_5_94_prefix s) (positive_select s 94) (lex_5_94_image s)

theorem lex_5_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.pos 94), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation5 94 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3229) (Sat.Literal.pos 94) (Sat.Literal.pos 62) (lex_5_94_prefix s) (positive_select s 94) (lex_5_94_image s)

theorem lex_5_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.pos 3229)] :=
  (lex_5_94_gate s).prop _ (List.Mem.head _)

theorem lex_5_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.neg 94), (Sat.Literal.pos 62)] :=
  (lex_5_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.pos 94), (Sat.Literal.neg 62)] :=
  (lex_5_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.neg 94), (Sat.Literal.neg 62), (Sat.Literal.pos 3230)] :=
  (lex_5_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3229), (Sat.Literal.pos 94), (Sat.Literal.pos 62), (Sat.Literal.pos 3230)] :=
  (lex_5_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3230) = lexBefore s permutation5 93 := by
  exact (positive_lex_of_descriptor s 3230 permutation5 94 (by rfl)).trans ((lex_skipped s permutation5 93 94 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation5 93) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation5 93 by rw [image5_eq]; rfl))

theorem lex_5_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3231) (Sat.Literal.pos 3230) (Sat.Literal.pos 93) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation5 93 (assignment s)
    (Sat.Literal.pos 3231) (Sat.Literal.pos 3230) (Sat.Literal.pos 93) (Sat.Literal.pos 61) (positive_of_descriptor s 3231 (.lex permutation5 93) (by rfl)) (lex_5_93_prefix s) (positive_select s 93) (lex_5_93_image s)

theorem lex_5_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.pos 93), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation5 93 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3230) (Sat.Literal.pos 93) (Sat.Literal.pos 61) (lex_5_93_prefix s) (positive_select s 93) (lex_5_93_image s)

theorem lex_5_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.pos 3230)] :=
  (lex_5_93_gate s).prop _ (List.Mem.head _)

theorem lex_5_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.neg 93), (Sat.Literal.pos 61)] :=
  (lex_5_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.pos 93), (Sat.Literal.neg 61)] :=
  (lex_5_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.neg 93), (Sat.Literal.neg 61), (Sat.Literal.pos 3231)] :=
  (lex_5_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3230), (Sat.Literal.pos 93), (Sat.Literal.pos 61), (Sat.Literal.pos 3231)] :=
  (lex_5_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3231) = lexBefore s permutation5 92 := by
  exact (positive_lex_of_descriptor s 3231 permutation5 93 (by rfl)).trans ((lex_skipped s permutation5 92 93 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation5 92) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation5 92 by rw [image5_eq]; rfl))

theorem lex_5_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3232) (Sat.Literal.pos 3231) (Sat.Literal.pos 92) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation5 92 (assignment s)
    (Sat.Literal.pos 3232) (Sat.Literal.pos 3231) (Sat.Literal.pos 92) (Sat.Literal.pos 60) (positive_of_descriptor s 3232 (.lex permutation5 92) (by rfl)) (lex_5_92_prefix s) (positive_select s 92) (lex_5_92_image s)

theorem lex_5_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.pos 92), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation5 92 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3231) (Sat.Literal.pos 92) (Sat.Literal.pos 60) (lex_5_92_prefix s) (positive_select s 92) (lex_5_92_image s)

theorem lex_5_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.pos 3231)] :=
  (lex_5_92_gate s).prop _ (List.Mem.head _)

theorem lex_5_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.neg 92), (Sat.Literal.pos 60)] :=
  (lex_5_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.pos 92), (Sat.Literal.neg 60)] :=
  (lex_5_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.neg 92), (Sat.Literal.neg 60), (Sat.Literal.pos 3232)] :=
  (lex_5_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3231), (Sat.Literal.pos 92), (Sat.Literal.pos 60), (Sat.Literal.pos 3232)] :=
  (lex_5_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3232) = lexBefore s permutation5 91 := by
  exact (positive_lex_of_descriptor s 3232 permutation5 92 (by rfl)).trans ((lex_skipped s permutation5 91 92 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation5 91) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation5 91 by rw [image5_eq]; rfl))

theorem lex_5_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3233) (Sat.Literal.pos 3232) (Sat.Literal.pos 91) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation5 91 (assignment s)
    (Sat.Literal.pos 3233) (Sat.Literal.pos 3232) (Sat.Literal.pos 91) (Sat.Literal.pos 59) (positive_of_descriptor s 3233 (.lex permutation5 91) (by rfl)) (lex_5_91_prefix s) (positive_select s 91) (lex_5_91_image s)

theorem lex_5_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.pos 91), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation5 91 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3232) (Sat.Literal.pos 91) (Sat.Literal.pos 59) (lex_5_91_prefix s) (positive_select s 91) (lex_5_91_image s)

theorem lex_5_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.pos 3232)] :=
  (lex_5_91_gate s).prop _ (List.Mem.head _)

theorem lex_5_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.neg 91), (Sat.Literal.pos 59)] :=
  (lex_5_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.pos 91), (Sat.Literal.neg 59)] :=
  (lex_5_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.neg 91), (Sat.Literal.neg 59), (Sat.Literal.pos 3233)] :=
  (lex_5_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3232), (Sat.Literal.pos 91), (Sat.Literal.pos 59), (Sat.Literal.pos 3233)] :=
  (lex_5_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3233) = lexBefore s permutation5 90 := by
  exact (positive_lex_of_descriptor s 3233 permutation5 91 (by rfl)).trans ((lex_skipped s permutation5 90 91 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation5 90) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation5 90 by rw [image5_eq]; rfl))

theorem lex_5_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3234) (Sat.Literal.pos 3233) (Sat.Literal.pos 90) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation5 90 (assignment s)
    (Sat.Literal.pos 3234) (Sat.Literal.pos 3233) (Sat.Literal.pos 90) (Sat.Literal.pos 58) (positive_of_descriptor s 3234 (.lex permutation5 90) (by rfl)) (lex_5_90_prefix s) (positive_select s 90) (lex_5_90_image s)

theorem lex_5_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.pos 90), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation5 90 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3233) (Sat.Literal.pos 90) (Sat.Literal.pos 58) (lex_5_90_prefix s) (positive_select s 90) (lex_5_90_image s)

theorem lex_5_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.pos 3233)] :=
  (lex_5_90_gate s).prop _ (List.Mem.head _)

theorem lex_5_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.neg 90), (Sat.Literal.pos 58)] :=
  (lex_5_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.pos 90), (Sat.Literal.neg 58)] :=
  (lex_5_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.neg 90), (Sat.Literal.neg 58), (Sat.Literal.pos 3234)] :=
  (lex_5_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3233), (Sat.Literal.pos 90), (Sat.Literal.pos 58), (Sat.Literal.pos 3234)] :=
  (lex_5_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3234) = lexBefore s permutation5 89 := by
  exact (positive_lex_of_descriptor s 3234 permutation5 90 (by rfl)).trans ((lex_skipped s permutation5 89 90 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation5 89) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation5 89 by rw [image5_eq]; rfl))

theorem lex_5_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3235) (Sat.Literal.pos 3234) (Sat.Literal.pos 89) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation5 89 (assignment s)
    (Sat.Literal.pos 3235) (Sat.Literal.pos 3234) (Sat.Literal.pos 89) (Sat.Literal.pos 57) (positive_of_descriptor s 3235 (.lex permutation5 89) (by rfl)) (lex_5_89_prefix s) (positive_select s 89) (lex_5_89_image s)

theorem lex_5_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.pos 89), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation5 89 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3234) (Sat.Literal.pos 89) (Sat.Literal.pos 57) (lex_5_89_prefix s) (positive_select s 89) (lex_5_89_image s)

theorem lex_5_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.pos 3234)] :=
  (lex_5_89_gate s).prop _ (List.Mem.head _)

theorem lex_5_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.neg 89), (Sat.Literal.pos 57)] :=
  (lex_5_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.pos 89), (Sat.Literal.neg 57)] :=
  (lex_5_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.neg 89), (Sat.Literal.neg 57), (Sat.Literal.pos 3235)] :=
  (lex_5_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3234), (Sat.Literal.pos 89), (Sat.Literal.pos 57), (Sat.Literal.pos 3235)] :=
  (lex_5_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3235) = lexBefore s permutation5 88 := by
  exact (positive_lex_of_descriptor s 3235 permutation5 89 (by rfl)).trans ((lex_skipped s permutation5 88 89 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation5 88) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation5 88 by rw [image5_eq]; rfl))

theorem lex_5_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3236) (Sat.Literal.pos 3235) (Sat.Literal.pos 88) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation5 88 (assignment s)
    (Sat.Literal.pos 3236) (Sat.Literal.pos 3235) (Sat.Literal.pos 88) (Sat.Literal.pos 56) (positive_of_descriptor s 3236 (.lex permutation5 88) (by rfl)) (lex_5_88_prefix s) (positive_select s 88) (lex_5_88_image s)

theorem lex_5_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.pos 88), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation5 88 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3235) (Sat.Literal.pos 88) (Sat.Literal.pos 56) (lex_5_88_prefix s) (positive_select s 88) (lex_5_88_image s)

theorem lex_5_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.pos 3235)] :=
  (lex_5_88_gate s).prop _ (List.Mem.head _)

theorem lex_5_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.neg 88), (Sat.Literal.pos 56)] :=
  (lex_5_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.pos 88), (Sat.Literal.neg 56)] :=
  (lex_5_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.neg 88), (Sat.Literal.neg 56), (Sat.Literal.pos 3236)] :=
  (lex_5_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3235), (Sat.Literal.pos 88), (Sat.Literal.pos 56), (Sat.Literal.pos 3236)] :=
  (lex_5_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3236) = lexBefore s permutation5 87 := by
  exact (positive_lex_of_descriptor s 3236 permutation5 88 (by rfl)).trans ((lex_skipped s permutation5 87 88 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation5 87) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation5 87 by rw [image5_eq]; rfl))

theorem lex_5_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3237) (Sat.Literal.pos 3236) (Sat.Literal.pos 87) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation5 87 (assignment s)
    (Sat.Literal.pos 3237) (Sat.Literal.pos 3236) (Sat.Literal.pos 87) (Sat.Literal.pos 55) (positive_of_descriptor s 3237 (.lex permutation5 87) (by rfl)) (lex_5_87_prefix s) (positive_select s 87) (lex_5_87_image s)

theorem lex_5_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.pos 87), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation5 87 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3236) (Sat.Literal.pos 87) (Sat.Literal.pos 55) (lex_5_87_prefix s) (positive_select s 87) (lex_5_87_image s)

theorem lex_5_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.pos 3236)] :=
  (lex_5_87_gate s).prop _ (List.Mem.head _)

theorem lex_5_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.neg 87), (Sat.Literal.pos 55)] :=
  (lex_5_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.pos 87), (Sat.Literal.neg 55)] :=
  (lex_5_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.neg 87), (Sat.Literal.neg 55), (Sat.Literal.pos 3237)] :=
  (lex_5_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3236), (Sat.Literal.pos 87), (Sat.Literal.pos 55), (Sat.Literal.pos 3237)] :=
  (lex_5_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3237) = lexBefore s permutation5 86 := by
  exact (positive_lex_of_descriptor s 3237 permutation5 87 (by rfl)).trans ((lex_skipped s permutation5 86 87 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation5 86) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation5 86 by rw [image5_eq]; rfl))

theorem lex_5_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3238) (Sat.Literal.pos 3237) (Sat.Literal.pos 86) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation5 86 (assignment s)
    (Sat.Literal.pos 3238) (Sat.Literal.pos 3237) (Sat.Literal.pos 86) (Sat.Literal.pos 54) (positive_of_descriptor s 3238 (.lex permutation5 86) (by rfl)) (lex_5_86_prefix s) (positive_select s 86) (lex_5_86_image s)

theorem lex_5_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.pos 86), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation5 86 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3237) (Sat.Literal.pos 86) (Sat.Literal.pos 54) (lex_5_86_prefix s) (positive_select s 86) (lex_5_86_image s)

theorem lex_5_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.pos 3237)] :=
  (lex_5_86_gate s).prop _ (List.Mem.head _)

theorem lex_5_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.neg 86), (Sat.Literal.pos 54)] :=
  (lex_5_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.pos 86), (Sat.Literal.neg 54)] :=
  (lex_5_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.neg 86), (Sat.Literal.neg 54), (Sat.Literal.pos 3238)] :=
  (lex_5_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3237), (Sat.Literal.pos 86), (Sat.Literal.pos 54), (Sat.Literal.pos 3238)] :=
  (lex_5_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3238) = lexBefore s permutation5 85 := by
  exact (positive_lex_of_descriptor s 3238 permutation5 86 (by rfl)).trans ((lex_skipped s permutation5 85 86 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation5 85) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation5 85 by rw [image5_eq]; rfl))

theorem lex_5_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3239) (Sat.Literal.pos 3238) (Sat.Literal.pos 85) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation5 85 (assignment s)
    (Sat.Literal.pos 3239) (Sat.Literal.pos 3238) (Sat.Literal.pos 85) (Sat.Literal.pos 53) (positive_of_descriptor s 3239 (.lex permutation5 85) (by rfl)) (lex_5_85_prefix s) (positive_select s 85) (lex_5_85_image s)

theorem lex_5_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.pos 85), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation5 85 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3238) (Sat.Literal.pos 85) (Sat.Literal.pos 53) (lex_5_85_prefix s) (positive_select s 85) (lex_5_85_image s)

theorem lex_5_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.pos 3238)] :=
  (lex_5_85_gate s).prop _ (List.Mem.head _)

theorem lex_5_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.neg 85), (Sat.Literal.pos 53)] :=
  (lex_5_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.pos 85), (Sat.Literal.neg 53)] :=
  (lex_5_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.neg 85), (Sat.Literal.neg 53), (Sat.Literal.pos 3239)] :=
  (lex_5_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3238), (Sat.Literal.pos 85), (Sat.Literal.pos 53), (Sat.Literal.pos 3239)] :=
  (lex_5_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3239) = lexBefore s permutation5 84 := by
  exact (positive_lex_of_descriptor s 3239 permutation5 85 (by rfl)).trans ((lex_skipped s permutation5 84 85 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation5 84) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation5 84 by rw [image5_eq]; rfl))

theorem lex_5_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3240) (Sat.Literal.pos 3239) (Sat.Literal.pos 84) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation5 84 (assignment s)
    (Sat.Literal.pos 3240) (Sat.Literal.pos 3239) (Sat.Literal.pos 84) (Sat.Literal.pos 52) (positive_of_descriptor s 3240 (.lex permutation5 84) (by rfl)) (lex_5_84_prefix s) (positive_select s 84) (lex_5_84_image s)

theorem lex_5_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.pos 84), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation5 84 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3239) (Sat.Literal.pos 84) (Sat.Literal.pos 52) (lex_5_84_prefix s) (positive_select s 84) (lex_5_84_image s)

theorem lex_5_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.pos 3239)] :=
  (lex_5_84_gate s).prop _ (List.Mem.head _)

theorem lex_5_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.neg 84), (Sat.Literal.pos 52)] :=
  (lex_5_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.pos 84), (Sat.Literal.neg 52)] :=
  (lex_5_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.neg 84), (Sat.Literal.neg 52), (Sat.Literal.pos 3240)] :=
  (lex_5_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3239), (Sat.Literal.pos 84), (Sat.Literal.pos 52), (Sat.Literal.pos 3240)] :=
  (lex_5_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3240) = lexBefore s permutation5 83 := by
  exact (positive_lex_of_descriptor s 3240 permutation5 84 (by rfl)).trans ((lex_skipped s permutation5 83 84 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation5 83) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation5 83 by rw [image5_eq]; rfl))

theorem lex_5_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3241) (Sat.Literal.pos 3240) (Sat.Literal.pos 83) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation5 83 (assignment s)
    (Sat.Literal.pos 3241) (Sat.Literal.pos 3240) (Sat.Literal.pos 83) (Sat.Literal.pos 51) (positive_of_descriptor s 3241 (.lex permutation5 83) (by rfl)) (lex_5_83_prefix s) (positive_select s 83) (lex_5_83_image s)

theorem lex_5_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.pos 83), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation5 83 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3240) (Sat.Literal.pos 83) (Sat.Literal.pos 51) (lex_5_83_prefix s) (positive_select s 83) (lex_5_83_image s)

theorem lex_5_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.pos 3240)] :=
  (lex_5_83_gate s).prop _ (List.Mem.head _)

theorem lex_5_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.neg 83), (Sat.Literal.pos 51)] :=
  (lex_5_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.pos 83), (Sat.Literal.neg 51)] :=
  (lex_5_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.neg 83), (Sat.Literal.neg 51), (Sat.Literal.pos 3241)] :=
  (lex_5_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3240), (Sat.Literal.pos 83), (Sat.Literal.pos 51), (Sat.Literal.pos 3241)] :=
  (lex_5_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3241) = lexBefore s permutation5 82 := by
  exact (positive_lex_of_descriptor s 3241 permutation5 83 (by rfl)).trans ((lex_skipped s permutation5 82 83 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation5 82) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation5 82 by rw [image5_eq]; rfl))

theorem lex_5_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3242) (Sat.Literal.pos 3241) (Sat.Literal.pos 82) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation5 82 (assignment s)
    (Sat.Literal.pos 3242) (Sat.Literal.pos 3241) (Sat.Literal.pos 82) (Sat.Literal.pos 50) (positive_of_descriptor s 3242 (.lex permutation5 82) (by rfl)) (lex_5_82_prefix s) (positive_select s 82) (lex_5_82_image s)

theorem lex_5_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.pos 82), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation5 82 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3241) (Sat.Literal.pos 82) (Sat.Literal.pos 50) (lex_5_82_prefix s) (positive_select s 82) (lex_5_82_image s)

theorem lex_5_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.pos 3241)] :=
  (lex_5_82_gate s).prop _ (List.Mem.head _)

theorem lex_5_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.neg 82), (Sat.Literal.pos 50)] :=
  (lex_5_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.pos 82), (Sat.Literal.neg 50)] :=
  (lex_5_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.neg 82), (Sat.Literal.neg 50), (Sat.Literal.pos 3242)] :=
  (lex_5_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3241), (Sat.Literal.pos 82), (Sat.Literal.pos 50), (Sat.Literal.pos 3242)] :=
  (lex_5_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3242) = lexBefore s permutation5 81 := by
  exact (positive_lex_of_descriptor s 3242 permutation5 82 (by rfl)).trans ((lex_skipped s permutation5 81 82 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation5 81) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation5 81 by rw [image5_eq]; rfl))

theorem lex_5_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3243) (Sat.Literal.pos 3242) (Sat.Literal.pos 81) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation5 81 (assignment s)
    (Sat.Literal.pos 3243) (Sat.Literal.pos 3242) (Sat.Literal.pos 81) (Sat.Literal.pos 49) (positive_of_descriptor s 3243 (.lex permutation5 81) (by rfl)) (lex_5_81_prefix s) (positive_select s 81) (lex_5_81_image s)

theorem lex_5_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.pos 81), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation5 81 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3242) (Sat.Literal.pos 81) (Sat.Literal.pos 49) (lex_5_81_prefix s) (positive_select s 81) (lex_5_81_image s)

theorem lex_5_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.pos 3242)] :=
  (lex_5_81_gate s).prop _ (List.Mem.head _)

theorem lex_5_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.neg 81), (Sat.Literal.pos 49)] :=
  (lex_5_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.pos 81), (Sat.Literal.neg 49)] :=
  (lex_5_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.neg 81), (Sat.Literal.neg 49), (Sat.Literal.pos 3243)] :=
  (lex_5_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3242), (Sat.Literal.pos 81), (Sat.Literal.pos 49), (Sat.Literal.pos 3243)] :=
  (lex_5_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3243) = lexBefore s permutation5 80 := by
  exact (positive_lex_of_descriptor s 3243 permutation5 81 (by rfl)).trans ((lex_skipped s permutation5 80 81 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation5 80) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation5 80 by rw [image5_eq]; rfl))

theorem lex_5_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3244) (Sat.Literal.pos 3243) (Sat.Literal.pos 80) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation5 80 (assignment s)
    (Sat.Literal.pos 3244) (Sat.Literal.pos 3243) (Sat.Literal.pos 80) (Sat.Literal.pos 48) (positive_of_descriptor s 3244 (.lex permutation5 80) (by rfl)) (lex_5_80_prefix s) (positive_select s 80) (lex_5_80_image s)

theorem lex_5_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.pos 80), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation5 80 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3243) (Sat.Literal.pos 80) (Sat.Literal.pos 48) (lex_5_80_prefix s) (positive_select s 80) (lex_5_80_image s)

theorem lex_5_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.pos 3243)] :=
  (lex_5_80_gate s).prop _ (List.Mem.head _)

theorem lex_5_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.neg 80), (Sat.Literal.pos 48)] :=
  (lex_5_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.pos 80), (Sat.Literal.neg 48)] :=
  (lex_5_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.neg 80), (Sat.Literal.neg 48), (Sat.Literal.pos 3244)] :=
  (lex_5_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3243), (Sat.Literal.pos 80), (Sat.Literal.pos 48), (Sat.Literal.pos 3244)] :=
  (lex_5_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3244) = lexBefore s permutation5 79 := by
  exact (positive_lex_of_descriptor s 3244 permutation5 80 (by rfl)).trans ((lex_skipped s permutation5 79 80 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation5 79) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation5 79 by rw [image5_eq]; rfl))

theorem lex_5_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3245) (Sat.Literal.pos 3244) (Sat.Literal.pos 79) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation5 79 (assignment s)
    (Sat.Literal.pos 3245) (Sat.Literal.pos 3244) (Sat.Literal.pos 79) (Sat.Literal.pos 47) (positive_of_descriptor s 3245 (.lex permutation5 79) (by rfl)) (lex_5_79_prefix s) (positive_select s 79) (lex_5_79_image s)

theorem lex_5_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.pos 79), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation5 79 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3244) (Sat.Literal.pos 79) (Sat.Literal.pos 47) (lex_5_79_prefix s) (positive_select s 79) (lex_5_79_image s)

theorem lex_5_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.pos 3244)] :=
  (lex_5_79_gate s).prop _ (List.Mem.head _)

theorem lex_5_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.neg 79), (Sat.Literal.pos 47)] :=
  (lex_5_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.pos 79), (Sat.Literal.neg 47)] :=
  (lex_5_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.neg 79), (Sat.Literal.neg 47), (Sat.Literal.pos 3245)] :=
  (lex_5_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3244), (Sat.Literal.pos 79), (Sat.Literal.pos 47), (Sat.Literal.pos 3245)] :=
  (lex_5_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3245) = lexBefore s permutation5 78 := by
  exact (positive_lex_of_descriptor s 3245 permutation5 79 (by rfl)).trans ((lex_skipped s permutation5 78 79 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation5 78) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation5 78 by rw [image5_eq]; rfl))

theorem lex_5_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3246) (Sat.Literal.pos 3245) (Sat.Literal.pos 78) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation5 78 (assignment s)
    (Sat.Literal.pos 3246) (Sat.Literal.pos 3245) (Sat.Literal.pos 78) (Sat.Literal.pos 46) (positive_of_descriptor s 3246 (.lex permutation5 78) (by rfl)) (lex_5_78_prefix s) (positive_select s 78) (lex_5_78_image s)

theorem lex_5_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.pos 78), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation5 78 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3245) (Sat.Literal.pos 78) (Sat.Literal.pos 46) (lex_5_78_prefix s) (positive_select s 78) (lex_5_78_image s)

theorem lex_5_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.pos 3245)] :=
  (lex_5_78_gate s).prop _ (List.Mem.head _)

theorem lex_5_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.neg 78), (Sat.Literal.pos 46)] :=
  (lex_5_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.pos 78), (Sat.Literal.neg 46)] :=
  (lex_5_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.neg 78), (Sat.Literal.neg 46), (Sat.Literal.pos 3246)] :=
  (lex_5_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3245), (Sat.Literal.pos 78), (Sat.Literal.pos 46), (Sat.Literal.pos 3246)] :=
  (lex_5_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3246) = lexBefore s permutation5 77 := by
  exact (positive_lex_of_descriptor s 3246 permutation5 78 (by rfl)).trans ((lex_skipped s permutation5 77 78 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation5 77) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation5 77 by rw [image5_eq]; rfl))

theorem lex_5_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3247) (Sat.Literal.pos 3246) (Sat.Literal.pos 77) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation5 77 (assignment s)
    (Sat.Literal.pos 3247) (Sat.Literal.pos 3246) (Sat.Literal.pos 77) (Sat.Literal.pos 45) (positive_of_descriptor s 3247 (.lex permutation5 77) (by rfl)) (lex_5_77_prefix s) (positive_select s 77) (lex_5_77_image s)

theorem lex_5_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.pos 77), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation5 77 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3246) (Sat.Literal.pos 77) (Sat.Literal.pos 45) (lex_5_77_prefix s) (positive_select s 77) (lex_5_77_image s)

theorem lex_5_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.pos 3246)] :=
  (lex_5_77_gate s).prop _ (List.Mem.head _)

theorem lex_5_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.neg 77), (Sat.Literal.pos 45)] :=
  (lex_5_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.pos 77), (Sat.Literal.neg 45)] :=
  (lex_5_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.neg 77), (Sat.Literal.neg 45), (Sat.Literal.pos 3247)] :=
  (lex_5_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3246), (Sat.Literal.pos 77), (Sat.Literal.pos 45), (Sat.Literal.pos 3247)] :=
  (lex_5_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3247) = lexBefore s permutation5 76 := by
  exact (positive_lex_of_descriptor s 3247 permutation5 77 (by rfl)).trans ((lex_skipped s permutation5 76 77 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation5 76) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation5 76 by rw [image5_eq]; rfl))

theorem lex_5_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3248) (Sat.Literal.pos 3247) (Sat.Literal.pos 76) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation5 76 (assignment s)
    (Sat.Literal.pos 3248) (Sat.Literal.pos 3247) (Sat.Literal.pos 76) (Sat.Literal.pos 44) (positive_of_descriptor s 3248 (.lex permutation5 76) (by rfl)) (lex_5_76_prefix s) (positive_select s 76) (lex_5_76_image s)

theorem lex_5_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.pos 76), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation5 76 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3247) (Sat.Literal.pos 76) (Sat.Literal.pos 44) (lex_5_76_prefix s) (positive_select s 76) (lex_5_76_image s)

theorem lex_5_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.pos 3247)] :=
  (lex_5_76_gate s).prop _ (List.Mem.head _)

theorem lex_5_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.neg 76), (Sat.Literal.pos 44)] :=
  (lex_5_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.pos 76), (Sat.Literal.neg 44)] :=
  (lex_5_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.neg 76), (Sat.Literal.neg 44), (Sat.Literal.pos 3248)] :=
  (lex_5_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3247), (Sat.Literal.pos 76), (Sat.Literal.pos 44), (Sat.Literal.pos 3248)] :=
  (lex_5_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3248) = lexBefore s permutation5 75 := by
  exact (positive_lex_of_descriptor s 3248 permutation5 76 (by rfl)).trans ((lex_skipped s permutation5 75 76 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation5 75) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation5 75 by rw [image5_eq]; rfl))

theorem lex_5_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3249) (Sat.Literal.pos 3248) (Sat.Literal.pos 75) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation5 75 (assignment s)
    (Sat.Literal.pos 3249) (Sat.Literal.pos 3248) (Sat.Literal.pos 75) (Sat.Literal.pos 43) (positive_of_descriptor s 3249 (.lex permutation5 75) (by rfl)) (lex_5_75_prefix s) (positive_select s 75) (lex_5_75_image s)

theorem lex_5_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.pos 75), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation5 75 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3248) (Sat.Literal.pos 75) (Sat.Literal.pos 43) (lex_5_75_prefix s) (positive_select s 75) (lex_5_75_image s)

theorem lex_5_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.pos 3248)] :=
  (lex_5_75_gate s).prop _ (List.Mem.head _)

theorem lex_5_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.neg 75), (Sat.Literal.pos 43)] :=
  (lex_5_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.pos 75), (Sat.Literal.neg 43)] :=
  (lex_5_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.neg 75), (Sat.Literal.neg 43), (Sat.Literal.pos 3249)] :=
  (lex_5_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3248), (Sat.Literal.pos 75), (Sat.Literal.pos 43), (Sat.Literal.pos 3249)] :=
  (lex_5_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3249) = lexBefore s permutation5 74 := by
  exact (positive_lex_of_descriptor s 3249 permutation5 75 (by rfl)).trans ((lex_skipped s permutation5 74 75 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation5 74) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation5 74 by rw [image5_eq]; rfl))

theorem lex_5_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3250) (Sat.Literal.pos 3249) (Sat.Literal.pos 74) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation5 74 (assignment s)
    (Sat.Literal.pos 3250) (Sat.Literal.pos 3249) (Sat.Literal.pos 74) (Sat.Literal.pos 42) (positive_of_descriptor s 3250 (.lex permutation5 74) (by rfl)) (lex_5_74_prefix s) (positive_select s 74) (lex_5_74_image s)

theorem lex_5_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.pos 74), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation5 74 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3249) (Sat.Literal.pos 74) (Sat.Literal.pos 42) (lex_5_74_prefix s) (positive_select s 74) (lex_5_74_image s)

theorem lex_5_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.pos 3249)] :=
  (lex_5_74_gate s).prop _ (List.Mem.head _)

theorem lex_5_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.neg 74), (Sat.Literal.pos 42)] :=
  (lex_5_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.pos 74), (Sat.Literal.neg 42)] :=
  (lex_5_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.neg 74), (Sat.Literal.neg 42), (Sat.Literal.pos 3250)] :=
  (lex_5_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3249), (Sat.Literal.pos 74), (Sat.Literal.pos 42), (Sat.Literal.pos 3250)] :=
  (lex_5_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3250) = lexBefore s permutation5 73 := by
  exact (positive_lex_of_descriptor s 3250 permutation5 74 (by rfl)).trans ((lex_skipped s permutation5 73 74 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation5 73) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation5 73 by rw [image5_eq]; rfl))

theorem lex_5_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3251) (Sat.Literal.pos 3250) (Sat.Literal.pos 73) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation5 73 (assignment s)
    (Sat.Literal.pos 3251) (Sat.Literal.pos 3250) (Sat.Literal.pos 73) (Sat.Literal.pos 41) (positive_of_descriptor s 3251 (.lex permutation5 73) (by rfl)) (lex_5_73_prefix s) (positive_select s 73) (lex_5_73_image s)

theorem lex_5_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.pos 73), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation5 73 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3250) (Sat.Literal.pos 73) (Sat.Literal.pos 41) (lex_5_73_prefix s) (positive_select s 73) (lex_5_73_image s)

theorem lex_5_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.pos 3250)] :=
  (lex_5_73_gate s).prop _ (List.Mem.head _)

theorem lex_5_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.neg 73), (Sat.Literal.pos 41)] :=
  (lex_5_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.pos 73), (Sat.Literal.neg 41)] :=
  (lex_5_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.neg 73), (Sat.Literal.neg 41), (Sat.Literal.pos 3251)] :=
  (lex_5_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3250), (Sat.Literal.pos 73), (Sat.Literal.pos 41), (Sat.Literal.pos 3251)] :=
  (lex_5_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3251) = lexBefore s permutation5 72 := by
  exact (positive_lex_of_descriptor s 3251 permutation5 73 (by rfl)).trans ((lex_skipped s permutation5 72 73 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation5 72) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation5 72 by rw [image5_eq]; rfl))

theorem lex_5_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3252) (Sat.Literal.pos 3251) (Sat.Literal.pos 72) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation5 72 (assignment s)
    (Sat.Literal.pos 3252) (Sat.Literal.pos 3251) (Sat.Literal.pos 72) (Sat.Literal.pos 40) (positive_of_descriptor s 3252 (.lex permutation5 72) (by rfl)) (lex_5_72_prefix s) (positive_select s 72) (lex_5_72_image s)

theorem lex_5_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.pos 72), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation5 72 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3251) (Sat.Literal.pos 72) (Sat.Literal.pos 40) (lex_5_72_prefix s) (positive_select s 72) (lex_5_72_image s)

theorem lex_5_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.pos 3251)] :=
  (lex_5_72_gate s).prop _ (List.Mem.head _)

theorem lex_5_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.neg 72), (Sat.Literal.pos 40)] :=
  (lex_5_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.pos 72), (Sat.Literal.neg 40)] :=
  (lex_5_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.neg 72), (Sat.Literal.neg 40), (Sat.Literal.pos 3252)] :=
  (lex_5_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3251), (Sat.Literal.pos 72), (Sat.Literal.pos 40), (Sat.Literal.pos 3252)] :=
  (lex_5_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3252) = lexBefore s permutation5 71 := by
  exact (positive_lex_of_descriptor s 3252 permutation5 72 (by rfl)).trans ((lex_skipped s permutation5 71 72 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation5 71) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation5 71 by rw [image5_eq]; rfl))

theorem lex_5_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3253) (Sat.Literal.pos 3252) (Sat.Literal.pos 71) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation5 71 (assignment s)
    (Sat.Literal.pos 3253) (Sat.Literal.pos 3252) (Sat.Literal.pos 71) (Sat.Literal.pos 39) (positive_of_descriptor s 3253 (.lex permutation5 71) (by rfl)) (lex_5_71_prefix s) (positive_select s 71) (lex_5_71_image s)

theorem lex_5_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.pos 71), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation5 71 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3252) (Sat.Literal.pos 71) (Sat.Literal.pos 39) (lex_5_71_prefix s) (positive_select s 71) (lex_5_71_image s)

theorem lex_5_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.pos 3252)] :=
  (lex_5_71_gate s).prop _ (List.Mem.head _)

theorem lex_5_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.neg 71), (Sat.Literal.pos 39)] :=
  (lex_5_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.pos 71), (Sat.Literal.neg 39)] :=
  (lex_5_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.neg 71), (Sat.Literal.neg 39), (Sat.Literal.pos 3253)] :=
  (lex_5_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3252), (Sat.Literal.pos 71), (Sat.Literal.pos 39), (Sat.Literal.pos 3253)] :=
  (lex_5_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3253) = lexBefore s permutation5 70 := by
  exact (positive_lex_of_descriptor s 3253 permutation5 71 (by rfl)).trans ((lex_skipped s permutation5 70 71 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation5 70) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation5 70 by rw [image5_eq]; rfl))

theorem lex_5_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3254) (Sat.Literal.pos 3253) (Sat.Literal.pos 70) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation5 70 (assignment s)
    (Sat.Literal.pos 3254) (Sat.Literal.pos 3253) (Sat.Literal.pos 70) (Sat.Literal.pos 38) (positive_of_descriptor s 3254 (.lex permutation5 70) (by rfl)) (lex_5_70_prefix s) (positive_select s 70) (lex_5_70_image s)

theorem lex_5_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.pos 70), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation5 70 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3253) (Sat.Literal.pos 70) (Sat.Literal.pos 38) (lex_5_70_prefix s) (positive_select s 70) (lex_5_70_image s)

theorem lex_5_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.pos 3253)] :=
  (lex_5_70_gate s).prop _ (List.Mem.head _)

theorem lex_5_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.neg 70), (Sat.Literal.pos 38)] :=
  (lex_5_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.pos 70), (Sat.Literal.neg 38)] :=
  (lex_5_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.neg 70), (Sat.Literal.neg 38), (Sat.Literal.pos 3254)] :=
  (lex_5_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3253), (Sat.Literal.pos 70), (Sat.Literal.pos 38), (Sat.Literal.pos 3254)] :=
  (lex_5_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3254) = lexBefore s permutation5 69 := by
  exact (positive_lex_of_descriptor s 3254 permutation5 70 (by rfl)).trans ((lex_skipped s permutation5 69 70 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation5 69) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation5 69 by rw [image5_eq]; rfl))

theorem lex_5_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3255) (Sat.Literal.pos 3254) (Sat.Literal.pos 69) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation5 69 (assignment s)
    (Sat.Literal.pos 3255) (Sat.Literal.pos 3254) (Sat.Literal.pos 69) (Sat.Literal.pos 37) (positive_of_descriptor s 3255 (.lex permutation5 69) (by rfl)) (lex_5_69_prefix s) (positive_select s 69) (lex_5_69_image s)

theorem lex_5_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.pos 69), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation5 69 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3254) (Sat.Literal.pos 69) (Sat.Literal.pos 37) (lex_5_69_prefix s) (positive_select s 69) (lex_5_69_image s)

theorem lex_5_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.pos 3254)] :=
  (lex_5_69_gate s).prop _ (List.Mem.head _)

theorem lex_5_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.neg 69), (Sat.Literal.pos 37)] :=
  (lex_5_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.pos 69), (Sat.Literal.neg 37)] :=
  (lex_5_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.neg 69), (Sat.Literal.neg 37), (Sat.Literal.pos 3255)] :=
  (lex_5_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3254), (Sat.Literal.pos 69), (Sat.Literal.pos 37), (Sat.Literal.pos 3255)] :=
  (lex_5_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3255) = lexBefore s permutation5 68 := by
  exact (positive_lex_of_descriptor s 3255 permutation5 69 (by rfl)).trans ((lex_skipped s permutation5 68 69 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation5 68) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation5 68 by rw [image5_eq]; rfl))

theorem lex_5_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3256) (Sat.Literal.pos 3255) (Sat.Literal.pos 68) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation5 68 (assignment s)
    (Sat.Literal.pos 3256) (Sat.Literal.pos 3255) (Sat.Literal.pos 68) (Sat.Literal.pos 36) (positive_of_descriptor s 3256 (.lex permutation5 68) (by rfl)) (lex_5_68_prefix s) (positive_select s 68) (lex_5_68_image s)

theorem lex_5_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.pos 68), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation5 68 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3255) (Sat.Literal.pos 68) (Sat.Literal.pos 36) (lex_5_68_prefix s) (positive_select s 68) (lex_5_68_image s)

theorem lex_5_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.pos 3255)] :=
  (lex_5_68_gate s).prop _ (List.Mem.head _)

theorem lex_5_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.neg 68), (Sat.Literal.pos 36)] :=
  (lex_5_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.pos 68), (Sat.Literal.neg 36)] :=
  (lex_5_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.neg 68), (Sat.Literal.neg 36), (Sat.Literal.pos 3256)] :=
  (lex_5_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3255), (Sat.Literal.pos 68), (Sat.Literal.pos 36), (Sat.Literal.pos 3256)] :=
  (lex_5_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3256) = lexBefore s permutation5 67 := by
  exact (positive_lex_of_descriptor s 3256 permutation5 68 (by rfl)).trans ((lex_skipped s permutation5 67 68 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation5 67) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation5 67 by rw [image5_eq]; rfl))

theorem lex_5_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3257) (Sat.Literal.pos 3256) (Sat.Literal.pos 67) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation5 67 (assignment s)
    (Sat.Literal.pos 3257) (Sat.Literal.pos 3256) (Sat.Literal.pos 67) (Sat.Literal.pos 35) (positive_of_descriptor s 3257 (.lex permutation5 67) (by rfl)) (lex_5_67_prefix s) (positive_select s 67) (lex_5_67_image s)

theorem lex_5_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.pos 67), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation5 67 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3256) (Sat.Literal.pos 67) (Sat.Literal.pos 35) (lex_5_67_prefix s) (positive_select s 67) (lex_5_67_image s)

theorem lex_5_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.pos 3256)] :=
  (lex_5_67_gate s).prop _ (List.Mem.head _)

theorem lex_5_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.neg 67), (Sat.Literal.pos 35)] :=
  (lex_5_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.pos 67), (Sat.Literal.neg 35)] :=
  (lex_5_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.neg 67), (Sat.Literal.neg 35), (Sat.Literal.pos 3257)] :=
  (lex_5_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3256), (Sat.Literal.pos 67), (Sat.Literal.pos 35), (Sat.Literal.pos 3257)] :=
  (lex_5_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3257) = lexBefore s permutation5 66 := by
  exact (positive_lex_of_descriptor s 3257 permutation5 67 (by rfl)).trans ((lex_skipped s permutation5 66 67 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation5 66) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation5 66 by rw [image5_eq]; rfl))

theorem lex_5_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3258) (Sat.Literal.pos 3257) (Sat.Literal.pos 66) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation5 66 (assignment s)
    (Sat.Literal.pos 3258) (Sat.Literal.pos 3257) (Sat.Literal.pos 66) (Sat.Literal.pos 34) (positive_of_descriptor s 3258 (.lex permutation5 66) (by rfl)) (lex_5_66_prefix s) (positive_select s 66) (lex_5_66_image s)

theorem lex_5_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.pos 66), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation5 66 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3257) (Sat.Literal.pos 66) (Sat.Literal.pos 34) (lex_5_66_prefix s) (positive_select s 66) (lex_5_66_image s)

theorem lex_5_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.pos 3257)] :=
  (lex_5_66_gate s).prop _ (List.Mem.head _)

theorem lex_5_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.neg 66), (Sat.Literal.pos 34)] :=
  (lex_5_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.pos 66), (Sat.Literal.neg 34)] :=
  (lex_5_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.neg 66), (Sat.Literal.neg 34), (Sat.Literal.pos 3258)] :=
  (lex_5_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3257), (Sat.Literal.pos 66), (Sat.Literal.pos 34), (Sat.Literal.pos 3258)] :=
  (lex_5_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3258) = lexBefore s permutation5 65 := by
  exact (positive_lex_of_descriptor s 3258 permutation5 66 (by rfl)).trans ((lex_skipped s permutation5 65 66 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation5 65) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation5 65 by rw [image5_eq]; rfl))

theorem lex_5_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3259) (Sat.Literal.pos 3258) (Sat.Literal.pos 65) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation5 65 (assignment s)
    (Sat.Literal.pos 3259) (Sat.Literal.pos 3258) (Sat.Literal.pos 65) (Sat.Literal.pos 33) (positive_of_descriptor s 3259 (.lex permutation5 65) (by rfl)) (lex_5_65_prefix s) (positive_select s 65) (lex_5_65_image s)

theorem lex_5_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.pos 65), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation5 65 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3258) (Sat.Literal.pos 65) (Sat.Literal.pos 33) (lex_5_65_prefix s) (positive_select s 65) (lex_5_65_image s)

theorem lex_5_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.pos 3258)] :=
  (lex_5_65_gate s).prop _ (List.Mem.head _)

theorem lex_5_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.neg 65), (Sat.Literal.pos 33)] :=
  (lex_5_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.pos 65), (Sat.Literal.neg 33)] :=
  (lex_5_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.neg 65), (Sat.Literal.neg 33), (Sat.Literal.pos 3259)] :=
  (lex_5_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3258), (Sat.Literal.pos 65), (Sat.Literal.pos 33), (Sat.Literal.pos 3259)] :=
  (lex_5_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3259) = lexBefore s permutation5 64 := by
  exact (positive_lex_of_descriptor s 3259 permutation5 65 (by rfl)).trans ((lex_skipped s permutation5 64 65 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation5 64) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation5 64 by rw [image5_eq]; rfl))

theorem lex_5_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3260) (Sat.Literal.pos 3259) (Sat.Literal.pos 64) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation5 64 (assignment s)
    (Sat.Literal.pos 3260) (Sat.Literal.pos 3259) (Sat.Literal.pos 64) (Sat.Literal.pos 32) (positive_of_descriptor s 3260 (.lex permutation5 64) (by rfl)) (lex_5_64_prefix s) (positive_select s 64) (lex_5_64_image s)

theorem lex_5_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.pos 64), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation5 64 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3259) (Sat.Literal.pos 64) (Sat.Literal.pos 32) (lex_5_64_prefix s) (positive_select s 64) (lex_5_64_image s)

theorem lex_5_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.pos 3259)] :=
  (lex_5_64_gate s).prop _ (List.Mem.head _)

theorem lex_5_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.neg 64), (Sat.Literal.pos 32)] :=
  (lex_5_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.pos 64), (Sat.Literal.neg 32)] :=
  (lex_5_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.neg 64), (Sat.Literal.neg 32), (Sat.Literal.pos 3260)] :=
  (lex_5_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3259), (Sat.Literal.pos 64), (Sat.Literal.pos 32), (Sat.Literal.pos 3260)] :=
  (lex_5_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3260) = lexBefore s permutation5 63 := by
  exact (positive_lex_of_descriptor s 3260 permutation5 64 (by rfl)).trans ((lex_skipped s permutation5 63 64 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation5 63) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation5 63 by rw [image5_eq]; rfl))

theorem lex_5_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3261) (Sat.Literal.pos 3260) (Sat.Literal.pos 63) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation5 63 (assignment s)
    (Sat.Literal.pos 3261) (Sat.Literal.pos 3260) (Sat.Literal.pos 63) (Sat.Literal.pos 95) (positive_of_descriptor s 3261 (.lex permutation5 63) (by rfl)) (lex_5_63_prefix s) (positive_select s 63) (lex_5_63_image s)

theorem lex_5_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.pos 63), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation5 63 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3260) (Sat.Literal.pos 63) (Sat.Literal.pos 95) (lex_5_63_prefix s) (positive_select s 63) (lex_5_63_image s)

theorem lex_5_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.pos 3260)] :=
  (lex_5_63_gate s).prop _ (List.Mem.head _)

theorem lex_5_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.neg 63), (Sat.Literal.pos 95)] :=
  (lex_5_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.pos 63), (Sat.Literal.neg 95)] :=
  (lex_5_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.neg 63), (Sat.Literal.neg 95), (Sat.Literal.pos 3261)] :=
  (lex_5_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3260), (Sat.Literal.pos 63), (Sat.Literal.pos 95), (Sat.Literal.pos 3261)] :=
  (lex_5_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3261) = lexBefore s permutation5 62 := by
  exact (positive_lex_of_descriptor s 3261 permutation5 63 (by rfl)).trans ((lex_skipped s permutation5 62 63 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation5 62) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation5 62 by rw [image5_eq]; rfl))

theorem lex_5_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3262) (Sat.Literal.pos 3261) (Sat.Literal.pos 62) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation5 62 (assignment s)
    (Sat.Literal.pos 3262) (Sat.Literal.pos 3261) (Sat.Literal.pos 62) (Sat.Literal.pos 94) (positive_of_descriptor s 3262 (.lex permutation5 62) (by rfl)) (lex_5_62_prefix s) (positive_select s 62) (lex_5_62_image s)

theorem lex_5_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.pos 62), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation5 62 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3261) (Sat.Literal.pos 62) (Sat.Literal.pos 94) (lex_5_62_prefix s) (positive_select s 62) (lex_5_62_image s)

theorem lex_5_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.pos 3261)] :=
  (lex_5_62_gate s).prop _ (List.Mem.head _)

theorem lex_5_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.neg 62), (Sat.Literal.pos 94)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.pos 62), (Sat.Literal.neg 94)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.neg 62), (Sat.Literal.neg 94), (Sat.Literal.pos 3262)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3261), (Sat.Literal.pos 62), (Sat.Literal.pos 94), (Sat.Literal.pos 3262)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3262) = lexBefore s permutation5 61 := by
  exact (positive_lex_of_descriptor s 3262 permutation5 62 (by rfl)).trans ((lex_skipped s permutation5 61 62 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation5 61) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation5 61 by rw [image5_eq]; rfl))

theorem lex_5_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3263) (Sat.Literal.pos 3262) (Sat.Literal.pos 61) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation5 61 (assignment s)
    (Sat.Literal.pos 3263) (Sat.Literal.pos 3262) (Sat.Literal.pos 61) (Sat.Literal.pos 93) (positive_of_descriptor s 3263 (.lex permutation5 61) (by rfl)) (lex_5_61_prefix s) (positive_select s 61) (lex_5_61_image s)

theorem lex_5_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.pos 61), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation5 61 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3262) (Sat.Literal.pos 61) (Sat.Literal.pos 93) (lex_5_61_prefix s) (positive_select s 61) (lex_5_61_image s)

theorem lex_5_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.pos 3262)] :=
  (lex_5_61_gate s).prop _ (List.Mem.head _)

theorem lex_5_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.neg 61), (Sat.Literal.pos 93)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.pos 61), (Sat.Literal.neg 93)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.neg 61), (Sat.Literal.neg 93), (Sat.Literal.pos 3263)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3262), (Sat.Literal.pos 61), (Sat.Literal.pos 93), (Sat.Literal.pos 3263)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3263) = lexBefore s permutation5 60 := by
  exact (positive_lex_of_descriptor s 3263 permutation5 61 (by rfl)).trans ((lex_skipped s permutation5 60 61 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation5 60) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation5 60 by rw [image5_eq]; rfl))

theorem lex_5_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3264) (Sat.Literal.pos 3263) (Sat.Literal.pos 60) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation5 60 (assignment s)
    (Sat.Literal.pos 3264) (Sat.Literal.pos 3263) (Sat.Literal.pos 60) (Sat.Literal.pos 92) (positive_of_descriptor s 3264 (.lex permutation5 60) (by rfl)) (lex_5_60_prefix s) (positive_select s 60) (lex_5_60_image s)

theorem lex_5_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.pos 60), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation5 60 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3263) (Sat.Literal.pos 60) (Sat.Literal.pos 92) (lex_5_60_prefix s) (positive_select s 60) (lex_5_60_image s)

theorem lex_5_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.pos 3263)] :=
  (lex_5_60_gate s).prop _ (List.Mem.head _)

theorem lex_5_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.neg 60), (Sat.Literal.pos 92)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.pos 60), (Sat.Literal.neg 92)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.neg 60), (Sat.Literal.neg 92), (Sat.Literal.pos 3264)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3263), (Sat.Literal.pos 60), (Sat.Literal.pos 92), (Sat.Literal.pos 3264)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3264) = lexBefore s permutation5 59 := by
  exact (positive_lex_of_descriptor s 3264 permutation5 60 (by rfl)).trans ((lex_skipped s permutation5 59 60 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation5 59) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation5 59 by rw [image5_eq]; rfl))

theorem lex_5_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3265) (Sat.Literal.pos 3264) (Sat.Literal.pos 59) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation5 59 (assignment s)
    (Sat.Literal.pos 3265) (Sat.Literal.pos 3264) (Sat.Literal.pos 59) (Sat.Literal.pos 91) (positive_of_descriptor s 3265 (.lex permutation5 59) (by rfl)) (lex_5_59_prefix s) (positive_select s 59) (lex_5_59_image s)

theorem lex_5_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.pos 59), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation5 59 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3264) (Sat.Literal.pos 59) (Sat.Literal.pos 91) (lex_5_59_prefix s) (positive_select s 59) (lex_5_59_image s)

theorem lex_5_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.pos 3264)] :=
  (lex_5_59_gate s).prop _ (List.Mem.head _)

theorem lex_5_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.neg 59), (Sat.Literal.pos 91)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.pos 59), (Sat.Literal.neg 91)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.neg 59), (Sat.Literal.neg 91), (Sat.Literal.pos 3265)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3264), (Sat.Literal.pos 59), (Sat.Literal.pos 91), (Sat.Literal.pos 3265)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3265) = lexBefore s permutation5 58 := by
  exact (positive_lex_of_descriptor s 3265 permutation5 59 (by rfl)).trans ((lex_skipped s permutation5 58 59 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation5 58) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation5 58 by rw [image5_eq]; rfl))

theorem lex_5_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3266) (Sat.Literal.pos 3265) (Sat.Literal.pos 58) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation5 58 (assignment s)
    (Sat.Literal.pos 3266) (Sat.Literal.pos 3265) (Sat.Literal.pos 58) (Sat.Literal.pos 90) (positive_of_descriptor s 3266 (.lex permutation5 58) (by rfl)) (lex_5_58_prefix s) (positive_select s 58) (lex_5_58_image s)

theorem lex_5_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.pos 58), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation5 58 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3265) (Sat.Literal.pos 58) (Sat.Literal.pos 90) (lex_5_58_prefix s) (positive_select s 58) (lex_5_58_image s)

theorem lex_5_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.pos 3265)] :=
  (lex_5_58_gate s).prop _ (List.Mem.head _)

theorem lex_5_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.neg 58), (Sat.Literal.pos 90)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.pos 58), (Sat.Literal.neg 90)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.neg 58), (Sat.Literal.neg 90), (Sat.Literal.pos 3266)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3265), (Sat.Literal.pos 58), (Sat.Literal.pos 90), (Sat.Literal.pos 3266)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3266) = lexBefore s permutation5 57 := by
  exact (positive_lex_of_descriptor s 3266 permutation5 58 (by rfl)).trans ((lex_skipped s permutation5 57 58 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation5 57) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation5 57 by rw [image5_eq]; rfl))

theorem lex_5_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3267) (Sat.Literal.pos 3266) (Sat.Literal.pos 57) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation5 57 (assignment s)
    (Sat.Literal.pos 3267) (Sat.Literal.pos 3266) (Sat.Literal.pos 57) (Sat.Literal.pos 89) (positive_of_descriptor s 3267 (.lex permutation5 57) (by rfl)) (lex_5_57_prefix s) (positive_select s 57) (lex_5_57_image s)

theorem lex_5_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.pos 57), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation5 57 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3266) (Sat.Literal.pos 57) (Sat.Literal.pos 89) (lex_5_57_prefix s) (positive_select s 57) (lex_5_57_image s)

theorem lex_5_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.pos 3266)] :=
  (lex_5_57_gate s).prop _ (List.Mem.head _)

theorem lex_5_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.neg 57), (Sat.Literal.pos 89)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.pos 57), (Sat.Literal.neg 89)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.neg 57), (Sat.Literal.neg 89), (Sat.Literal.pos 3267)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3266), (Sat.Literal.pos 57), (Sat.Literal.pos 89), (Sat.Literal.pos 3267)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3267) = lexBefore s permutation5 56 := by
  exact (positive_lex_of_descriptor s 3267 permutation5 57 (by rfl)).trans ((lex_skipped s permutation5 56 57 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation5 56) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation5 56 by rw [image5_eq]; rfl))

theorem lex_5_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3268) (Sat.Literal.pos 3267) (Sat.Literal.pos 56) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation5 56 (assignment s)
    (Sat.Literal.pos 3268) (Sat.Literal.pos 3267) (Sat.Literal.pos 56) (Sat.Literal.pos 88) (positive_of_descriptor s 3268 (.lex permutation5 56) (by rfl)) (lex_5_56_prefix s) (positive_select s 56) (lex_5_56_image s)

theorem lex_5_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.pos 56), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation5 56 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3267) (Sat.Literal.pos 56) (Sat.Literal.pos 88) (lex_5_56_prefix s) (positive_select s 56) (lex_5_56_image s)

theorem lex_5_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.pos 3267)] :=
  (lex_5_56_gate s).prop _ (List.Mem.head _)

theorem lex_5_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.neg 56), (Sat.Literal.pos 88)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.pos 56), (Sat.Literal.neg 88)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.neg 56), (Sat.Literal.neg 88), (Sat.Literal.pos 3268)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3267), (Sat.Literal.pos 56), (Sat.Literal.pos 88), (Sat.Literal.pos 3268)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3268) = lexBefore s permutation5 55 := by
  exact (positive_lex_of_descriptor s 3268 permutation5 56 (by rfl)).trans ((lex_skipped s permutation5 55 56 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation5 55) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation5 55 by rw [image5_eq]; rfl))

theorem lex_5_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3269) (Sat.Literal.pos 3268) (Sat.Literal.pos 55) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation5 55 (assignment s)
    (Sat.Literal.pos 3269) (Sat.Literal.pos 3268) (Sat.Literal.pos 55) (Sat.Literal.pos 87) (positive_of_descriptor s 3269 (.lex permutation5 55) (by rfl)) (lex_5_55_prefix s) (positive_select s 55) (lex_5_55_image s)

theorem lex_5_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.pos 55), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation5 55 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3268) (Sat.Literal.pos 55) (Sat.Literal.pos 87) (lex_5_55_prefix s) (positive_select s 55) (lex_5_55_image s)

theorem lex_5_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.pos 3268)] :=
  (lex_5_55_gate s).prop _ (List.Mem.head _)

theorem lex_5_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.neg 55), (Sat.Literal.pos 87)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.pos 55), (Sat.Literal.neg 87)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.neg 55), (Sat.Literal.neg 87), (Sat.Literal.pos 3269)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3268), (Sat.Literal.pos 55), (Sat.Literal.pos 87), (Sat.Literal.pos 3269)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3269) = lexBefore s permutation5 54 := by
  exact (positive_lex_of_descriptor s 3269 permutation5 55 (by rfl)).trans ((lex_skipped s permutation5 54 55 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation5 54) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation5 54 by rw [image5_eq]; rfl))

theorem lex_5_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3270) (Sat.Literal.pos 3269) (Sat.Literal.pos 54) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation5 54 (assignment s)
    (Sat.Literal.pos 3270) (Sat.Literal.pos 3269) (Sat.Literal.pos 54) (Sat.Literal.pos 86) (positive_of_descriptor s 3270 (.lex permutation5 54) (by rfl)) (lex_5_54_prefix s) (positive_select s 54) (lex_5_54_image s)

theorem lex_5_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.pos 54), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation5 54 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3269) (Sat.Literal.pos 54) (Sat.Literal.pos 86) (lex_5_54_prefix s) (positive_select s 54) (lex_5_54_image s)

theorem lex_5_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.pos 3269)] :=
  (lex_5_54_gate s).prop _ (List.Mem.head _)

theorem lex_5_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.neg 54), (Sat.Literal.pos 86)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.pos 54), (Sat.Literal.neg 86)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.neg 54), (Sat.Literal.neg 86), (Sat.Literal.pos 3270)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3269), (Sat.Literal.pos 54), (Sat.Literal.pos 86), (Sat.Literal.pos 3270)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3270) = lexBefore s permutation5 53 := by
  exact (positive_lex_of_descriptor s 3270 permutation5 54 (by rfl)).trans ((lex_skipped s permutation5 53 54 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation5 53) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation5 53 by rw [image5_eq]; rfl))

theorem lex_5_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3271) (Sat.Literal.pos 3270) (Sat.Literal.pos 53) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation5 53 (assignment s)
    (Sat.Literal.pos 3271) (Sat.Literal.pos 3270) (Sat.Literal.pos 53) (Sat.Literal.pos 85) (positive_of_descriptor s 3271 (.lex permutation5 53) (by rfl)) (lex_5_53_prefix s) (positive_select s 53) (lex_5_53_image s)

theorem lex_5_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.pos 53), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation5 53 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3270) (Sat.Literal.pos 53) (Sat.Literal.pos 85) (lex_5_53_prefix s) (positive_select s 53) (lex_5_53_image s)

theorem lex_5_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.pos 3270)] :=
  (lex_5_53_gate s).prop _ (List.Mem.head _)

theorem lex_5_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.neg 53), (Sat.Literal.pos 85)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.pos 53), (Sat.Literal.neg 85)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.neg 53), (Sat.Literal.neg 85), (Sat.Literal.pos 3271)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3270), (Sat.Literal.pos 53), (Sat.Literal.pos 85), (Sat.Literal.pos 3271)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3271) = lexBefore s permutation5 52 := by
  exact (positive_lex_of_descriptor s 3271 permutation5 53 (by rfl)).trans ((lex_skipped s permutation5 52 53 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation5 52) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation5 52 by rw [image5_eq]; rfl))

theorem lex_5_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3272) (Sat.Literal.pos 3271) (Sat.Literal.pos 52) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation5 52 (assignment s)
    (Sat.Literal.pos 3272) (Sat.Literal.pos 3271) (Sat.Literal.pos 52) (Sat.Literal.pos 84) (positive_of_descriptor s 3272 (.lex permutation5 52) (by rfl)) (lex_5_52_prefix s) (positive_select s 52) (lex_5_52_image s)

theorem lex_5_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.pos 52), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation5 52 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3271) (Sat.Literal.pos 52) (Sat.Literal.pos 84) (lex_5_52_prefix s) (positive_select s 52) (lex_5_52_image s)

theorem lex_5_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.pos 3271)] :=
  (lex_5_52_gate s).prop _ (List.Mem.head _)

theorem lex_5_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.neg 52), (Sat.Literal.pos 84)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.pos 52), (Sat.Literal.neg 84)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.neg 52), (Sat.Literal.neg 84), (Sat.Literal.pos 3272)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3271), (Sat.Literal.pos 52), (Sat.Literal.pos 84), (Sat.Literal.pos 3272)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3272) = lexBefore s permutation5 51 := by
  exact (positive_lex_of_descriptor s 3272 permutation5 52 (by rfl)).trans ((lex_skipped s permutation5 51 52 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation5 51) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation5 51 by rw [image5_eq]; rfl))

theorem lex_5_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3273) (Sat.Literal.pos 3272) (Sat.Literal.pos 51) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation5 51 (assignment s)
    (Sat.Literal.pos 3273) (Sat.Literal.pos 3272) (Sat.Literal.pos 51) (Sat.Literal.pos 83) (positive_of_descriptor s 3273 (.lex permutation5 51) (by rfl)) (lex_5_51_prefix s) (positive_select s 51) (lex_5_51_image s)

theorem lex_5_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.pos 51), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation5 51 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3272) (Sat.Literal.pos 51) (Sat.Literal.pos 83) (lex_5_51_prefix s) (positive_select s 51) (lex_5_51_image s)

theorem lex_5_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.pos 3272)] :=
  (lex_5_51_gate s).prop _ (List.Mem.head _)

theorem lex_5_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.neg 51), (Sat.Literal.pos 83)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.pos 51), (Sat.Literal.neg 83)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.neg 51), (Sat.Literal.neg 83), (Sat.Literal.pos 3273)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3272), (Sat.Literal.pos 51), (Sat.Literal.pos 83), (Sat.Literal.pos 3273)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3273) = lexBefore s permutation5 50 := by
  exact (positive_lex_of_descriptor s 3273 permutation5 51 (by rfl)).trans ((lex_skipped s permutation5 50 51 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation5 50) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation5 50 by rw [image5_eq]; rfl))

theorem lex_5_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3274) (Sat.Literal.pos 3273) (Sat.Literal.pos 50) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation5 50 (assignment s)
    (Sat.Literal.pos 3274) (Sat.Literal.pos 3273) (Sat.Literal.pos 50) (Sat.Literal.pos 82) (positive_of_descriptor s 3274 (.lex permutation5 50) (by rfl)) (lex_5_50_prefix s) (positive_select s 50) (lex_5_50_image s)

theorem lex_5_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.pos 50), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation5 50 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3273) (Sat.Literal.pos 50) (Sat.Literal.pos 82) (lex_5_50_prefix s) (positive_select s 50) (lex_5_50_image s)

theorem lex_5_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.pos 3273)] :=
  (lex_5_50_gate s).prop _ (List.Mem.head _)

theorem lex_5_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.neg 50), (Sat.Literal.pos 82)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.pos 50), (Sat.Literal.neg 82)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.neg 50), (Sat.Literal.neg 82), (Sat.Literal.pos 3274)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3273), (Sat.Literal.pos 50), (Sat.Literal.pos 82), (Sat.Literal.pos 3274)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3274) = lexBefore s permutation5 49 := by
  exact (positive_lex_of_descriptor s 3274 permutation5 50 (by rfl)).trans ((lex_skipped s permutation5 49 50 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation5 49) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation5 49 by rw [image5_eq]; rfl))

theorem lex_5_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3275) (Sat.Literal.pos 3274) (Sat.Literal.pos 49) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation5 49 (assignment s)
    (Sat.Literal.pos 3275) (Sat.Literal.pos 3274) (Sat.Literal.pos 49) (Sat.Literal.pos 81) (positive_of_descriptor s 3275 (.lex permutation5 49) (by rfl)) (lex_5_49_prefix s) (positive_select s 49) (lex_5_49_image s)

theorem lex_5_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.pos 49), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation5 49 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3274) (Sat.Literal.pos 49) (Sat.Literal.pos 81) (lex_5_49_prefix s) (positive_select s 49) (lex_5_49_image s)

theorem lex_5_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.pos 3274)] :=
  (lex_5_49_gate s).prop _ (List.Mem.head _)

theorem lex_5_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.neg 49), (Sat.Literal.pos 81)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.pos 49), (Sat.Literal.neg 81)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.neg 49), (Sat.Literal.neg 81), (Sat.Literal.pos 3275)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3274), (Sat.Literal.pos 49), (Sat.Literal.pos 81), (Sat.Literal.pos 3275)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3275) = lexBefore s permutation5 48 := by
  exact (positive_lex_of_descriptor s 3275 permutation5 49 (by rfl)).trans ((lex_skipped s permutation5 48 49 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation5 48) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation5 48 by rw [image5_eq]; rfl))

theorem lex_5_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3276) (Sat.Literal.pos 3275) (Sat.Literal.pos 48) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation5 48 (assignment s)
    (Sat.Literal.pos 3276) (Sat.Literal.pos 3275) (Sat.Literal.pos 48) (Sat.Literal.pos 80) (positive_of_descriptor s 3276 (.lex permutation5 48) (by rfl)) (lex_5_48_prefix s) (positive_select s 48) (lex_5_48_image s)

theorem lex_5_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.pos 48), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation5 48 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3275) (Sat.Literal.pos 48) (Sat.Literal.pos 80) (lex_5_48_prefix s) (positive_select s 48) (lex_5_48_image s)

theorem lex_5_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.pos 3275)] :=
  (lex_5_48_gate s).prop _ (List.Mem.head _)

theorem lex_5_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.neg 48), (Sat.Literal.pos 80)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.pos 48), (Sat.Literal.neg 80)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.neg 48), (Sat.Literal.neg 80), (Sat.Literal.pos 3276)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3275), (Sat.Literal.pos 48), (Sat.Literal.pos 80), (Sat.Literal.pos 3276)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3276) = lexBefore s permutation5 47 := by
  exact (positive_lex_of_descriptor s 3276 permutation5 48 (by rfl)).trans ((lex_skipped s permutation5 47 48 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation5 47) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation5 47 by rw [image5_eq]; rfl))

theorem lex_5_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3277) (Sat.Literal.pos 3276) (Sat.Literal.pos 47) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation5 47 (assignment s)
    (Sat.Literal.pos 3277) (Sat.Literal.pos 3276) (Sat.Literal.pos 47) (Sat.Literal.pos 79) (positive_of_descriptor s 3277 (.lex permutation5 47) (by rfl)) (lex_5_47_prefix s) (positive_select s 47) (lex_5_47_image s)

theorem lex_5_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.pos 47), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation5 47 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3276) (Sat.Literal.pos 47) (Sat.Literal.pos 79) (lex_5_47_prefix s) (positive_select s 47) (lex_5_47_image s)

theorem lex_5_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.pos 3276)] :=
  (lex_5_47_gate s).prop _ (List.Mem.head _)

theorem lex_5_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.neg 47), (Sat.Literal.pos 79)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.pos 47), (Sat.Literal.neg 79)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.neg 47), (Sat.Literal.neg 79), (Sat.Literal.pos 3277)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3276), (Sat.Literal.pos 47), (Sat.Literal.pos 79), (Sat.Literal.pos 3277)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3277) = lexBefore s permutation5 46 := by
  exact (positive_lex_of_descriptor s 3277 permutation5 47 (by rfl)).trans ((lex_skipped s permutation5 46 47 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation5 46) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation5 46 by rw [image5_eq]; rfl))

theorem lex_5_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3278) (Sat.Literal.pos 3277) (Sat.Literal.pos 46) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation5 46 (assignment s)
    (Sat.Literal.pos 3278) (Sat.Literal.pos 3277) (Sat.Literal.pos 46) (Sat.Literal.pos 78) (positive_of_descriptor s 3278 (.lex permutation5 46) (by rfl)) (lex_5_46_prefix s) (positive_select s 46) (lex_5_46_image s)

theorem lex_5_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.pos 46), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation5 46 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3277) (Sat.Literal.pos 46) (Sat.Literal.pos 78) (lex_5_46_prefix s) (positive_select s 46) (lex_5_46_image s)

theorem lex_5_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.pos 3277)] :=
  (lex_5_46_gate s).prop _ (List.Mem.head _)

theorem lex_5_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.neg 46), (Sat.Literal.pos 78)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.pos 46), (Sat.Literal.neg 78)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.neg 46), (Sat.Literal.neg 78), (Sat.Literal.pos 3278)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3277), (Sat.Literal.pos 46), (Sat.Literal.pos 78), (Sat.Literal.pos 3278)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3278) = lexBefore s permutation5 45 := by
  exact (positive_lex_of_descriptor s 3278 permutation5 46 (by rfl)).trans ((lex_skipped s permutation5 45 46 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation5 45) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation5 45 by rw [image5_eq]; rfl))

theorem lex_5_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3279) (Sat.Literal.pos 3278) (Sat.Literal.pos 45) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation5 45 (assignment s)
    (Sat.Literal.pos 3279) (Sat.Literal.pos 3278) (Sat.Literal.pos 45) (Sat.Literal.pos 77) (positive_of_descriptor s 3279 (.lex permutation5 45) (by rfl)) (lex_5_45_prefix s) (positive_select s 45) (lex_5_45_image s)

theorem lex_5_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.pos 45), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation5 45 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3278) (Sat.Literal.pos 45) (Sat.Literal.pos 77) (lex_5_45_prefix s) (positive_select s 45) (lex_5_45_image s)

theorem lex_5_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.pos 3278)] :=
  (lex_5_45_gate s).prop _ (List.Mem.head _)

theorem lex_5_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.neg 45), (Sat.Literal.pos 77)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.pos 45), (Sat.Literal.neg 77)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.neg 45), (Sat.Literal.neg 77), (Sat.Literal.pos 3279)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3278), (Sat.Literal.pos 45), (Sat.Literal.pos 77), (Sat.Literal.pos 3279)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3279) = lexBefore s permutation5 44 := by
  exact (positive_lex_of_descriptor s 3279 permutation5 45 (by rfl)).trans ((lex_skipped s permutation5 44 45 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation5 44) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation5 44 by rw [image5_eq]; rfl))

theorem lex_5_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3280) (Sat.Literal.pos 3279) (Sat.Literal.pos 44) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation5 44 (assignment s)
    (Sat.Literal.pos 3280) (Sat.Literal.pos 3279) (Sat.Literal.pos 44) (Sat.Literal.pos 76) (positive_of_descriptor s 3280 (.lex permutation5 44) (by rfl)) (lex_5_44_prefix s) (positive_select s 44) (lex_5_44_image s)

theorem lex_5_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.pos 44), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation5 44 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3279) (Sat.Literal.pos 44) (Sat.Literal.pos 76) (lex_5_44_prefix s) (positive_select s 44) (lex_5_44_image s)

theorem lex_5_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.pos 3279)] :=
  (lex_5_44_gate s).prop _ (List.Mem.head _)

theorem lex_5_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.neg 44), (Sat.Literal.pos 76)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.pos 44), (Sat.Literal.neg 76)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.neg 44), (Sat.Literal.neg 76), (Sat.Literal.pos 3280)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3279), (Sat.Literal.pos 44), (Sat.Literal.pos 76), (Sat.Literal.pos 3280)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3280) = lexBefore s permutation5 43 := by
  exact (positive_lex_of_descriptor s 3280 permutation5 44 (by rfl)).trans ((lex_skipped s permutation5 43 44 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation5 43) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation5 43 by rw [image5_eq]; rfl))

theorem lex_5_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3281) (Sat.Literal.pos 3280) (Sat.Literal.pos 43) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation5 43 (assignment s)
    (Sat.Literal.pos 3281) (Sat.Literal.pos 3280) (Sat.Literal.pos 43) (Sat.Literal.pos 75) (positive_of_descriptor s 3281 (.lex permutation5 43) (by rfl)) (lex_5_43_prefix s) (positive_select s 43) (lex_5_43_image s)

theorem lex_5_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.pos 43), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation5 43 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3280) (Sat.Literal.pos 43) (Sat.Literal.pos 75) (lex_5_43_prefix s) (positive_select s 43) (lex_5_43_image s)

theorem lex_5_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.pos 3280)] :=
  (lex_5_43_gate s).prop _ (List.Mem.head _)

theorem lex_5_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.neg 43), (Sat.Literal.pos 75)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.pos 43), (Sat.Literal.neg 75)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.neg 43), (Sat.Literal.neg 75), (Sat.Literal.pos 3281)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3280), (Sat.Literal.pos 43), (Sat.Literal.pos 75), (Sat.Literal.pos 3281)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3281) = lexBefore s permutation5 42 := by
  exact (positive_lex_of_descriptor s 3281 permutation5 43 (by rfl)).trans ((lex_skipped s permutation5 42 43 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation5 42) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation5 42 by rw [image5_eq]; rfl))

theorem lex_5_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3282) (Sat.Literal.pos 3281) (Sat.Literal.pos 42) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation5 42 (assignment s)
    (Sat.Literal.pos 3282) (Sat.Literal.pos 3281) (Sat.Literal.pos 42) (Sat.Literal.pos 74) (positive_of_descriptor s 3282 (.lex permutation5 42) (by rfl)) (lex_5_42_prefix s) (positive_select s 42) (lex_5_42_image s)

theorem lex_5_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.pos 42), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation5 42 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3281) (Sat.Literal.pos 42) (Sat.Literal.pos 74) (lex_5_42_prefix s) (positive_select s 42) (lex_5_42_image s)

theorem lex_5_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.pos 3281)] :=
  (lex_5_42_gate s).prop _ (List.Mem.head _)

theorem lex_5_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.neg 42), (Sat.Literal.pos 74)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.pos 42), (Sat.Literal.neg 74)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.neg 42), (Sat.Literal.neg 74), (Sat.Literal.pos 3282)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3281), (Sat.Literal.pos 42), (Sat.Literal.pos 74), (Sat.Literal.pos 3282)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3282) = lexBefore s permutation5 41 := by
  exact (positive_lex_of_descriptor s 3282 permutation5 42 (by rfl)).trans ((lex_skipped s permutation5 41 42 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation5 41) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation5 41 by rw [image5_eq]; rfl))

theorem lex_5_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3283) (Sat.Literal.pos 3282) (Sat.Literal.pos 41) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation5 41 (assignment s)
    (Sat.Literal.pos 3283) (Sat.Literal.pos 3282) (Sat.Literal.pos 41) (Sat.Literal.pos 73) (positive_of_descriptor s 3283 (.lex permutation5 41) (by rfl)) (lex_5_41_prefix s) (positive_select s 41) (lex_5_41_image s)

theorem lex_5_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.pos 41), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation5 41 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3282) (Sat.Literal.pos 41) (Sat.Literal.pos 73) (lex_5_41_prefix s) (positive_select s 41) (lex_5_41_image s)

theorem lex_5_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.pos 3282)] :=
  (lex_5_41_gate s).prop _ (List.Mem.head _)

theorem lex_5_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.neg 41), (Sat.Literal.pos 73)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.pos 41), (Sat.Literal.neg 73)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.neg 41), (Sat.Literal.neg 73), (Sat.Literal.pos 3283)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3282), (Sat.Literal.pos 41), (Sat.Literal.pos 73), (Sat.Literal.pos 3283)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3283) = lexBefore s permutation5 40 := by
  exact (positive_lex_of_descriptor s 3283 permutation5 41 (by rfl)).trans ((lex_skipped s permutation5 40 41 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation5 40) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation5 40 by rw [image5_eq]; rfl))

theorem lex_5_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3284) (Sat.Literal.pos 3283) (Sat.Literal.pos 40) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation5 40 (assignment s)
    (Sat.Literal.pos 3284) (Sat.Literal.pos 3283) (Sat.Literal.pos 40) (Sat.Literal.pos 72) (positive_of_descriptor s 3284 (.lex permutation5 40) (by rfl)) (lex_5_40_prefix s) (positive_select s 40) (lex_5_40_image s)

theorem lex_5_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.pos 40), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation5 40 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3283) (Sat.Literal.pos 40) (Sat.Literal.pos 72) (lex_5_40_prefix s) (positive_select s 40) (lex_5_40_image s)

theorem lex_5_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.pos 3283)] :=
  (lex_5_40_gate s).prop _ (List.Mem.head _)

theorem lex_5_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.neg 40), (Sat.Literal.pos 72)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.pos 40), (Sat.Literal.neg 72)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.neg 40), (Sat.Literal.neg 72), (Sat.Literal.pos 3284)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3283), (Sat.Literal.pos 40), (Sat.Literal.pos 72), (Sat.Literal.pos 3284)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3284) = lexBefore s permutation5 39 := by
  exact (positive_lex_of_descriptor s 3284 permutation5 40 (by rfl)).trans ((lex_skipped s permutation5 39 40 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation5 39) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation5 39 by rw [image5_eq]; rfl))

theorem lex_5_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3285) (Sat.Literal.pos 3284) (Sat.Literal.pos 39) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation5 39 (assignment s)
    (Sat.Literal.pos 3285) (Sat.Literal.pos 3284) (Sat.Literal.pos 39) (Sat.Literal.pos 71) (positive_of_descriptor s 3285 (.lex permutation5 39) (by rfl)) (lex_5_39_prefix s) (positive_select s 39) (lex_5_39_image s)

theorem lex_5_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.pos 39), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation5 39 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3284) (Sat.Literal.pos 39) (Sat.Literal.pos 71) (lex_5_39_prefix s) (positive_select s 39) (lex_5_39_image s)

theorem lex_5_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.pos 3284)] :=
  (lex_5_39_gate s).prop _ (List.Mem.head _)

theorem lex_5_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.neg 39), (Sat.Literal.pos 71)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.pos 39), (Sat.Literal.neg 71)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.neg 39), (Sat.Literal.neg 71), (Sat.Literal.pos 3285)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3284), (Sat.Literal.pos 39), (Sat.Literal.pos 71), (Sat.Literal.pos 3285)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3285) = lexBefore s permutation5 38 := by
  exact (positive_lex_of_descriptor s 3285 permutation5 39 (by rfl)).trans ((lex_skipped s permutation5 38 39 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation5 38) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation5 38 by rw [image5_eq]; rfl))

theorem lex_5_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3286) (Sat.Literal.pos 3285) (Sat.Literal.pos 38) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation5 38 (assignment s)
    (Sat.Literal.pos 3286) (Sat.Literal.pos 3285) (Sat.Literal.pos 38) (Sat.Literal.pos 70) (positive_of_descriptor s 3286 (.lex permutation5 38) (by rfl)) (lex_5_38_prefix s) (positive_select s 38) (lex_5_38_image s)

theorem lex_5_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.pos 38), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation5 38 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3285) (Sat.Literal.pos 38) (Sat.Literal.pos 70) (lex_5_38_prefix s) (positive_select s 38) (lex_5_38_image s)

theorem lex_5_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.pos 3285)] :=
  (lex_5_38_gate s).prop _ (List.Mem.head _)

theorem lex_5_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.neg 38), (Sat.Literal.pos 70)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.pos 38), (Sat.Literal.neg 70)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.neg 38), (Sat.Literal.neg 70), (Sat.Literal.pos 3286)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3285), (Sat.Literal.pos 38), (Sat.Literal.pos 70), (Sat.Literal.pos 3286)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3286) = lexBefore s permutation5 37 := by
  exact (positive_lex_of_descriptor s 3286 permutation5 38 (by rfl)).trans ((lex_skipped s permutation5 37 38 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation5 37) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation5 37 by rw [image5_eq]; rfl))

theorem lex_5_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3287) (Sat.Literal.pos 3286) (Sat.Literal.pos 37) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation5 37 (assignment s)
    (Sat.Literal.pos 3287) (Sat.Literal.pos 3286) (Sat.Literal.pos 37) (Sat.Literal.pos 69) (positive_of_descriptor s 3287 (.lex permutation5 37) (by rfl)) (lex_5_37_prefix s) (positive_select s 37) (lex_5_37_image s)

theorem lex_5_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.pos 37), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation5 37 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3286) (Sat.Literal.pos 37) (Sat.Literal.pos 69) (lex_5_37_prefix s) (positive_select s 37) (lex_5_37_image s)

theorem lex_5_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.pos 3286)] :=
  (lex_5_37_gate s).prop _ (List.Mem.head _)

theorem lex_5_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.neg 37), (Sat.Literal.pos 69)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.pos 37), (Sat.Literal.neg 69)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.neg 37), (Sat.Literal.neg 69), (Sat.Literal.pos 3287)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3286), (Sat.Literal.pos 37), (Sat.Literal.pos 69), (Sat.Literal.pos 3287)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3287) = lexBefore s permutation5 36 := by
  exact (positive_lex_of_descriptor s 3287 permutation5 37 (by rfl)).trans ((lex_skipped s permutation5 36 37 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation5 36) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation5 36 by rw [image5_eq]; rfl))

theorem lex_5_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3288) (Sat.Literal.pos 3287) (Sat.Literal.pos 36) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation5 36 (assignment s)
    (Sat.Literal.pos 3288) (Sat.Literal.pos 3287) (Sat.Literal.pos 36) (Sat.Literal.pos 68) (positive_of_descriptor s 3288 (.lex permutation5 36) (by rfl)) (lex_5_36_prefix s) (positive_select s 36) (lex_5_36_image s)

theorem lex_5_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.pos 36), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation5 36 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3287) (Sat.Literal.pos 36) (Sat.Literal.pos 68) (lex_5_36_prefix s) (positive_select s 36) (lex_5_36_image s)

theorem lex_5_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.pos 3287)] :=
  (lex_5_36_gate s).prop _ (List.Mem.head _)

theorem lex_5_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.neg 36), (Sat.Literal.pos 68)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.pos 36), (Sat.Literal.neg 68)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.neg 36), (Sat.Literal.neg 68), (Sat.Literal.pos 3288)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3287), (Sat.Literal.pos 36), (Sat.Literal.pos 68), (Sat.Literal.pos 3288)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3288) = lexBefore s permutation5 35 := by
  exact (positive_lex_of_descriptor s 3288 permutation5 36 (by rfl)).trans ((lex_skipped s permutation5 35 36 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation5 35) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation5 35 by rw [image5_eq]; rfl))

theorem lex_5_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3289) (Sat.Literal.pos 3288) (Sat.Literal.pos 35) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation5 35 (assignment s)
    (Sat.Literal.pos 3289) (Sat.Literal.pos 3288) (Sat.Literal.pos 35) (Sat.Literal.pos 67) (positive_of_descriptor s 3289 (.lex permutation5 35) (by rfl)) (lex_5_35_prefix s) (positive_select s 35) (lex_5_35_image s)

theorem lex_5_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.pos 35), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation5 35 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3288) (Sat.Literal.pos 35) (Sat.Literal.pos 67) (lex_5_35_prefix s) (positive_select s 35) (lex_5_35_image s)

theorem lex_5_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.pos 3288)] :=
  (lex_5_35_gate s).prop _ (List.Mem.head _)

theorem lex_5_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.neg 35), (Sat.Literal.pos 67)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.pos 35), (Sat.Literal.neg 67)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.neg 35), (Sat.Literal.neg 67), (Sat.Literal.pos 3289)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3288), (Sat.Literal.pos 35), (Sat.Literal.pos 67), (Sat.Literal.pos 3289)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3289) = lexBefore s permutation5 34 := by
  exact (positive_lex_of_descriptor s 3289 permutation5 35 (by rfl)).trans ((lex_skipped s permutation5 34 35 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation5 34) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation5 34 by rw [image5_eq]; rfl))

theorem lex_5_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3290) (Sat.Literal.pos 3289) (Sat.Literal.pos 34) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation5 34 (assignment s)
    (Sat.Literal.pos 3290) (Sat.Literal.pos 3289) (Sat.Literal.pos 34) (Sat.Literal.pos 66) (positive_of_descriptor s 3290 (.lex permutation5 34) (by rfl)) (lex_5_34_prefix s) (positive_select s 34) (lex_5_34_image s)

theorem lex_5_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.pos 34), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation5 34 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3289) (Sat.Literal.pos 34) (Sat.Literal.pos 66) (lex_5_34_prefix s) (positive_select s 34) (lex_5_34_image s)

theorem lex_5_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.pos 3289)] :=
  (lex_5_34_gate s).prop _ (List.Mem.head _)

theorem lex_5_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.neg 34), (Sat.Literal.pos 66)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.pos 34), (Sat.Literal.neg 66)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.neg 34), (Sat.Literal.neg 66), (Sat.Literal.pos 3290)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3289), (Sat.Literal.pos 34), (Sat.Literal.pos 66), (Sat.Literal.pos 3290)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3290) = lexBefore s permutation5 33 := by
  exact (positive_lex_of_descriptor s 3290 permutation5 34 (by rfl)).trans ((lex_skipped s permutation5 33 34 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation5 33) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation5 33 by rw [image5_eq]; rfl))

theorem lex_5_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3291) (Sat.Literal.pos 3290) (Sat.Literal.pos 33) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation5 33 (assignment s)
    (Sat.Literal.pos 3291) (Sat.Literal.pos 3290) (Sat.Literal.pos 33) (Sat.Literal.pos 65) (positive_of_descriptor s 3291 (.lex permutation5 33) (by rfl)) (lex_5_33_prefix s) (positive_select s 33) (lex_5_33_image s)

theorem lex_5_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.pos 33), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation5 33 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3290) (Sat.Literal.pos 33) (Sat.Literal.pos 65) (lex_5_33_prefix s) (positive_select s 33) (lex_5_33_image s)

theorem lex_5_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.pos 3290)] :=
  (lex_5_33_gate s).prop _ (List.Mem.head _)

theorem lex_5_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.neg 33), (Sat.Literal.pos 65)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.pos 33), (Sat.Literal.neg 65)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.neg 33), (Sat.Literal.neg 65), (Sat.Literal.pos 3291)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3290), (Sat.Literal.pos 33), (Sat.Literal.pos 65), (Sat.Literal.pos 3291)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3291) = lexBefore s permutation5 32 := by
  exact (positive_lex_of_descriptor s 3291 permutation5 33 (by rfl)).trans ((lex_skipped s permutation5 32 33 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation5 32) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation5 32 by rw [image5_eq]; rfl))

theorem lex_5_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3292) (Sat.Literal.pos 3291) (Sat.Literal.pos 32) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation5 32 (assignment s)
    (Sat.Literal.pos 3292) (Sat.Literal.pos 3291) (Sat.Literal.pos 32) (Sat.Literal.pos 64) (positive_of_descriptor s 3292 (.lex permutation5 32) (by rfl)) (lex_5_32_prefix s) (positive_select s 32) (lex_5_32_image s)

theorem lex_5_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.pos 32), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation5 32 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3291) (Sat.Literal.pos 32) (Sat.Literal.pos 64) (lex_5_32_prefix s) (positive_select s 32) (lex_5_32_image s)

theorem lex_5_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3292), (Sat.Literal.pos 3291)] :=
  (lex_5_32_gate s).prop _ (List.Mem.head _)

theorem lex_5_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3292), (Sat.Literal.neg 32), (Sat.Literal.pos 64)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3292), (Sat.Literal.pos 32), (Sat.Literal.neg 64)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.neg 32), (Sat.Literal.neg 64), (Sat.Literal.pos 3292)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3291), (Sat.Literal.pos 32), (Sat.Literal.pos 64), (Sat.Literal.pos 3292)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation6 191 := by
  exact (negative_falsum s).trans ((lex_first s permutation6 191 (by intro j hj; rw [image6_eq]; exact fixedOnRange_spec image6 192 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_6_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation6 191) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation6 191 by rw [image6_eq]; rfl))

theorem lex_6_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3293) (Sat.Literal.neg 256) (Sat.Literal.pos 191) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation6 191 (assignment s)
    (Sat.Literal.pos 3293) (Sat.Literal.neg 256) (Sat.Literal.pos 191) (Sat.Literal.pos 127) (positive_of_descriptor s 3293 (.lex permutation6 191) (by rfl)) (lex_6_191_prefix s) (positive_select s 191) (lex_6_191_image s)

theorem lex_6_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 191), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation6 191 (hmax permutation6) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 191) (Sat.Literal.pos 127) (lex_6_191_prefix s) (positive_select s 191) (lex_6_191_image s)

theorem lex_6_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.neg 256)] :=
  (lex_6_191_gate s).prop _ (List.Mem.head _)

theorem lex_6_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.neg 191), (Sat.Literal.pos 127)] :=
  (lex_6_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.pos 191), (Sat.Literal.neg 127)] :=
  (lex_6_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 191), (Sat.Literal.neg 127), (Sat.Literal.pos 3293)] :=
  (lex_6_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 191), (Sat.Literal.pos 127), (Sat.Literal.pos 3293)] :=
  (lex_6_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3293) = lexBefore s permutation6 190 := by
  exact (positive_lex_of_descriptor s 3293 permutation6 191 (by rfl)).trans ((lex_skipped s permutation6 190 191 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation6 190) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation6 190 by rw [image6_eq]; rfl))

theorem lex_6_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3294) (Sat.Literal.pos 3293) (Sat.Literal.pos 190) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation6 190 (assignment s)
    (Sat.Literal.pos 3294) (Sat.Literal.pos 3293) (Sat.Literal.pos 190) (Sat.Literal.pos 126) (positive_of_descriptor s 3294 (.lex permutation6 190) (by rfl)) (lex_6_190_prefix s) (positive_select s 190) (lex_6_190_image s)

theorem lex_6_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.pos 190), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation6 190 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3293) (Sat.Literal.pos 190) (Sat.Literal.pos 126) (lex_6_190_prefix s) (positive_select s 190) (lex_6_190_image s)

theorem lex_6_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.pos 3293)] :=
  (lex_6_190_gate s).prop _ (List.Mem.head _)

theorem lex_6_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.neg 190), (Sat.Literal.pos 126)] :=
  (lex_6_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.pos 190), (Sat.Literal.neg 126)] :=
  (lex_6_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.neg 190), (Sat.Literal.neg 126), (Sat.Literal.pos 3294)] :=
  (lex_6_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3293), (Sat.Literal.pos 190), (Sat.Literal.pos 126), (Sat.Literal.pos 3294)] :=
  (lex_6_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3294) = lexBefore s permutation6 189 := by
  exact (positive_lex_of_descriptor s 3294 permutation6 190 (by rfl)).trans ((lex_skipped s permutation6 189 190 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation6 189) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation6 189 by rw [image6_eq]; rfl))

theorem lex_6_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3295) (Sat.Literal.pos 3294) (Sat.Literal.pos 189) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation6 189 (assignment s)
    (Sat.Literal.pos 3295) (Sat.Literal.pos 3294) (Sat.Literal.pos 189) (Sat.Literal.pos 125) (positive_of_descriptor s 3295 (.lex permutation6 189) (by rfl)) (lex_6_189_prefix s) (positive_select s 189) (lex_6_189_image s)

theorem lex_6_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.pos 189), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation6 189 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3294) (Sat.Literal.pos 189) (Sat.Literal.pos 125) (lex_6_189_prefix s) (positive_select s 189) (lex_6_189_image s)

theorem lex_6_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.pos 3294)] :=
  (lex_6_189_gate s).prop _ (List.Mem.head _)

theorem lex_6_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.neg 189), (Sat.Literal.pos 125)] :=
  (lex_6_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.pos 189), (Sat.Literal.neg 125)] :=
  (lex_6_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.neg 189), (Sat.Literal.neg 125), (Sat.Literal.pos 3295)] :=
  (lex_6_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3294), (Sat.Literal.pos 189), (Sat.Literal.pos 125), (Sat.Literal.pos 3295)] :=
  (lex_6_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3295) = lexBefore s permutation6 188 := by
  exact (positive_lex_of_descriptor s 3295 permutation6 189 (by rfl)).trans ((lex_skipped s permutation6 188 189 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation6 188) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation6 188 by rw [image6_eq]; rfl))

theorem lex_6_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3296) (Sat.Literal.pos 3295) (Sat.Literal.pos 188) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation6 188 (assignment s)
    (Sat.Literal.pos 3296) (Sat.Literal.pos 3295) (Sat.Literal.pos 188) (Sat.Literal.pos 124) (positive_of_descriptor s 3296 (.lex permutation6 188) (by rfl)) (lex_6_188_prefix s) (positive_select s 188) (lex_6_188_image s)

theorem lex_6_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.pos 188), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation6 188 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3295) (Sat.Literal.pos 188) (Sat.Literal.pos 124) (lex_6_188_prefix s) (positive_select s 188) (lex_6_188_image s)

theorem lex_6_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.pos 3295)] :=
  (lex_6_188_gate s).prop _ (List.Mem.head _)

theorem lex_6_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.neg 188), (Sat.Literal.pos 124)] :=
  (lex_6_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.pos 188), (Sat.Literal.neg 124)] :=
  (lex_6_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.neg 188), (Sat.Literal.neg 124), (Sat.Literal.pos 3296)] :=
  (lex_6_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3295), (Sat.Literal.pos 188), (Sat.Literal.pos 124), (Sat.Literal.pos 3296)] :=
  (lex_6_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3296) = lexBefore s permutation6 187 := by
  exact (positive_lex_of_descriptor s 3296 permutation6 188 (by rfl)).trans ((lex_skipped s permutation6 187 188 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation6 187) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation6 187 by rw [image6_eq]; rfl))

theorem lex_6_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3297) (Sat.Literal.pos 3296) (Sat.Literal.pos 187) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation6 187 (assignment s)
    (Sat.Literal.pos 3297) (Sat.Literal.pos 3296) (Sat.Literal.pos 187) (Sat.Literal.pos 123) (positive_of_descriptor s 3297 (.lex permutation6 187) (by rfl)) (lex_6_187_prefix s) (positive_select s 187) (lex_6_187_image s)

theorem lex_6_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.pos 187), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation6 187 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3296) (Sat.Literal.pos 187) (Sat.Literal.pos 123) (lex_6_187_prefix s) (positive_select s 187) (lex_6_187_image s)

theorem lex_6_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.pos 3296)] :=
  (lex_6_187_gate s).prop _ (List.Mem.head _)

theorem lex_6_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.neg 187), (Sat.Literal.pos 123)] :=
  (lex_6_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.pos 187), (Sat.Literal.neg 123)] :=
  (lex_6_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.neg 187), (Sat.Literal.neg 123), (Sat.Literal.pos 3297)] :=
  (lex_6_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3296), (Sat.Literal.pos 187), (Sat.Literal.pos 123), (Sat.Literal.pos 3297)] :=
  (lex_6_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3297) = lexBefore s permutation6 186 := by
  exact (positive_lex_of_descriptor s 3297 permutation6 187 (by rfl)).trans ((lex_skipped s permutation6 186 187 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation6 186) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation6 186 by rw [image6_eq]; rfl))

theorem lex_6_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3298) (Sat.Literal.pos 3297) (Sat.Literal.pos 186) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation6 186 (assignment s)
    (Sat.Literal.pos 3298) (Sat.Literal.pos 3297) (Sat.Literal.pos 186) (Sat.Literal.pos 122) (positive_of_descriptor s 3298 (.lex permutation6 186) (by rfl)) (lex_6_186_prefix s) (positive_select s 186) (lex_6_186_image s)

theorem lex_6_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.pos 186), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation6 186 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3297) (Sat.Literal.pos 186) (Sat.Literal.pos 122) (lex_6_186_prefix s) (positive_select s 186) (lex_6_186_image s)

theorem lex_6_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.pos 3297)] :=
  (lex_6_186_gate s).prop _ (List.Mem.head _)

theorem lex_6_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.neg 186), (Sat.Literal.pos 122)] :=
  (lex_6_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.pos 186), (Sat.Literal.neg 122)] :=
  (lex_6_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.neg 186), (Sat.Literal.neg 122), (Sat.Literal.pos 3298)] :=
  (lex_6_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3297), (Sat.Literal.pos 186), (Sat.Literal.pos 122), (Sat.Literal.pos 3298)] :=
  (lex_6_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3298) = lexBefore s permutation6 185 := by
  exact (positive_lex_of_descriptor s 3298 permutation6 186 (by rfl)).trans ((lex_skipped s permutation6 185 186 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation6 185) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation6 185 by rw [image6_eq]; rfl))

theorem lex_6_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3299) (Sat.Literal.pos 3298) (Sat.Literal.pos 185) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation6 185 (assignment s)
    (Sat.Literal.pos 3299) (Sat.Literal.pos 3298) (Sat.Literal.pos 185) (Sat.Literal.pos 121) (positive_of_descriptor s 3299 (.lex permutation6 185) (by rfl)) (lex_6_185_prefix s) (positive_select s 185) (lex_6_185_image s)

theorem lex_6_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.pos 185), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation6 185 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3298) (Sat.Literal.pos 185) (Sat.Literal.pos 121) (lex_6_185_prefix s) (positive_select s 185) (lex_6_185_image s)

theorem lex_6_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.pos 3298)] :=
  (lex_6_185_gate s).prop _ (List.Mem.head _)

theorem lex_6_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.neg 185), (Sat.Literal.pos 121)] :=
  (lex_6_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.pos 185), (Sat.Literal.neg 121)] :=
  (lex_6_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.neg 185), (Sat.Literal.neg 121), (Sat.Literal.pos 3299)] :=
  (lex_6_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3298), (Sat.Literal.pos 185), (Sat.Literal.pos 121), (Sat.Literal.pos 3299)] :=
  (lex_6_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3299) = lexBefore s permutation6 184 := by
  exact (positive_lex_of_descriptor s 3299 permutation6 185 (by rfl)).trans ((lex_skipped s permutation6 184 185 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation6 184) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation6 184 by rw [image6_eq]; rfl))

theorem lex_6_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3300) (Sat.Literal.pos 3299) (Sat.Literal.pos 184) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation6 184 (assignment s)
    (Sat.Literal.pos 3300) (Sat.Literal.pos 3299) (Sat.Literal.pos 184) (Sat.Literal.pos 120) (positive_of_descriptor s 3300 (.lex permutation6 184) (by rfl)) (lex_6_184_prefix s) (positive_select s 184) (lex_6_184_image s)

theorem lex_6_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.pos 184), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation6 184 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3299) (Sat.Literal.pos 184) (Sat.Literal.pos 120) (lex_6_184_prefix s) (positive_select s 184) (lex_6_184_image s)

theorem lex_6_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.pos 3299)] :=
  (lex_6_184_gate s).prop _ (List.Mem.head _)

theorem lex_6_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.neg 184), (Sat.Literal.pos 120)] :=
  (lex_6_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.pos 184), (Sat.Literal.neg 120)] :=
  (lex_6_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.neg 184), (Sat.Literal.neg 120), (Sat.Literal.pos 3300)] :=
  (lex_6_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3299), (Sat.Literal.pos 184), (Sat.Literal.pos 120), (Sat.Literal.pos 3300)] :=
  (lex_6_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3300) = lexBefore s permutation6 183 := by
  exact (positive_lex_of_descriptor s 3300 permutation6 184 (by rfl)).trans ((lex_skipped s permutation6 183 184 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation6 183) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation6 183 by rw [image6_eq]; rfl))

theorem lex_6_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3301) (Sat.Literal.pos 3300) (Sat.Literal.pos 183) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation6 183 (assignment s)
    (Sat.Literal.pos 3301) (Sat.Literal.pos 3300) (Sat.Literal.pos 183) (Sat.Literal.pos 119) (positive_of_descriptor s 3301 (.lex permutation6 183) (by rfl)) (lex_6_183_prefix s) (positive_select s 183) (lex_6_183_image s)

theorem lex_6_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.pos 183), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation6 183 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3300) (Sat.Literal.pos 183) (Sat.Literal.pos 119) (lex_6_183_prefix s) (positive_select s 183) (lex_6_183_image s)

theorem lex_6_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.pos 3300)] :=
  (lex_6_183_gate s).prop _ (List.Mem.head _)

theorem lex_6_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.neg 183), (Sat.Literal.pos 119)] :=
  (lex_6_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.pos 183), (Sat.Literal.neg 119)] :=
  (lex_6_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.neg 183), (Sat.Literal.neg 119), (Sat.Literal.pos 3301)] :=
  (lex_6_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3300), (Sat.Literal.pos 183), (Sat.Literal.pos 119), (Sat.Literal.pos 3301)] :=
  (lex_6_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3301) = lexBefore s permutation6 182 := by
  exact (positive_lex_of_descriptor s 3301 permutation6 183 (by rfl)).trans ((lex_skipped s permutation6 182 183 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation6 182) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation6 182 by rw [image6_eq]; rfl))

theorem lex_6_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3302) (Sat.Literal.pos 3301) (Sat.Literal.pos 182) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation6 182 (assignment s)
    (Sat.Literal.pos 3302) (Sat.Literal.pos 3301) (Sat.Literal.pos 182) (Sat.Literal.pos 118) (positive_of_descriptor s 3302 (.lex permutation6 182) (by rfl)) (lex_6_182_prefix s) (positive_select s 182) (lex_6_182_image s)

theorem lex_6_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.pos 182), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation6 182 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3301) (Sat.Literal.pos 182) (Sat.Literal.pos 118) (lex_6_182_prefix s) (positive_select s 182) (lex_6_182_image s)

theorem lex_6_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.pos 3301)] :=
  (lex_6_182_gate s).prop _ (List.Mem.head _)

theorem lex_6_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.neg 182), (Sat.Literal.pos 118)] :=
  (lex_6_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.pos 182), (Sat.Literal.neg 118)] :=
  (lex_6_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.neg 182), (Sat.Literal.neg 118), (Sat.Literal.pos 3302)] :=
  (lex_6_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3301), (Sat.Literal.pos 182), (Sat.Literal.pos 118), (Sat.Literal.pos 3302)] :=
  (lex_6_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3302) = lexBefore s permutation6 181 := by
  exact (positive_lex_of_descriptor s 3302 permutation6 182 (by rfl)).trans ((lex_skipped s permutation6 181 182 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation6 181) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation6 181 by rw [image6_eq]; rfl))

theorem lex_6_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3303) (Sat.Literal.pos 3302) (Sat.Literal.pos 181) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation6 181 (assignment s)
    (Sat.Literal.pos 3303) (Sat.Literal.pos 3302) (Sat.Literal.pos 181) (Sat.Literal.pos 117) (positive_of_descriptor s 3303 (.lex permutation6 181) (by rfl)) (lex_6_181_prefix s) (positive_select s 181) (lex_6_181_image s)

theorem lex_6_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.pos 181), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation6 181 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3302) (Sat.Literal.pos 181) (Sat.Literal.pos 117) (lex_6_181_prefix s) (positive_select s 181) (lex_6_181_image s)

theorem lex_6_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.pos 3302)] :=
  (lex_6_181_gate s).prop _ (List.Mem.head _)

theorem lex_6_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.neg 181), (Sat.Literal.pos 117)] :=
  (lex_6_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.pos 181), (Sat.Literal.neg 117)] :=
  (lex_6_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.neg 181), (Sat.Literal.neg 117), (Sat.Literal.pos 3303)] :=
  (lex_6_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3302), (Sat.Literal.pos 181), (Sat.Literal.pos 117), (Sat.Literal.pos 3303)] :=
  (lex_6_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3303) = lexBefore s permutation6 180 := by
  exact (positive_lex_of_descriptor s 3303 permutation6 181 (by rfl)).trans ((lex_skipped s permutation6 180 181 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation6 180) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation6 180 by rw [image6_eq]; rfl))

theorem lex_6_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3304) (Sat.Literal.pos 3303) (Sat.Literal.pos 180) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation6 180 (assignment s)
    (Sat.Literal.pos 3304) (Sat.Literal.pos 3303) (Sat.Literal.pos 180) (Sat.Literal.pos 116) (positive_of_descriptor s 3304 (.lex permutation6 180) (by rfl)) (lex_6_180_prefix s) (positive_select s 180) (lex_6_180_image s)

theorem lex_6_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.pos 180), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation6 180 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3303) (Sat.Literal.pos 180) (Sat.Literal.pos 116) (lex_6_180_prefix s) (positive_select s 180) (lex_6_180_image s)

theorem lex_6_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.pos 3303)] :=
  (lex_6_180_gate s).prop _ (List.Mem.head _)

theorem lex_6_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.neg 180), (Sat.Literal.pos 116)] :=
  (lex_6_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.pos 180), (Sat.Literal.neg 116)] :=
  (lex_6_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.neg 180), (Sat.Literal.neg 116), (Sat.Literal.pos 3304)] :=
  (lex_6_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3303), (Sat.Literal.pos 180), (Sat.Literal.pos 116), (Sat.Literal.pos 3304)] :=
  (lex_6_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3304) = lexBefore s permutation6 179 := by
  exact (positive_lex_of_descriptor s 3304 permutation6 180 (by rfl)).trans ((lex_skipped s permutation6 179 180 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation6 179) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation6 179 by rw [image6_eq]; rfl))

theorem lex_6_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3305) (Sat.Literal.pos 3304) (Sat.Literal.pos 179) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation6 179 (assignment s)
    (Sat.Literal.pos 3305) (Sat.Literal.pos 3304) (Sat.Literal.pos 179) (Sat.Literal.pos 115) (positive_of_descriptor s 3305 (.lex permutation6 179) (by rfl)) (lex_6_179_prefix s) (positive_select s 179) (lex_6_179_image s)

theorem lex_6_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.pos 179), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation6 179 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3304) (Sat.Literal.pos 179) (Sat.Literal.pos 115) (lex_6_179_prefix s) (positive_select s 179) (lex_6_179_image s)

theorem lex_6_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.pos 3304)] :=
  (lex_6_179_gate s).prop _ (List.Mem.head _)

theorem lex_6_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.neg 179), (Sat.Literal.pos 115)] :=
  (lex_6_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.pos 179), (Sat.Literal.neg 115)] :=
  (lex_6_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.neg 179), (Sat.Literal.neg 115), (Sat.Literal.pos 3305)] :=
  (lex_6_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3304), (Sat.Literal.pos 179), (Sat.Literal.pos 115), (Sat.Literal.pos 3305)] :=
  (lex_6_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3305) = lexBefore s permutation6 178 := by
  exact (positive_lex_of_descriptor s 3305 permutation6 179 (by rfl)).trans ((lex_skipped s permutation6 178 179 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation6 178) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation6 178 by rw [image6_eq]; rfl))

theorem lex_6_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3306) (Sat.Literal.pos 3305) (Sat.Literal.pos 178) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation6 178 (assignment s)
    (Sat.Literal.pos 3306) (Sat.Literal.pos 3305) (Sat.Literal.pos 178) (Sat.Literal.pos 114) (positive_of_descriptor s 3306 (.lex permutation6 178) (by rfl)) (lex_6_178_prefix s) (positive_select s 178) (lex_6_178_image s)

theorem lex_6_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.pos 178), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation6 178 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3305) (Sat.Literal.pos 178) (Sat.Literal.pos 114) (lex_6_178_prefix s) (positive_select s 178) (lex_6_178_image s)

theorem lex_6_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.pos 3305)] :=
  (lex_6_178_gate s).prop _ (List.Mem.head _)

theorem lex_6_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.neg 178), (Sat.Literal.pos 114)] :=
  (lex_6_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.pos 178), (Sat.Literal.neg 114)] :=
  (lex_6_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.neg 178), (Sat.Literal.neg 114), (Sat.Literal.pos 3306)] :=
  (lex_6_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3305), (Sat.Literal.pos 178), (Sat.Literal.pos 114), (Sat.Literal.pos 3306)] :=
  (lex_6_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3306) = lexBefore s permutation6 177 := by
  exact (positive_lex_of_descriptor s 3306 permutation6 178 (by rfl)).trans ((lex_skipped s permutation6 177 178 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation6 177) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation6 177 by rw [image6_eq]; rfl))

theorem lex_6_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3307) (Sat.Literal.pos 3306) (Sat.Literal.pos 177) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation6 177 (assignment s)
    (Sat.Literal.pos 3307) (Sat.Literal.pos 3306) (Sat.Literal.pos 177) (Sat.Literal.pos 113) (positive_of_descriptor s 3307 (.lex permutation6 177) (by rfl)) (lex_6_177_prefix s) (positive_select s 177) (lex_6_177_image s)

theorem lex_6_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.pos 177), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation6 177 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3306) (Sat.Literal.pos 177) (Sat.Literal.pos 113) (lex_6_177_prefix s) (positive_select s 177) (lex_6_177_image s)

theorem lex_6_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.pos 3306)] :=
  (lex_6_177_gate s).prop _ (List.Mem.head _)

theorem lex_6_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.neg 177), (Sat.Literal.pos 113)] :=
  (lex_6_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.pos 177), (Sat.Literal.neg 113)] :=
  (lex_6_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.neg 177), (Sat.Literal.neg 113), (Sat.Literal.pos 3307)] :=
  (lex_6_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3306), (Sat.Literal.pos 177), (Sat.Literal.pos 113), (Sat.Literal.pos 3307)] :=
  (lex_6_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3307) = lexBefore s permutation6 176 := by
  exact (positive_lex_of_descriptor s 3307 permutation6 177 (by rfl)).trans ((lex_skipped s permutation6 176 177 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation6 176) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation6 176 by rw [image6_eq]; rfl))

theorem lex_6_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3308) (Sat.Literal.pos 3307) (Sat.Literal.pos 176) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation6 176 (assignment s)
    (Sat.Literal.pos 3308) (Sat.Literal.pos 3307) (Sat.Literal.pos 176) (Sat.Literal.pos 112) (positive_of_descriptor s 3308 (.lex permutation6 176) (by rfl)) (lex_6_176_prefix s) (positive_select s 176) (lex_6_176_image s)

theorem lex_6_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.pos 176), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation6 176 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3307) (Sat.Literal.pos 176) (Sat.Literal.pos 112) (lex_6_176_prefix s) (positive_select s 176) (lex_6_176_image s)

theorem lex_6_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.pos 3307)] :=
  (lex_6_176_gate s).prop _ (List.Mem.head _)

theorem lex_6_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.neg 176), (Sat.Literal.pos 112)] :=
  (lex_6_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.pos 176), (Sat.Literal.neg 112)] :=
  (lex_6_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.neg 176), (Sat.Literal.neg 112), (Sat.Literal.pos 3308)] :=
  (lex_6_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3307), (Sat.Literal.pos 176), (Sat.Literal.pos 112), (Sat.Literal.pos 3308)] :=
  (lex_6_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3308) = lexBefore s permutation6 175 := by
  exact (positive_lex_of_descriptor s 3308 permutation6 176 (by rfl)).trans ((lex_skipped s permutation6 175 176 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation6 175) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation6 175 by rw [image6_eq]; rfl))

theorem lex_6_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3309) (Sat.Literal.pos 3308) (Sat.Literal.pos 175) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation6 175 (assignment s)
    (Sat.Literal.pos 3309) (Sat.Literal.pos 3308) (Sat.Literal.pos 175) (Sat.Literal.pos 111) (positive_of_descriptor s 3309 (.lex permutation6 175) (by rfl)) (lex_6_175_prefix s) (positive_select s 175) (lex_6_175_image s)

theorem lex_6_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.pos 175), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation6 175 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3308) (Sat.Literal.pos 175) (Sat.Literal.pos 111) (lex_6_175_prefix s) (positive_select s 175) (lex_6_175_image s)

theorem lex_6_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.pos 3308)] :=
  (lex_6_175_gate s).prop _ (List.Mem.head _)

theorem lex_6_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.neg 175), (Sat.Literal.pos 111)] :=
  (lex_6_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.pos 175), (Sat.Literal.neg 111)] :=
  (lex_6_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.neg 175), (Sat.Literal.neg 111), (Sat.Literal.pos 3309)] :=
  (lex_6_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3308), (Sat.Literal.pos 175), (Sat.Literal.pos 111), (Sat.Literal.pos 3309)] :=
  (lex_6_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3309) = lexBefore s permutation6 174 := by
  exact (positive_lex_of_descriptor s 3309 permutation6 175 (by rfl)).trans ((lex_skipped s permutation6 174 175 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation6 174) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation6 174 by rw [image6_eq]; rfl))

theorem lex_6_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3310) (Sat.Literal.pos 3309) (Sat.Literal.pos 174) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation6 174 (assignment s)
    (Sat.Literal.pos 3310) (Sat.Literal.pos 3309) (Sat.Literal.pos 174) (Sat.Literal.pos 110) (positive_of_descriptor s 3310 (.lex permutation6 174) (by rfl)) (lex_6_174_prefix s) (positive_select s 174) (lex_6_174_image s)

theorem lex_6_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.pos 174), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation6 174 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3309) (Sat.Literal.pos 174) (Sat.Literal.pos 110) (lex_6_174_prefix s) (positive_select s 174) (lex_6_174_image s)

theorem lex_6_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.pos 3309)] :=
  (lex_6_174_gate s).prop _ (List.Mem.head _)

theorem lex_6_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.neg 174), (Sat.Literal.pos 110)] :=
  (lex_6_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.pos 174), (Sat.Literal.neg 110)] :=
  (lex_6_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.neg 174), (Sat.Literal.neg 110), (Sat.Literal.pos 3310)] :=
  (lex_6_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3309), (Sat.Literal.pos 174), (Sat.Literal.pos 110), (Sat.Literal.pos 3310)] :=
  (lex_6_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3310) = lexBefore s permutation6 173 := by
  exact (positive_lex_of_descriptor s 3310 permutation6 174 (by rfl)).trans ((lex_skipped s permutation6 173 174 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation6 173) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation6 173 by rw [image6_eq]; rfl))

theorem lex_6_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3311) (Sat.Literal.pos 3310) (Sat.Literal.pos 173) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation6 173 (assignment s)
    (Sat.Literal.pos 3311) (Sat.Literal.pos 3310) (Sat.Literal.pos 173) (Sat.Literal.pos 109) (positive_of_descriptor s 3311 (.lex permutation6 173) (by rfl)) (lex_6_173_prefix s) (positive_select s 173) (lex_6_173_image s)

theorem lex_6_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.pos 173), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation6 173 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3310) (Sat.Literal.pos 173) (Sat.Literal.pos 109) (lex_6_173_prefix s) (positive_select s 173) (lex_6_173_image s)

theorem lex_6_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.pos 3310)] :=
  (lex_6_173_gate s).prop _ (List.Mem.head _)

theorem lex_6_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.neg 173), (Sat.Literal.pos 109)] :=
  (lex_6_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.pos 173), (Sat.Literal.neg 109)] :=
  (lex_6_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.neg 173), (Sat.Literal.neg 109), (Sat.Literal.pos 3311)] :=
  (lex_6_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3310), (Sat.Literal.pos 173), (Sat.Literal.pos 109), (Sat.Literal.pos 3311)] :=
  (lex_6_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3311) = lexBefore s permutation6 172 := by
  exact (positive_lex_of_descriptor s 3311 permutation6 173 (by rfl)).trans ((lex_skipped s permutation6 172 173 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation6 172) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation6 172 by rw [image6_eq]; rfl))

theorem lex_6_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3312) (Sat.Literal.pos 3311) (Sat.Literal.pos 172) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation6 172 (assignment s)
    (Sat.Literal.pos 3312) (Sat.Literal.pos 3311) (Sat.Literal.pos 172) (Sat.Literal.pos 108) (positive_of_descriptor s 3312 (.lex permutation6 172) (by rfl)) (lex_6_172_prefix s) (positive_select s 172) (lex_6_172_image s)

theorem lex_6_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.pos 172), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation6 172 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3311) (Sat.Literal.pos 172) (Sat.Literal.pos 108) (lex_6_172_prefix s) (positive_select s 172) (lex_6_172_image s)

theorem lex_6_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.pos 3311)] :=
  (lex_6_172_gate s).prop _ (List.Mem.head _)

theorem lex_6_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.neg 172), (Sat.Literal.pos 108)] :=
  (lex_6_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.pos 172), (Sat.Literal.neg 108)] :=
  (lex_6_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.neg 172), (Sat.Literal.neg 108), (Sat.Literal.pos 3312)] :=
  (lex_6_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3311), (Sat.Literal.pos 172), (Sat.Literal.pos 108), (Sat.Literal.pos 3312)] :=
  (lex_6_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3312) = lexBefore s permutation6 171 := by
  exact (positive_lex_of_descriptor s 3312 permutation6 172 (by rfl)).trans ((lex_skipped s permutation6 171 172 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation6 171) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation6 171 by rw [image6_eq]; rfl))

theorem lex_6_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3313) (Sat.Literal.pos 3312) (Sat.Literal.pos 171) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation6 171 (assignment s)
    (Sat.Literal.pos 3313) (Sat.Literal.pos 3312) (Sat.Literal.pos 171) (Sat.Literal.pos 107) (positive_of_descriptor s 3313 (.lex permutation6 171) (by rfl)) (lex_6_171_prefix s) (positive_select s 171) (lex_6_171_image s)

theorem lex_6_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.pos 171), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation6 171 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3312) (Sat.Literal.pos 171) (Sat.Literal.pos 107) (lex_6_171_prefix s) (positive_select s 171) (lex_6_171_image s)

theorem lex_6_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.pos 3312)] :=
  (lex_6_171_gate s).prop _ (List.Mem.head _)

theorem lex_6_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.neg 171), (Sat.Literal.pos 107)] :=
  (lex_6_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.pos 171), (Sat.Literal.neg 107)] :=
  (lex_6_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.neg 171), (Sat.Literal.neg 107), (Sat.Literal.pos 3313)] :=
  (lex_6_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3312), (Sat.Literal.pos 171), (Sat.Literal.pos 107), (Sat.Literal.pos 3313)] :=
  (lex_6_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3313) = lexBefore s permutation6 170 := by
  exact (positive_lex_of_descriptor s 3313 permutation6 171 (by rfl)).trans ((lex_skipped s permutation6 170 171 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation6 170) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation6 170 by rw [image6_eq]; rfl))

theorem lex_6_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3314) (Sat.Literal.pos 3313) (Sat.Literal.pos 170) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation6 170 (assignment s)
    (Sat.Literal.pos 3314) (Sat.Literal.pos 3313) (Sat.Literal.pos 170) (Sat.Literal.pos 106) (positive_of_descriptor s 3314 (.lex permutation6 170) (by rfl)) (lex_6_170_prefix s) (positive_select s 170) (lex_6_170_image s)

theorem lex_6_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.pos 170), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation6 170 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3313) (Sat.Literal.pos 170) (Sat.Literal.pos 106) (lex_6_170_prefix s) (positive_select s 170) (lex_6_170_image s)

theorem lex_6_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.pos 3313)] :=
  (lex_6_170_gate s).prop _ (List.Mem.head _)

theorem lex_6_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.neg 170), (Sat.Literal.pos 106)] :=
  (lex_6_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.pos 170), (Sat.Literal.neg 106)] :=
  (lex_6_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.neg 170), (Sat.Literal.neg 106), (Sat.Literal.pos 3314)] :=
  (lex_6_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3313), (Sat.Literal.pos 170), (Sat.Literal.pos 106), (Sat.Literal.pos 3314)] :=
  (lex_6_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3314) = lexBefore s permutation6 169 := by
  exact (positive_lex_of_descriptor s 3314 permutation6 170 (by rfl)).trans ((lex_skipped s permutation6 169 170 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation6 169) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation6 169 by rw [image6_eq]; rfl))

theorem lex_6_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3315) (Sat.Literal.pos 3314) (Sat.Literal.pos 169) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation6 169 (assignment s)
    (Sat.Literal.pos 3315) (Sat.Literal.pos 3314) (Sat.Literal.pos 169) (Sat.Literal.pos 105) (positive_of_descriptor s 3315 (.lex permutation6 169) (by rfl)) (lex_6_169_prefix s) (positive_select s 169) (lex_6_169_image s)

theorem lex_6_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.pos 169), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation6 169 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3314) (Sat.Literal.pos 169) (Sat.Literal.pos 105) (lex_6_169_prefix s) (positive_select s 169) (lex_6_169_image s)

theorem lex_6_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.pos 3314)] :=
  (lex_6_169_gate s).prop _ (List.Mem.head _)

theorem lex_6_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.neg 169), (Sat.Literal.pos 105)] :=
  (lex_6_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.pos 169), (Sat.Literal.neg 105)] :=
  (lex_6_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.neg 169), (Sat.Literal.neg 105), (Sat.Literal.pos 3315)] :=
  (lex_6_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3314), (Sat.Literal.pos 169), (Sat.Literal.pos 105), (Sat.Literal.pos 3315)] :=
  (lex_6_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3315) = lexBefore s permutation6 168 := by
  exact (positive_lex_of_descriptor s 3315 permutation6 169 (by rfl)).trans ((lex_skipped s permutation6 168 169 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation6 168) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation6 168 by rw [image6_eq]; rfl))

theorem lex_6_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3316) (Sat.Literal.pos 3315) (Sat.Literal.pos 168) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation6 168 (assignment s)
    (Sat.Literal.pos 3316) (Sat.Literal.pos 3315) (Sat.Literal.pos 168) (Sat.Literal.pos 104) (positive_of_descriptor s 3316 (.lex permutation6 168) (by rfl)) (lex_6_168_prefix s) (positive_select s 168) (lex_6_168_image s)

theorem lex_6_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.pos 168), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation6 168 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3315) (Sat.Literal.pos 168) (Sat.Literal.pos 104) (lex_6_168_prefix s) (positive_select s 168) (lex_6_168_image s)

theorem lex_6_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.pos 3315)] :=
  (lex_6_168_gate s).prop _ (List.Mem.head _)

theorem lex_6_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.neg 168), (Sat.Literal.pos 104)] :=
  (lex_6_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.pos 168), (Sat.Literal.neg 104)] :=
  (lex_6_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.neg 168), (Sat.Literal.neg 104), (Sat.Literal.pos 3316)] :=
  (lex_6_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3315), (Sat.Literal.pos 168), (Sat.Literal.pos 104), (Sat.Literal.pos 3316)] :=
  (lex_6_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3316) = lexBefore s permutation6 167 := by
  exact (positive_lex_of_descriptor s 3316 permutation6 168 (by rfl)).trans ((lex_skipped s permutation6 167 168 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation6 167) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation6 167 by rw [image6_eq]; rfl))

theorem lex_6_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3317) (Sat.Literal.pos 3316) (Sat.Literal.pos 167) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation6 167 (assignment s)
    (Sat.Literal.pos 3317) (Sat.Literal.pos 3316) (Sat.Literal.pos 167) (Sat.Literal.pos 103) (positive_of_descriptor s 3317 (.lex permutation6 167) (by rfl)) (lex_6_167_prefix s) (positive_select s 167) (lex_6_167_image s)

theorem lex_6_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.pos 167), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation6 167 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3316) (Sat.Literal.pos 167) (Sat.Literal.pos 103) (lex_6_167_prefix s) (positive_select s 167) (lex_6_167_image s)

theorem lex_6_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.pos 3316)] :=
  (lex_6_167_gate s).prop _ (List.Mem.head _)

theorem lex_6_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.neg 167), (Sat.Literal.pos 103)] :=
  (lex_6_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.pos 167), (Sat.Literal.neg 103)] :=
  (lex_6_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.neg 167), (Sat.Literal.neg 103), (Sat.Literal.pos 3317)] :=
  (lex_6_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3316), (Sat.Literal.pos 167), (Sat.Literal.pos 103), (Sat.Literal.pos 3317)] :=
  (lex_6_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3317) = lexBefore s permutation6 166 := by
  exact (positive_lex_of_descriptor s 3317 permutation6 167 (by rfl)).trans ((lex_skipped s permutation6 166 167 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation6 166) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation6 166 by rw [image6_eq]; rfl))

theorem lex_6_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3318) (Sat.Literal.pos 3317) (Sat.Literal.pos 166) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation6 166 (assignment s)
    (Sat.Literal.pos 3318) (Sat.Literal.pos 3317) (Sat.Literal.pos 166) (Sat.Literal.pos 102) (positive_of_descriptor s 3318 (.lex permutation6 166) (by rfl)) (lex_6_166_prefix s) (positive_select s 166) (lex_6_166_image s)

theorem lex_6_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.pos 166), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation6 166 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3317) (Sat.Literal.pos 166) (Sat.Literal.pos 102) (lex_6_166_prefix s) (positive_select s 166) (lex_6_166_image s)

theorem lex_6_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.pos 3317)] :=
  (lex_6_166_gate s).prop _ (List.Mem.head _)

theorem lex_6_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.neg 166), (Sat.Literal.pos 102)] :=
  (lex_6_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.pos 166), (Sat.Literal.neg 102)] :=
  (lex_6_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.neg 166), (Sat.Literal.neg 102), (Sat.Literal.pos 3318)] :=
  (lex_6_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3317), (Sat.Literal.pos 166), (Sat.Literal.pos 102), (Sat.Literal.pos 3318)] :=
  (lex_6_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3318) = lexBefore s permutation6 165 := by
  exact (positive_lex_of_descriptor s 3318 permutation6 166 (by rfl)).trans ((lex_skipped s permutation6 165 166 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation6 165) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation6 165 by rw [image6_eq]; rfl))

theorem lex_6_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3319) (Sat.Literal.pos 3318) (Sat.Literal.pos 165) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation6 165 (assignment s)
    (Sat.Literal.pos 3319) (Sat.Literal.pos 3318) (Sat.Literal.pos 165) (Sat.Literal.pos 101) (positive_of_descriptor s 3319 (.lex permutation6 165) (by rfl)) (lex_6_165_prefix s) (positive_select s 165) (lex_6_165_image s)

theorem lex_6_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.pos 165), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation6 165 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3318) (Sat.Literal.pos 165) (Sat.Literal.pos 101) (lex_6_165_prefix s) (positive_select s 165) (lex_6_165_image s)

theorem lex_6_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.pos 3318)] :=
  (lex_6_165_gate s).prop _ (List.Mem.head _)

theorem lex_6_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.neg 165), (Sat.Literal.pos 101)] :=
  (lex_6_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.pos 165), (Sat.Literal.neg 101)] :=
  (lex_6_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.neg 165), (Sat.Literal.neg 101), (Sat.Literal.pos 3319)] :=
  (lex_6_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3318), (Sat.Literal.pos 165), (Sat.Literal.pos 101), (Sat.Literal.pos 3319)] :=
  (lex_6_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3319) = lexBefore s permutation6 164 := by
  exact (positive_lex_of_descriptor s 3319 permutation6 165 (by rfl)).trans ((lex_skipped s permutation6 164 165 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation6 164) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation6 164 by rw [image6_eq]; rfl))

theorem lex_6_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3320) (Sat.Literal.pos 3319) (Sat.Literal.pos 164) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation6 164 (assignment s)
    (Sat.Literal.pos 3320) (Sat.Literal.pos 3319) (Sat.Literal.pos 164) (Sat.Literal.pos 100) (positive_of_descriptor s 3320 (.lex permutation6 164) (by rfl)) (lex_6_164_prefix s) (positive_select s 164) (lex_6_164_image s)

theorem lex_6_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.pos 164), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation6 164 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3319) (Sat.Literal.pos 164) (Sat.Literal.pos 100) (lex_6_164_prefix s) (positive_select s 164) (lex_6_164_image s)

theorem lex_6_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.pos 3319)] :=
  (lex_6_164_gate s).prop _ (List.Mem.head _)

theorem lex_6_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.neg 164), (Sat.Literal.pos 100)] :=
  (lex_6_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.pos 164), (Sat.Literal.neg 100)] :=
  (lex_6_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.neg 164), (Sat.Literal.neg 100), (Sat.Literal.pos 3320)] :=
  (lex_6_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3319), (Sat.Literal.pos 164), (Sat.Literal.pos 100), (Sat.Literal.pos 3320)] :=
  (lex_6_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3320) = lexBefore s permutation6 163 := by
  exact (positive_lex_of_descriptor s 3320 permutation6 164 (by rfl)).trans ((lex_skipped s permutation6 163 164 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation6 163) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation6 163 by rw [image6_eq]; rfl))

theorem lex_6_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3321) (Sat.Literal.pos 3320) (Sat.Literal.pos 163) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation6 163 (assignment s)
    (Sat.Literal.pos 3321) (Sat.Literal.pos 3320) (Sat.Literal.pos 163) (Sat.Literal.pos 99) (positive_of_descriptor s 3321 (.lex permutation6 163) (by rfl)) (lex_6_163_prefix s) (positive_select s 163) (lex_6_163_image s)

theorem lex_6_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.pos 163), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation6 163 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3320) (Sat.Literal.pos 163) (Sat.Literal.pos 99) (lex_6_163_prefix s) (positive_select s 163) (lex_6_163_image s)

theorem lex_6_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.pos 3320)] :=
  (lex_6_163_gate s).prop _ (List.Mem.head _)

theorem lex_6_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.neg 163), (Sat.Literal.pos 99)] :=
  (lex_6_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.pos 163), (Sat.Literal.neg 99)] :=
  (lex_6_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.neg 163), (Sat.Literal.neg 99), (Sat.Literal.pos 3321)] :=
  (lex_6_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3320), (Sat.Literal.pos 163), (Sat.Literal.pos 99), (Sat.Literal.pos 3321)] :=
  (lex_6_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3321) = lexBefore s permutation6 162 := by
  exact (positive_lex_of_descriptor s 3321 permutation6 163 (by rfl)).trans ((lex_skipped s permutation6 162 163 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation6 162) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation6 162 by rw [image6_eq]; rfl))

theorem lex_6_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3322) (Sat.Literal.pos 3321) (Sat.Literal.pos 162) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation6 162 (assignment s)
    (Sat.Literal.pos 3322) (Sat.Literal.pos 3321) (Sat.Literal.pos 162) (Sat.Literal.pos 98) (positive_of_descriptor s 3322 (.lex permutation6 162) (by rfl)) (lex_6_162_prefix s) (positive_select s 162) (lex_6_162_image s)

theorem lex_6_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.pos 162), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation6 162 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3321) (Sat.Literal.pos 162) (Sat.Literal.pos 98) (lex_6_162_prefix s) (positive_select s 162) (lex_6_162_image s)

theorem lex_6_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.pos 3321)] :=
  (lex_6_162_gate s).prop _ (List.Mem.head _)

theorem lex_6_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.neg 162), (Sat.Literal.pos 98)] :=
  (lex_6_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.pos 162), (Sat.Literal.neg 98)] :=
  (lex_6_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.neg 162), (Sat.Literal.neg 98), (Sat.Literal.pos 3322)] :=
  (lex_6_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3321), (Sat.Literal.pos 162), (Sat.Literal.pos 98), (Sat.Literal.pos 3322)] :=
  (lex_6_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3322) = lexBefore s permutation6 161 := by
  exact (positive_lex_of_descriptor s 3322 permutation6 162 (by rfl)).trans ((lex_skipped s permutation6 161 162 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation6 161) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation6 161 by rw [image6_eq]; rfl))

theorem lex_6_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3323) (Sat.Literal.pos 3322) (Sat.Literal.pos 161) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation6 161 (assignment s)
    (Sat.Literal.pos 3323) (Sat.Literal.pos 3322) (Sat.Literal.pos 161) (Sat.Literal.pos 97) (positive_of_descriptor s 3323 (.lex permutation6 161) (by rfl)) (lex_6_161_prefix s) (positive_select s 161) (lex_6_161_image s)

theorem lex_6_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.pos 161), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation6 161 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3322) (Sat.Literal.pos 161) (Sat.Literal.pos 97) (lex_6_161_prefix s) (positive_select s 161) (lex_6_161_image s)

theorem lex_6_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.pos 3322)] :=
  (lex_6_161_gate s).prop _ (List.Mem.head _)

theorem lex_6_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.neg 161), (Sat.Literal.pos 97)] :=
  (lex_6_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.pos 161), (Sat.Literal.neg 97)] :=
  (lex_6_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.neg 161), (Sat.Literal.neg 97), (Sat.Literal.pos 3323)] :=
  (lex_6_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3322), (Sat.Literal.pos 161), (Sat.Literal.pos 97), (Sat.Literal.pos 3323)] :=
  (lex_6_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3323) = lexBefore s permutation6 160 := by
  exact (positive_lex_of_descriptor s 3323 permutation6 161 (by rfl)).trans ((lex_skipped s permutation6 160 161 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation6 160) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation6 160 by rw [image6_eq]; rfl))

theorem lex_6_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3324) (Sat.Literal.pos 3323) (Sat.Literal.pos 160) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation6 160 (assignment s)
    (Sat.Literal.pos 3324) (Sat.Literal.pos 3323) (Sat.Literal.pos 160) (Sat.Literal.pos 96) (positive_of_descriptor s 3324 (.lex permutation6 160) (by rfl)) (lex_6_160_prefix s) (positive_select s 160) (lex_6_160_image s)

theorem lex_6_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.pos 160), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation6 160 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3323) (Sat.Literal.pos 160) (Sat.Literal.pos 96) (lex_6_160_prefix s) (positive_select s 160) (lex_6_160_image s)

theorem lex_6_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.pos 3323)] :=
  (lex_6_160_gate s).prop _ (List.Mem.head _)

theorem lex_6_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.neg 160), (Sat.Literal.pos 96)] :=
  (lex_6_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.pos 160), (Sat.Literal.neg 96)] :=
  (lex_6_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.neg 160), (Sat.Literal.neg 96), (Sat.Literal.pos 3324)] :=
  (lex_6_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3323), (Sat.Literal.pos 160), (Sat.Literal.pos 96), (Sat.Literal.pos 3324)] :=
  (lex_6_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_5_163_gate

end Crown.CertificateData
