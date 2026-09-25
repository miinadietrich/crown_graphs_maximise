import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_10_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4324) = lexBefore s permutation10 101 := by
  exact (positive_lex_of_descriptor s 4324 permutation10 103 (by rfl)).trans ((lex_skipped s permutation10 101 103 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 102 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation10 101) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation10 101 by rw [image10_eq]; rfl))

theorem lex_10_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4325) (Sat.Literal.pos 4324) (Sat.Literal.pos 101) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation10 101 (assignment s)
    (Sat.Literal.pos 4325) (Sat.Literal.pos 4324) (Sat.Literal.pos 101) (Sat.Literal.pos 86) (positive_of_descriptor s 4325 (.lex permutation10 101) (by rfl)) (lex_10_101_prefix s) (positive_select s 101) (lex_10_101_image s)

theorem lex_10_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.pos 101), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation10 101 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4324) (Sat.Literal.pos 101) (Sat.Literal.pos 86) (lex_10_101_prefix s) (positive_select s 101) (lex_10_101_image s)

theorem lex_10_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.pos 4324)] :=
  (lex_10_101_gate s).prop _ (List.Mem.head _)

theorem lex_10_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.neg 101), (Sat.Literal.pos 86)] :=
  (lex_10_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.pos 101), (Sat.Literal.neg 86)] :=
  (lex_10_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.neg 101), (Sat.Literal.neg 86), (Sat.Literal.pos 4325)] :=
  (lex_10_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4324), (Sat.Literal.pos 101), (Sat.Literal.pos 86), (Sat.Literal.pos 4325)] :=
  (lex_10_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4325) = lexBefore s permutation10 100 := by
  exact (positive_lex_of_descriptor s 4325 permutation10 101 (by rfl)).trans ((lex_skipped s permutation10 100 101 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation10 100) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation10 100 by rw [image10_eq]; rfl))

theorem lex_10_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4326) (Sat.Literal.pos 4325) (Sat.Literal.pos 100) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation10 100 (assignment s)
    (Sat.Literal.pos 4326) (Sat.Literal.pos 4325) (Sat.Literal.pos 100) (Sat.Literal.pos 70) (positive_of_descriptor s 4326 (.lex permutation10 100) (by rfl)) (lex_10_100_prefix s) (positive_select s 100) (lex_10_100_image s)

theorem lex_10_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.pos 100), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation10 100 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4325) (Sat.Literal.pos 100) (Sat.Literal.pos 70) (lex_10_100_prefix s) (positive_select s 100) (lex_10_100_image s)

theorem lex_10_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.pos 4325)] :=
  (lex_10_100_gate s).prop _ (List.Mem.head _)

theorem lex_10_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.neg 100), (Sat.Literal.pos 70)] :=
  (lex_10_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.pos 100), (Sat.Literal.neg 70)] :=
  (lex_10_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.neg 100), (Sat.Literal.neg 70), (Sat.Literal.pos 4326)] :=
  (lex_10_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4325), (Sat.Literal.pos 100), (Sat.Literal.pos 70), (Sat.Literal.pos 4326)] :=
  (lex_10_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4326) = lexBefore s permutation10 99 := by
  exact (positive_lex_of_descriptor s 4326 permutation10 100 (by rfl)).trans ((lex_skipped s permutation10 99 100 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation10 99) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation10 99 by rw [image10_eq]; rfl))

theorem lex_10_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4327) (Sat.Literal.pos 4326) (Sat.Literal.pos 99) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation10 99 (assignment s)
    (Sat.Literal.pos 4327) (Sat.Literal.pos 4326) (Sat.Literal.pos 99) (Sat.Literal.pos 54) (positive_of_descriptor s 4327 (.lex permutation10 99) (by rfl)) (lex_10_99_prefix s) (positive_select s 99) (lex_10_99_image s)

theorem lex_10_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.pos 99), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation10 99 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4326) (Sat.Literal.pos 99) (Sat.Literal.pos 54) (lex_10_99_prefix s) (positive_select s 99) (lex_10_99_image s)

theorem lex_10_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.pos 4326)] :=
  (lex_10_99_gate s).prop _ (List.Mem.head _)

theorem lex_10_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.neg 99), (Sat.Literal.pos 54)] :=
  (lex_10_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.pos 99), (Sat.Literal.neg 54)] :=
  (lex_10_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.neg 99), (Sat.Literal.neg 54), (Sat.Literal.pos 4327)] :=
  (lex_10_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4326), (Sat.Literal.pos 99), (Sat.Literal.pos 54), (Sat.Literal.pos 4327)] :=
  (lex_10_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4327) = lexBefore s permutation10 98 := by
  exact (positive_lex_of_descriptor s 4327 permutation10 99 (by rfl)).trans ((lex_skipped s permutation10 98 99 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation10 98) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation10 98 by rw [image10_eq]; rfl))

theorem lex_10_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4328) (Sat.Literal.pos 4327) (Sat.Literal.pos 98) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation10 98 (assignment s)
    (Sat.Literal.pos 4328) (Sat.Literal.pos 4327) (Sat.Literal.pos 98) (Sat.Literal.pos 38) (positive_of_descriptor s 4328 (.lex permutation10 98) (by rfl)) (lex_10_98_prefix s) (positive_select s 98) (lex_10_98_image s)

theorem lex_10_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.pos 98), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation10 98 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4327) (Sat.Literal.pos 98) (Sat.Literal.pos 38) (lex_10_98_prefix s) (positive_select s 98) (lex_10_98_image s)

theorem lex_10_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.pos 4327)] :=
  (lex_10_98_gate s).prop _ (List.Mem.head _)

theorem lex_10_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.neg 98), (Sat.Literal.pos 38)] :=
  (lex_10_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.pos 98), (Sat.Literal.neg 38)] :=
  (lex_10_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.neg 98), (Sat.Literal.neg 38), (Sat.Literal.pos 4328)] :=
  (lex_10_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4327), (Sat.Literal.pos 98), (Sat.Literal.pos 38), (Sat.Literal.pos 4328)] :=
  (lex_10_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4328) = lexBefore s permutation10 97 := by
  exact (positive_lex_of_descriptor s 4328 permutation10 98 (by rfl)).trans ((lex_skipped s permutation10 97 98 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation10 97) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation10 97 by rw [image10_eq]; rfl))

theorem lex_10_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4329) (Sat.Literal.pos 4328) (Sat.Literal.pos 97) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation10 97 (assignment s)
    (Sat.Literal.pos 4329) (Sat.Literal.pos 4328) (Sat.Literal.pos 97) (Sat.Literal.pos 22) (positive_of_descriptor s 4329 (.lex permutation10 97) (by rfl)) (lex_10_97_prefix s) (positive_select s 97) (lex_10_97_image s)

theorem lex_10_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.pos 97), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation10 97 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4328) (Sat.Literal.pos 97) (Sat.Literal.pos 22) (lex_10_97_prefix s) (positive_select s 97) (lex_10_97_image s)

theorem lex_10_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.pos 4328)] :=
  (lex_10_97_gate s).prop _ (List.Mem.head _)

theorem lex_10_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.neg 97), (Sat.Literal.pos 22)] :=
  (lex_10_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.pos 97), (Sat.Literal.neg 22)] :=
  (lex_10_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.neg 97), (Sat.Literal.neg 22), (Sat.Literal.pos 4329)] :=
  (lex_10_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4328), (Sat.Literal.pos 97), (Sat.Literal.pos 22), (Sat.Literal.pos 4329)] :=
  (lex_10_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4329) = lexBefore s permutation10 96 := by
  exact (positive_lex_of_descriptor s 4329 permutation10 97 (by rfl)).trans ((lex_skipped s permutation10 96 97 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation10 96) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation10 96 by rw [image10_eq]; rfl))

theorem lex_10_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4330) (Sat.Literal.pos 4329) (Sat.Literal.pos 96) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation10 96 (assignment s)
    (Sat.Literal.pos 4330) (Sat.Literal.pos 4329) (Sat.Literal.pos 96) (Sat.Literal.pos 6) (positive_of_descriptor s 4330 (.lex permutation10 96) (by rfl)) (lex_10_96_prefix s) (positive_select s 96) (lex_10_96_image s)

theorem lex_10_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.pos 96), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation10 96 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4329) (Sat.Literal.pos 96) (Sat.Literal.pos 6) (lex_10_96_prefix s) (positive_select s 96) (lex_10_96_image s)

theorem lex_10_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.pos 4329)] :=
  (lex_10_96_gate s).prop _ (List.Mem.head _)

theorem lex_10_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.neg 96), (Sat.Literal.pos 6)] :=
  (lex_10_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.pos 96), (Sat.Literal.neg 6)] :=
  (lex_10_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.neg 96), (Sat.Literal.neg 6), (Sat.Literal.pos 4330)] :=
  (lex_10_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4329), (Sat.Literal.pos 96), (Sat.Literal.pos 6), (Sat.Literal.pos 4330)] :=
  (lex_10_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4330) = lexBefore s permutation10 95 := by
  exact (positive_lex_of_descriptor s 4330 permutation10 96 (by rfl)).trans ((lex_skipped s permutation10 95 96 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation10 95) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation10 95 by rw [image10_eq]; rfl))

theorem lex_10_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4331) (Sat.Literal.pos 4330) (Sat.Literal.pos 95) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation10 95 (assignment s)
    (Sat.Literal.pos 4331) (Sat.Literal.pos 4330) (Sat.Literal.pos 95) (Sat.Literal.pos 245) (positive_of_descriptor s 4331 (.lex permutation10 95) (by rfl)) (lex_10_95_prefix s) (positive_select s 95) (lex_10_95_image s)

theorem lex_10_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.pos 95), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation10 95 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4330) (Sat.Literal.pos 95) (Sat.Literal.pos 245) (lex_10_95_prefix s) (positive_select s 95) (lex_10_95_image s)

theorem lex_10_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.pos 4330)] :=
  (lex_10_95_gate s).prop _ (List.Mem.head _)

theorem lex_10_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.neg 95), (Sat.Literal.pos 245)] :=
  (lex_10_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.pos 95), (Sat.Literal.neg 245)] :=
  (lex_10_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.neg 95), (Sat.Literal.neg 245), (Sat.Literal.pos 4331)] :=
  (lex_10_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4330), (Sat.Literal.pos 95), (Sat.Literal.pos 245), (Sat.Literal.pos 4331)] :=
  (lex_10_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4331) = lexBefore s permutation10 94 := by
  exact (positive_lex_of_descriptor s 4331 permutation10 95 (by rfl)).trans ((lex_skipped s permutation10 94 95 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation10 94) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation10 94 by rw [image10_eq]; rfl))

theorem lex_10_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4332) (Sat.Literal.pos 4331) (Sat.Literal.pos 94) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation10 94 (assignment s)
    (Sat.Literal.pos 4332) (Sat.Literal.pos 4331) (Sat.Literal.pos 94) (Sat.Literal.pos 229) (positive_of_descriptor s 4332 (.lex permutation10 94) (by rfl)) (lex_10_94_prefix s) (positive_select s 94) (lex_10_94_image s)

theorem lex_10_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.pos 94), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation10 94 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4331) (Sat.Literal.pos 94) (Sat.Literal.pos 229) (lex_10_94_prefix s) (positive_select s 94) (lex_10_94_image s)

theorem lex_10_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.pos 4331)] :=
  (lex_10_94_gate s).prop _ (List.Mem.head _)

theorem lex_10_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.neg 94), (Sat.Literal.pos 229)] :=
  (lex_10_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.pos 94), (Sat.Literal.neg 229)] :=
  (lex_10_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.neg 94), (Sat.Literal.neg 229), (Sat.Literal.pos 4332)] :=
  (lex_10_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4331), (Sat.Literal.pos 94), (Sat.Literal.pos 229), (Sat.Literal.pos 4332)] :=
  (lex_10_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4332) = lexBefore s permutation10 93 := by
  exact (positive_lex_of_descriptor s 4332 permutation10 94 (by rfl)).trans ((lex_skipped s permutation10 93 94 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation10 93) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation10 93 by rw [image10_eq]; rfl))

theorem lex_10_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4333) (Sat.Literal.pos 4332) (Sat.Literal.pos 93) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation10 93 (assignment s)
    (Sat.Literal.pos 4333) (Sat.Literal.pos 4332) (Sat.Literal.pos 93) (Sat.Literal.pos 213) (positive_of_descriptor s 4333 (.lex permutation10 93) (by rfl)) (lex_10_93_prefix s) (positive_select s 93) (lex_10_93_image s)

theorem lex_10_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.pos 93), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation10 93 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4332) (Sat.Literal.pos 93) (Sat.Literal.pos 213) (lex_10_93_prefix s) (positive_select s 93) (lex_10_93_image s)

theorem lex_10_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.pos 4332)] :=
  (lex_10_93_gate s).prop _ (List.Mem.head _)

theorem lex_10_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.neg 93), (Sat.Literal.pos 213)] :=
  (lex_10_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.pos 93), (Sat.Literal.neg 213)] :=
  (lex_10_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.neg 93), (Sat.Literal.neg 213), (Sat.Literal.pos 4333)] :=
  (lex_10_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4332), (Sat.Literal.pos 93), (Sat.Literal.pos 213), (Sat.Literal.pos 4333)] :=
  (lex_10_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4333) = lexBefore s permutation10 92 := by
  exact (positive_lex_of_descriptor s 4333 permutation10 93 (by rfl)).trans ((lex_skipped s permutation10 92 93 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation10 92) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation10 92 by rw [image10_eq]; rfl))

theorem lex_10_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4334) (Sat.Literal.pos 4333) (Sat.Literal.pos 92) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation10 92 (assignment s)
    (Sat.Literal.pos 4334) (Sat.Literal.pos 4333) (Sat.Literal.pos 92) (Sat.Literal.pos 197) (positive_of_descriptor s 4334 (.lex permutation10 92) (by rfl)) (lex_10_92_prefix s) (positive_select s 92) (lex_10_92_image s)

theorem lex_10_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.pos 92), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation10 92 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4333) (Sat.Literal.pos 92) (Sat.Literal.pos 197) (lex_10_92_prefix s) (positive_select s 92) (lex_10_92_image s)

theorem lex_10_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.pos 4333)] :=
  (lex_10_92_gate s).prop _ (List.Mem.head _)

theorem lex_10_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.neg 92), (Sat.Literal.pos 197)] :=
  (lex_10_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.pos 92), (Sat.Literal.neg 197)] :=
  (lex_10_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.neg 92), (Sat.Literal.neg 197), (Sat.Literal.pos 4334)] :=
  (lex_10_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4333), (Sat.Literal.pos 92), (Sat.Literal.pos 197), (Sat.Literal.pos 4334)] :=
  (lex_10_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4334) = lexBefore s permutation10 91 := by
  exact (positive_lex_of_descriptor s 4334 permutation10 92 (by rfl)).trans ((lex_skipped s permutation10 91 92 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation10 91) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation10 91 by rw [image10_eq]; rfl))

theorem lex_10_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4335) (Sat.Literal.pos 4334) (Sat.Literal.pos 91) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation10 91 (assignment s)
    (Sat.Literal.pos 4335) (Sat.Literal.pos 4334) (Sat.Literal.pos 91) (Sat.Literal.pos 181) (positive_of_descriptor s 4335 (.lex permutation10 91) (by rfl)) (lex_10_91_prefix s) (positive_select s 91) (lex_10_91_image s)

theorem lex_10_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.pos 91), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation10 91 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4334) (Sat.Literal.pos 91) (Sat.Literal.pos 181) (lex_10_91_prefix s) (positive_select s 91) (lex_10_91_image s)

theorem lex_10_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.pos 4334)] :=
  (lex_10_91_gate s).prop _ (List.Mem.head _)

theorem lex_10_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.neg 91), (Sat.Literal.pos 181)] :=
  (lex_10_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.pos 91), (Sat.Literal.neg 181)] :=
  (lex_10_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.neg 91), (Sat.Literal.neg 181), (Sat.Literal.pos 4335)] :=
  (lex_10_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4334), (Sat.Literal.pos 91), (Sat.Literal.pos 181), (Sat.Literal.pos 4335)] :=
  (lex_10_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4335) = lexBefore s permutation10 90 := by
  exact (positive_lex_of_descriptor s 4335 permutation10 91 (by rfl)).trans ((lex_skipped s permutation10 90 91 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation10 90) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation10 90 by rw [image10_eq]; rfl))

theorem lex_10_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4336) (Sat.Literal.pos 4335) (Sat.Literal.pos 90) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation10 90 (assignment s)
    (Sat.Literal.pos 4336) (Sat.Literal.pos 4335) (Sat.Literal.pos 90) (Sat.Literal.pos 165) (positive_of_descriptor s 4336 (.lex permutation10 90) (by rfl)) (lex_10_90_prefix s) (positive_select s 90) (lex_10_90_image s)

theorem lex_10_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.pos 90), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation10 90 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4335) (Sat.Literal.pos 90) (Sat.Literal.pos 165) (lex_10_90_prefix s) (positive_select s 90) (lex_10_90_image s)

theorem lex_10_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.pos 4335)] :=
  (lex_10_90_gate s).prop _ (List.Mem.head _)

theorem lex_10_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.neg 90), (Sat.Literal.pos 165)] :=
  (lex_10_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.pos 90), (Sat.Literal.neg 165)] :=
  (lex_10_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.neg 90), (Sat.Literal.neg 165), (Sat.Literal.pos 4336)] :=
  (lex_10_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4335), (Sat.Literal.pos 90), (Sat.Literal.pos 165), (Sat.Literal.pos 4336)] :=
  (lex_10_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4336) = lexBefore s permutation10 89 := by
  exact (positive_lex_of_descriptor s 4336 permutation10 90 (by rfl)).trans ((lex_skipped s permutation10 89 90 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation10 89) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation10 89 by rw [image10_eq]; rfl))

theorem lex_10_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4337) (Sat.Literal.pos 4336) (Sat.Literal.pos 89) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation10 89 (assignment s)
    (Sat.Literal.pos 4337) (Sat.Literal.pos 4336) (Sat.Literal.pos 89) (Sat.Literal.pos 149) (positive_of_descriptor s 4337 (.lex permutation10 89) (by rfl)) (lex_10_89_prefix s) (positive_select s 89) (lex_10_89_image s)

theorem lex_10_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.pos 89), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation10 89 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4336) (Sat.Literal.pos 89) (Sat.Literal.pos 149) (lex_10_89_prefix s) (positive_select s 89) (lex_10_89_image s)

theorem lex_10_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.pos 4336)] :=
  (lex_10_89_gate s).prop _ (List.Mem.head _)

theorem lex_10_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.neg 89), (Sat.Literal.pos 149)] :=
  (lex_10_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.pos 89), (Sat.Literal.neg 149)] :=
  (lex_10_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.neg 89), (Sat.Literal.neg 149), (Sat.Literal.pos 4337)] :=
  (lex_10_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4336), (Sat.Literal.pos 89), (Sat.Literal.pos 149), (Sat.Literal.pos 4337)] :=
  (lex_10_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4337) = lexBefore s permutation10 88 := by
  exact (positive_lex_of_descriptor s 4337 permutation10 89 (by rfl)).trans ((lex_skipped s permutation10 88 89 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation10 88) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation10 88 by rw [image10_eq]; rfl))

theorem lex_10_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4338) (Sat.Literal.pos 4337) (Sat.Literal.pos 88) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation10 88 (assignment s)
    (Sat.Literal.pos 4338) (Sat.Literal.pos 4337) (Sat.Literal.pos 88) (Sat.Literal.pos 133) (positive_of_descriptor s 4338 (.lex permutation10 88) (by rfl)) (lex_10_88_prefix s) (positive_select s 88) (lex_10_88_image s)

theorem lex_10_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.pos 88), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation10 88 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4337) (Sat.Literal.pos 88) (Sat.Literal.pos 133) (lex_10_88_prefix s) (positive_select s 88) (lex_10_88_image s)

theorem lex_10_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.pos 4337)] :=
  (lex_10_88_gate s).prop _ (List.Mem.head _)

theorem lex_10_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.neg 88), (Sat.Literal.pos 133)] :=
  (lex_10_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.pos 88), (Sat.Literal.neg 133)] :=
  (lex_10_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.neg 88), (Sat.Literal.neg 133), (Sat.Literal.pos 4338)] :=
  (lex_10_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4337), (Sat.Literal.pos 88), (Sat.Literal.pos 133), (Sat.Literal.pos 4338)] :=
  (lex_10_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4338) = lexBefore s permutation10 87 := by
  exact (positive_lex_of_descriptor s 4338 permutation10 88 (by rfl)).trans ((lex_skipped s permutation10 87 88 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation10 87) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation10 87 by rw [image10_eq]; rfl))

theorem lex_10_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4339) (Sat.Literal.pos 4338) (Sat.Literal.pos 87) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation10 87 (assignment s)
    (Sat.Literal.pos 4339) (Sat.Literal.pos 4338) (Sat.Literal.pos 87) (Sat.Literal.pos 117) (positive_of_descriptor s 4339 (.lex permutation10 87) (by rfl)) (lex_10_87_prefix s) (positive_select s 87) (lex_10_87_image s)

theorem lex_10_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.pos 87), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation10 87 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4338) (Sat.Literal.pos 87) (Sat.Literal.pos 117) (lex_10_87_prefix s) (positive_select s 87) (lex_10_87_image s)

theorem lex_10_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.pos 4338)] :=
  (lex_10_87_gate s).prop _ (List.Mem.head _)

theorem lex_10_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.neg 87), (Sat.Literal.pos 117)] :=
  (lex_10_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.pos 87), (Sat.Literal.neg 117)] :=
  (lex_10_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.neg 87), (Sat.Literal.neg 117), (Sat.Literal.pos 4339)] :=
  (lex_10_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4338), (Sat.Literal.pos 87), (Sat.Literal.pos 117), (Sat.Literal.pos 4339)] :=
  (lex_10_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4339) = lexBefore s permutation10 86 := by
  exact (positive_lex_of_descriptor s 4339 permutation10 87 (by rfl)).trans ((lex_skipped s permutation10 86 87 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation10 86) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation10 86 by rw [image10_eq]; rfl))

theorem lex_10_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4340) (Sat.Literal.pos 4339) (Sat.Literal.pos 86) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation10 86 (assignment s)
    (Sat.Literal.pos 4340) (Sat.Literal.pos 4339) (Sat.Literal.pos 86) (Sat.Literal.pos 101) (positive_of_descriptor s 4340 (.lex permutation10 86) (by rfl)) (lex_10_86_prefix s) (positive_select s 86) (lex_10_86_image s)

theorem lex_10_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.pos 86), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation10 86 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4339) (Sat.Literal.pos 86) (Sat.Literal.pos 101) (lex_10_86_prefix s) (positive_select s 86) (lex_10_86_image s)

theorem lex_10_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.pos 4339)] :=
  (lex_10_86_gate s).prop _ (List.Mem.head _)

theorem lex_10_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.neg 86), (Sat.Literal.pos 101)] :=
  (lex_10_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.pos 86), (Sat.Literal.neg 101)] :=
  (lex_10_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.neg 86), (Sat.Literal.neg 101), (Sat.Literal.pos 4340)] :=
  (lex_10_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4339), (Sat.Literal.pos 86), (Sat.Literal.pos 101), (Sat.Literal.pos 4340)] :=
  (lex_10_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4340) = lexBefore s permutation10 84 := by
  exact (positive_lex_of_descriptor s 4340 permutation10 86 (by rfl)).trans ((lex_skipped s permutation10 84 86 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 85 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation10 84) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation10 84 by rw [image10_eq]; rfl))

theorem lex_10_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4341) (Sat.Literal.pos 4340) (Sat.Literal.pos 84) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation10 84 (assignment s)
    (Sat.Literal.pos 4341) (Sat.Literal.pos 4340) (Sat.Literal.pos 84) (Sat.Literal.pos 69) (positive_of_descriptor s 4341 (.lex permutation10 84) (by rfl)) (lex_10_84_prefix s) (positive_select s 84) (lex_10_84_image s)

theorem lex_10_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.pos 84), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation10 84 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4340) (Sat.Literal.pos 84) (Sat.Literal.pos 69) (lex_10_84_prefix s) (positive_select s 84) (lex_10_84_image s)

theorem lex_10_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.pos 4340)] :=
  (lex_10_84_gate s).prop _ (List.Mem.head _)

theorem lex_10_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.neg 84), (Sat.Literal.pos 69)] :=
  (lex_10_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.pos 84), (Sat.Literal.neg 69)] :=
  (lex_10_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.neg 84), (Sat.Literal.neg 69), (Sat.Literal.pos 4341)] :=
  (lex_10_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4340), (Sat.Literal.pos 84), (Sat.Literal.pos 69), (Sat.Literal.pos 4341)] :=
  (lex_10_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4341) = lexBefore s permutation10 83 := by
  exact (positive_lex_of_descriptor s 4341 permutation10 84 (by rfl)).trans ((lex_skipped s permutation10 83 84 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation10 83) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation10 83 by rw [image10_eq]; rfl))

theorem lex_10_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4342) (Sat.Literal.pos 4341) (Sat.Literal.pos 83) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation10 83 (assignment s)
    (Sat.Literal.pos 4342) (Sat.Literal.pos 4341) (Sat.Literal.pos 83) (Sat.Literal.pos 53) (positive_of_descriptor s 4342 (.lex permutation10 83) (by rfl)) (lex_10_83_prefix s) (positive_select s 83) (lex_10_83_image s)

theorem lex_10_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.pos 83), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation10 83 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4341) (Sat.Literal.pos 83) (Sat.Literal.pos 53) (lex_10_83_prefix s) (positive_select s 83) (lex_10_83_image s)

theorem lex_10_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.pos 4341)] :=
  (lex_10_83_gate s).prop _ (List.Mem.head _)

theorem lex_10_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.neg 83), (Sat.Literal.pos 53)] :=
  (lex_10_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.pos 83), (Sat.Literal.neg 53)] :=
  (lex_10_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.neg 83), (Sat.Literal.neg 53), (Sat.Literal.pos 4342)] :=
  (lex_10_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4341), (Sat.Literal.pos 83), (Sat.Literal.pos 53), (Sat.Literal.pos 4342)] :=
  (lex_10_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4342) = lexBefore s permutation10 82 := by
  exact (positive_lex_of_descriptor s 4342 permutation10 83 (by rfl)).trans ((lex_skipped s permutation10 82 83 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation10 82) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation10 82 by rw [image10_eq]; rfl))

theorem lex_10_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4343) (Sat.Literal.pos 4342) (Sat.Literal.pos 82) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation10 82 (assignment s)
    (Sat.Literal.pos 4343) (Sat.Literal.pos 4342) (Sat.Literal.pos 82) (Sat.Literal.pos 37) (positive_of_descriptor s 4343 (.lex permutation10 82) (by rfl)) (lex_10_82_prefix s) (positive_select s 82) (lex_10_82_image s)

theorem lex_10_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.pos 82), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation10 82 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4342) (Sat.Literal.pos 82) (Sat.Literal.pos 37) (lex_10_82_prefix s) (positive_select s 82) (lex_10_82_image s)

theorem lex_10_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.pos 4342)] :=
  (lex_10_82_gate s).prop _ (List.Mem.head _)

theorem lex_10_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.neg 82), (Sat.Literal.pos 37)] :=
  (lex_10_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.pos 82), (Sat.Literal.neg 37)] :=
  (lex_10_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.neg 82), (Sat.Literal.neg 37), (Sat.Literal.pos 4343)] :=
  (lex_10_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4342), (Sat.Literal.pos 82), (Sat.Literal.pos 37), (Sat.Literal.pos 4343)] :=
  (lex_10_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4343) = lexBefore s permutation10 81 := by
  exact (positive_lex_of_descriptor s 4343 permutation10 82 (by rfl)).trans ((lex_skipped s permutation10 81 82 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation10 81) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation10 81 by rw [image10_eq]; rfl))

theorem lex_10_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4344) (Sat.Literal.pos 4343) (Sat.Literal.pos 81) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation10 81 (assignment s)
    (Sat.Literal.pos 4344) (Sat.Literal.pos 4343) (Sat.Literal.pos 81) (Sat.Literal.pos 21) (positive_of_descriptor s 4344 (.lex permutation10 81) (by rfl)) (lex_10_81_prefix s) (positive_select s 81) (lex_10_81_image s)

theorem lex_10_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.pos 81), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation10 81 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4343) (Sat.Literal.pos 81) (Sat.Literal.pos 21) (lex_10_81_prefix s) (positive_select s 81) (lex_10_81_image s)

theorem lex_10_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.pos 4343)] :=
  (lex_10_81_gate s).prop _ (List.Mem.head _)

theorem lex_10_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.neg 81), (Sat.Literal.pos 21)] :=
  (lex_10_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.pos 81), (Sat.Literal.neg 21)] :=
  (lex_10_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.neg 81), (Sat.Literal.neg 21), (Sat.Literal.pos 4344)] :=
  (lex_10_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4343), (Sat.Literal.pos 81), (Sat.Literal.pos 21), (Sat.Literal.pos 4344)] :=
  (lex_10_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4344) = lexBefore s permutation10 80 := by
  exact (positive_lex_of_descriptor s 4344 permutation10 81 (by rfl)).trans ((lex_skipped s permutation10 80 81 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation10 80) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation10 80 by rw [image10_eq]; rfl))

theorem lex_10_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4345) (Sat.Literal.pos 4344) (Sat.Literal.pos 80) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation10 80 (assignment s)
    (Sat.Literal.pos 4345) (Sat.Literal.pos 4344) (Sat.Literal.pos 80) (Sat.Literal.pos 5) (positive_of_descriptor s 4345 (.lex permutation10 80) (by rfl)) (lex_10_80_prefix s) (positive_select s 80) (lex_10_80_image s)

theorem lex_10_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.pos 80), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation10 80 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4344) (Sat.Literal.pos 80) (Sat.Literal.pos 5) (lex_10_80_prefix s) (positive_select s 80) (lex_10_80_image s)

theorem lex_10_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.pos 4344)] :=
  (lex_10_80_gate s).prop _ (List.Mem.head _)

theorem lex_10_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.neg 80), (Sat.Literal.pos 5)] :=
  (lex_10_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.pos 80), (Sat.Literal.neg 5)] :=
  (lex_10_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.neg 80), (Sat.Literal.neg 5), (Sat.Literal.pos 4345)] :=
  (lex_10_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4344), (Sat.Literal.pos 80), (Sat.Literal.pos 5), (Sat.Literal.pos 4345)] :=
  (lex_10_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4345) = lexBefore s permutation10 79 := by
  exact (positive_lex_of_descriptor s 4345 permutation10 80 (by rfl)).trans ((lex_skipped s permutation10 79 80 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation10 79) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation10 79 by rw [image10_eq]; rfl))

theorem lex_10_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4346) (Sat.Literal.pos 4345) (Sat.Literal.pos 79) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation10 79 (assignment s)
    (Sat.Literal.pos 4346) (Sat.Literal.pos 4345) (Sat.Literal.pos 79) (Sat.Literal.pos 244) (positive_of_descriptor s 4346 (.lex permutation10 79) (by rfl)) (lex_10_79_prefix s) (positive_select s 79) (lex_10_79_image s)

theorem lex_10_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.pos 79), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation10 79 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4345) (Sat.Literal.pos 79) (Sat.Literal.pos 244) (lex_10_79_prefix s) (positive_select s 79) (lex_10_79_image s)

theorem lex_10_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.pos 4345)] :=
  (lex_10_79_gate s).prop _ (List.Mem.head _)

theorem lex_10_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.neg 79), (Sat.Literal.pos 244)] :=
  (lex_10_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.pos 79), (Sat.Literal.neg 244)] :=
  (lex_10_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.neg 79), (Sat.Literal.neg 244), (Sat.Literal.pos 4346)] :=
  (lex_10_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4345), (Sat.Literal.pos 79), (Sat.Literal.pos 244), (Sat.Literal.pos 4346)] :=
  (lex_10_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4346) = lexBefore s permutation10 78 := by
  exact (positive_lex_of_descriptor s 4346 permutation10 79 (by rfl)).trans ((lex_skipped s permutation10 78 79 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation10 78) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation10 78 by rw [image10_eq]; rfl))

theorem lex_10_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4347) (Sat.Literal.pos 4346) (Sat.Literal.pos 78) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation10 78 (assignment s)
    (Sat.Literal.pos 4347) (Sat.Literal.pos 4346) (Sat.Literal.pos 78) (Sat.Literal.pos 228) (positive_of_descriptor s 4347 (.lex permutation10 78) (by rfl)) (lex_10_78_prefix s) (positive_select s 78) (lex_10_78_image s)

theorem lex_10_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.pos 78), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation10 78 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4346) (Sat.Literal.pos 78) (Sat.Literal.pos 228) (lex_10_78_prefix s) (positive_select s 78) (lex_10_78_image s)

theorem lex_10_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.pos 4346)] :=
  (lex_10_78_gate s).prop _ (List.Mem.head _)

theorem lex_10_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.neg 78), (Sat.Literal.pos 228)] :=
  (lex_10_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.pos 78), (Sat.Literal.neg 228)] :=
  (lex_10_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.neg 78), (Sat.Literal.neg 228), (Sat.Literal.pos 4347)] :=
  (lex_10_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4346), (Sat.Literal.pos 78), (Sat.Literal.pos 228), (Sat.Literal.pos 4347)] :=
  (lex_10_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4347) = lexBefore s permutation10 77 := by
  exact (positive_lex_of_descriptor s 4347 permutation10 78 (by rfl)).trans ((lex_skipped s permutation10 77 78 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation10 77) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation10 77 by rw [image10_eq]; rfl))

theorem lex_10_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4348) (Sat.Literal.pos 4347) (Sat.Literal.pos 77) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation10 77 (assignment s)
    (Sat.Literal.pos 4348) (Sat.Literal.pos 4347) (Sat.Literal.pos 77) (Sat.Literal.pos 212) (positive_of_descriptor s 4348 (.lex permutation10 77) (by rfl)) (lex_10_77_prefix s) (positive_select s 77) (lex_10_77_image s)

theorem lex_10_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.pos 77), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation10 77 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4347) (Sat.Literal.pos 77) (Sat.Literal.pos 212) (lex_10_77_prefix s) (positive_select s 77) (lex_10_77_image s)

theorem lex_10_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.pos 4347)] :=
  (lex_10_77_gate s).prop _ (List.Mem.head _)

theorem lex_10_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.neg 77), (Sat.Literal.pos 212)] :=
  (lex_10_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.pos 77), (Sat.Literal.neg 212)] :=
  (lex_10_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.neg 77), (Sat.Literal.neg 212), (Sat.Literal.pos 4348)] :=
  (lex_10_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4347), (Sat.Literal.pos 77), (Sat.Literal.pos 212), (Sat.Literal.pos 4348)] :=
  (lex_10_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4348) = lexBefore s permutation10 76 := by
  exact (positive_lex_of_descriptor s 4348 permutation10 77 (by rfl)).trans ((lex_skipped s permutation10 76 77 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation10 76) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation10 76 by rw [image10_eq]; rfl))

theorem lex_10_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4349) (Sat.Literal.pos 4348) (Sat.Literal.pos 76) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation10 76 (assignment s)
    (Sat.Literal.pos 4349) (Sat.Literal.pos 4348) (Sat.Literal.pos 76) (Sat.Literal.pos 196) (positive_of_descriptor s 4349 (.lex permutation10 76) (by rfl)) (lex_10_76_prefix s) (positive_select s 76) (lex_10_76_image s)

theorem lex_10_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.pos 76), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation10 76 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4348) (Sat.Literal.pos 76) (Sat.Literal.pos 196) (lex_10_76_prefix s) (positive_select s 76) (lex_10_76_image s)

theorem lex_10_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.pos 4348)] :=
  (lex_10_76_gate s).prop _ (List.Mem.head _)

theorem lex_10_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.neg 76), (Sat.Literal.pos 196)] :=
  (lex_10_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.pos 76), (Sat.Literal.neg 196)] :=
  (lex_10_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.neg 76), (Sat.Literal.neg 196), (Sat.Literal.pos 4349)] :=
  (lex_10_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4348), (Sat.Literal.pos 76), (Sat.Literal.pos 196), (Sat.Literal.pos 4349)] :=
  (lex_10_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4349) = lexBefore s permutation10 75 := by
  exact (positive_lex_of_descriptor s 4349 permutation10 76 (by rfl)).trans ((lex_skipped s permutation10 75 76 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation10 75) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation10 75 by rw [image10_eq]; rfl))

theorem lex_10_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4350) (Sat.Literal.pos 4349) (Sat.Literal.pos 75) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation10 75 (assignment s)
    (Sat.Literal.pos 4350) (Sat.Literal.pos 4349) (Sat.Literal.pos 75) (Sat.Literal.pos 180) (positive_of_descriptor s 4350 (.lex permutation10 75) (by rfl)) (lex_10_75_prefix s) (positive_select s 75) (lex_10_75_image s)

theorem lex_10_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.pos 75), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation10 75 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4349) (Sat.Literal.pos 75) (Sat.Literal.pos 180) (lex_10_75_prefix s) (positive_select s 75) (lex_10_75_image s)

theorem lex_10_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.pos 4349)] :=
  (lex_10_75_gate s).prop _ (List.Mem.head _)

theorem lex_10_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.neg 75), (Sat.Literal.pos 180)] :=
  (lex_10_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.pos 75), (Sat.Literal.neg 180)] :=
  (lex_10_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.neg 75), (Sat.Literal.neg 180), (Sat.Literal.pos 4350)] :=
  (lex_10_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4349), (Sat.Literal.pos 75), (Sat.Literal.pos 180), (Sat.Literal.pos 4350)] :=
  (lex_10_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4350) = lexBefore s permutation10 74 := by
  exact (positive_lex_of_descriptor s 4350 permutation10 75 (by rfl)).trans ((lex_skipped s permutation10 74 75 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation10 74) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation10 74 by rw [image10_eq]; rfl))

theorem lex_10_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4351) (Sat.Literal.pos 4350) (Sat.Literal.pos 74) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation10 74 (assignment s)
    (Sat.Literal.pos 4351) (Sat.Literal.pos 4350) (Sat.Literal.pos 74) (Sat.Literal.pos 164) (positive_of_descriptor s 4351 (.lex permutation10 74) (by rfl)) (lex_10_74_prefix s) (positive_select s 74) (lex_10_74_image s)

theorem lex_10_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.pos 74), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation10 74 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4350) (Sat.Literal.pos 74) (Sat.Literal.pos 164) (lex_10_74_prefix s) (positive_select s 74) (lex_10_74_image s)

theorem lex_10_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.pos 4350)] :=
  (lex_10_74_gate s).prop _ (List.Mem.head _)

theorem lex_10_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.neg 74), (Sat.Literal.pos 164)] :=
  (lex_10_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.pos 74), (Sat.Literal.neg 164)] :=
  (lex_10_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.neg 74), (Sat.Literal.neg 164), (Sat.Literal.pos 4351)] :=
  (lex_10_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4350), (Sat.Literal.pos 74), (Sat.Literal.pos 164), (Sat.Literal.pos 4351)] :=
  (lex_10_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4351) = lexBefore s permutation10 73 := by
  exact (positive_lex_of_descriptor s 4351 permutation10 74 (by rfl)).trans ((lex_skipped s permutation10 73 74 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation10 73) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation10 73 by rw [image10_eq]; rfl))

theorem lex_10_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4352) (Sat.Literal.pos 4351) (Sat.Literal.pos 73) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation10 73 (assignment s)
    (Sat.Literal.pos 4352) (Sat.Literal.pos 4351) (Sat.Literal.pos 73) (Sat.Literal.pos 148) (positive_of_descriptor s 4352 (.lex permutation10 73) (by rfl)) (lex_10_73_prefix s) (positive_select s 73) (lex_10_73_image s)

theorem lex_10_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.pos 73), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation10 73 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4351) (Sat.Literal.pos 73) (Sat.Literal.pos 148) (lex_10_73_prefix s) (positive_select s 73) (lex_10_73_image s)

theorem lex_10_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.pos 4351)] :=
  (lex_10_73_gate s).prop _ (List.Mem.head _)

theorem lex_10_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.neg 73), (Sat.Literal.pos 148)] :=
  (lex_10_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.pos 73), (Sat.Literal.neg 148)] :=
  (lex_10_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.neg 73), (Sat.Literal.neg 148), (Sat.Literal.pos 4352)] :=
  (lex_10_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4351), (Sat.Literal.pos 73), (Sat.Literal.pos 148), (Sat.Literal.pos 4352)] :=
  (lex_10_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4352) = lexBefore s permutation10 72 := by
  exact (positive_lex_of_descriptor s 4352 permutation10 73 (by rfl)).trans ((lex_skipped s permutation10 72 73 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation10 72) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation10 72 by rw [image10_eq]; rfl))

theorem lex_10_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4353) (Sat.Literal.pos 4352) (Sat.Literal.pos 72) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation10 72 (assignment s)
    (Sat.Literal.pos 4353) (Sat.Literal.pos 4352) (Sat.Literal.pos 72) (Sat.Literal.pos 132) (positive_of_descriptor s 4353 (.lex permutation10 72) (by rfl)) (lex_10_72_prefix s) (positive_select s 72) (lex_10_72_image s)

theorem lex_10_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.pos 72), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation10 72 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4352) (Sat.Literal.pos 72) (Sat.Literal.pos 132) (lex_10_72_prefix s) (positive_select s 72) (lex_10_72_image s)

theorem lex_10_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.pos 4352)] :=
  (lex_10_72_gate s).prop _ (List.Mem.head _)

theorem lex_10_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.neg 72), (Sat.Literal.pos 132)] :=
  (lex_10_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.pos 72), (Sat.Literal.neg 132)] :=
  (lex_10_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.neg 72), (Sat.Literal.neg 132), (Sat.Literal.pos 4353)] :=
  (lex_10_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4352), (Sat.Literal.pos 72), (Sat.Literal.pos 132), (Sat.Literal.pos 4353)] :=
  (lex_10_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4353) = lexBefore s permutation10 71 := by
  exact (positive_lex_of_descriptor s 4353 permutation10 72 (by rfl)).trans ((lex_skipped s permutation10 71 72 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation10 71) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation10 71 by rw [image10_eq]; rfl))

theorem lex_10_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4354) (Sat.Literal.pos 4353) (Sat.Literal.pos 71) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation10 71 (assignment s)
    (Sat.Literal.pos 4354) (Sat.Literal.pos 4353) (Sat.Literal.pos 71) (Sat.Literal.pos 116) (positive_of_descriptor s 4354 (.lex permutation10 71) (by rfl)) (lex_10_71_prefix s) (positive_select s 71) (lex_10_71_image s)

theorem lex_10_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.pos 71), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation10 71 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4353) (Sat.Literal.pos 71) (Sat.Literal.pos 116) (lex_10_71_prefix s) (positive_select s 71) (lex_10_71_image s)

theorem lex_10_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.pos 4353)] :=
  (lex_10_71_gate s).prop _ (List.Mem.head _)

theorem lex_10_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.neg 71), (Sat.Literal.pos 116)] :=
  (lex_10_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.pos 71), (Sat.Literal.neg 116)] :=
  (lex_10_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.neg 71), (Sat.Literal.neg 116), (Sat.Literal.pos 4354)] :=
  (lex_10_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4353), (Sat.Literal.pos 71), (Sat.Literal.pos 116), (Sat.Literal.pos 4354)] :=
  (lex_10_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4354) = lexBefore s permutation10 70 := by
  exact (positive_lex_of_descriptor s 4354 permutation10 71 (by rfl)).trans ((lex_skipped s permutation10 70 71 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation10 70) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation10 70 by rw [image10_eq]; rfl))

theorem lex_10_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4355) (Sat.Literal.pos 4354) (Sat.Literal.pos 70) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation10 70 (assignment s)
    (Sat.Literal.pos 4355) (Sat.Literal.pos 4354) (Sat.Literal.pos 70) (Sat.Literal.pos 100) (positive_of_descriptor s 4355 (.lex permutation10 70) (by rfl)) (lex_10_70_prefix s) (positive_select s 70) (lex_10_70_image s)

theorem lex_10_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.pos 70), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation10 70 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4354) (Sat.Literal.pos 70) (Sat.Literal.pos 100) (lex_10_70_prefix s) (positive_select s 70) (lex_10_70_image s)

theorem lex_10_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.pos 4354)] :=
  (lex_10_70_gate s).prop _ (List.Mem.head _)

theorem lex_10_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.neg 70), (Sat.Literal.pos 100)] :=
  (lex_10_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.pos 70), (Sat.Literal.neg 100)] :=
  (lex_10_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.neg 70), (Sat.Literal.neg 100), (Sat.Literal.pos 4355)] :=
  (lex_10_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4354), (Sat.Literal.pos 70), (Sat.Literal.pos 100), (Sat.Literal.pos 4355)] :=
  (lex_10_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4355) = lexBefore s permutation10 69 := by
  exact (positive_lex_of_descriptor s 4355 permutation10 70 (by rfl)).trans ((lex_skipped s permutation10 69 70 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation10 69) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation10 69 by rw [image10_eq]; rfl))

theorem lex_10_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4356) (Sat.Literal.pos 4355) (Sat.Literal.pos 69) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation10 69 (assignment s)
    (Sat.Literal.pos 4356) (Sat.Literal.pos 4355) (Sat.Literal.pos 69) (Sat.Literal.pos 84) (positive_of_descriptor s 4356 (.lex permutation10 69) (by rfl)) (lex_10_69_prefix s) (positive_select s 69) (lex_10_69_image s)

theorem lex_10_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.pos 69), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation10 69 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4355) (Sat.Literal.pos 69) (Sat.Literal.pos 84) (lex_10_69_prefix s) (positive_select s 69) (lex_10_69_image s)

theorem lex_10_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.pos 4355)] :=
  (lex_10_69_gate s).prop _ (List.Mem.head _)

theorem lex_10_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.neg 69), (Sat.Literal.pos 84)] :=
  (lex_10_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.pos 69), (Sat.Literal.neg 84)] :=
  (lex_10_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.neg 69), (Sat.Literal.neg 84), (Sat.Literal.pos 4356)] :=
  (lex_10_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4355), (Sat.Literal.pos 69), (Sat.Literal.pos 84), (Sat.Literal.pos 4356)] :=
  (lex_10_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4356) = lexBefore s permutation10 67 := by
  exact (positive_lex_of_descriptor s 4356 permutation10 69 (by rfl)).trans ((lex_skipped s permutation10 67 69 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 68 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation10 67) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation10 67 by rw [image10_eq]; rfl))

theorem lex_10_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4357) (Sat.Literal.pos 4356) (Sat.Literal.pos 67) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation10 67 (assignment s)
    (Sat.Literal.pos 4357) (Sat.Literal.pos 4356) (Sat.Literal.pos 67) (Sat.Literal.pos 52) (positive_of_descriptor s 4357 (.lex permutation10 67) (by rfl)) (lex_10_67_prefix s) (positive_select s 67) (lex_10_67_image s)

theorem lex_10_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.pos 67), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation10 67 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4356) (Sat.Literal.pos 67) (Sat.Literal.pos 52) (lex_10_67_prefix s) (positive_select s 67) (lex_10_67_image s)

theorem lex_10_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.pos 4356)] :=
  (lex_10_67_gate s).prop _ (List.Mem.head _)

theorem lex_10_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.neg 67), (Sat.Literal.pos 52)] :=
  (lex_10_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.pos 67), (Sat.Literal.neg 52)] :=
  (lex_10_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.neg 67), (Sat.Literal.neg 52), (Sat.Literal.pos 4357)] :=
  (lex_10_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4356), (Sat.Literal.pos 67), (Sat.Literal.pos 52), (Sat.Literal.pos 4357)] :=
  (lex_10_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4357) = lexBefore s permutation10 66 := by
  exact (positive_lex_of_descriptor s 4357 permutation10 67 (by rfl)).trans ((lex_skipped s permutation10 66 67 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation10 66) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation10 66 by rw [image10_eq]; rfl))

theorem lex_10_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4358) (Sat.Literal.pos 4357) (Sat.Literal.pos 66) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation10 66 (assignment s)
    (Sat.Literal.pos 4358) (Sat.Literal.pos 4357) (Sat.Literal.pos 66) (Sat.Literal.pos 36) (positive_of_descriptor s 4358 (.lex permutation10 66) (by rfl)) (lex_10_66_prefix s) (positive_select s 66) (lex_10_66_image s)

theorem lex_10_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.pos 66), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation10 66 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4357) (Sat.Literal.pos 66) (Sat.Literal.pos 36) (lex_10_66_prefix s) (positive_select s 66) (lex_10_66_image s)

theorem lex_10_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.pos 4357)] :=
  (lex_10_66_gate s).prop _ (List.Mem.head _)

theorem lex_10_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.neg 66), (Sat.Literal.pos 36)] :=
  (lex_10_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.pos 66), (Sat.Literal.neg 36)] :=
  (lex_10_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.neg 66), (Sat.Literal.neg 36), (Sat.Literal.pos 4358)] :=
  (lex_10_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4357), (Sat.Literal.pos 66), (Sat.Literal.pos 36), (Sat.Literal.pos 4358)] :=
  (lex_10_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4358) = lexBefore s permutation10 65 := by
  exact (positive_lex_of_descriptor s 4358 permutation10 66 (by rfl)).trans ((lex_skipped s permutation10 65 66 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation10 65) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation10 65 by rw [image10_eq]; rfl))

theorem lex_10_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4359) (Sat.Literal.pos 4358) (Sat.Literal.pos 65) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation10 65 (assignment s)
    (Sat.Literal.pos 4359) (Sat.Literal.pos 4358) (Sat.Literal.pos 65) (Sat.Literal.pos 20) (positive_of_descriptor s 4359 (.lex permutation10 65) (by rfl)) (lex_10_65_prefix s) (positive_select s 65) (lex_10_65_image s)

theorem lex_10_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.pos 65), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation10 65 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4358) (Sat.Literal.pos 65) (Sat.Literal.pos 20) (lex_10_65_prefix s) (positive_select s 65) (lex_10_65_image s)

theorem lex_10_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.pos 4358)] :=
  (lex_10_65_gate s).prop _ (List.Mem.head _)

theorem lex_10_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.neg 65), (Sat.Literal.pos 20)] :=
  (lex_10_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.pos 65), (Sat.Literal.neg 20)] :=
  (lex_10_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.neg 65), (Sat.Literal.neg 20), (Sat.Literal.pos 4359)] :=
  (lex_10_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4358), (Sat.Literal.pos 65), (Sat.Literal.pos 20), (Sat.Literal.pos 4359)] :=
  (lex_10_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4359) = lexBefore s permutation10 64 := by
  exact (positive_lex_of_descriptor s 4359 permutation10 65 (by rfl)).trans ((lex_skipped s permutation10 64 65 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation10 64) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation10 64 by rw [image10_eq]; rfl))

theorem lex_10_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4360) (Sat.Literal.pos 4359) (Sat.Literal.pos 64) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation10 64 (assignment s)
    (Sat.Literal.pos 4360) (Sat.Literal.pos 4359) (Sat.Literal.pos 64) (Sat.Literal.pos 4) (positive_of_descriptor s 4360 (.lex permutation10 64) (by rfl)) (lex_10_64_prefix s) (positive_select s 64) (lex_10_64_image s)

theorem lex_10_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.pos 64), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation10 64 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4359) (Sat.Literal.pos 64) (Sat.Literal.pos 4) (lex_10_64_prefix s) (positive_select s 64) (lex_10_64_image s)

theorem lex_10_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.pos 4359)] :=
  (lex_10_64_gate s).prop _ (List.Mem.head _)

theorem lex_10_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.neg 64), (Sat.Literal.pos 4)] :=
  (lex_10_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.pos 64), (Sat.Literal.neg 4)] :=
  (lex_10_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.neg 64), (Sat.Literal.neg 4), (Sat.Literal.pos 4360)] :=
  (lex_10_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4359), (Sat.Literal.pos 64), (Sat.Literal.pos 4), (Sat.Literal.pos 4360)] :=
  (lex_10_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4360) = lexBefore s permutation10 63 := by
  exact (positive_lex_of_descriptor s 4360 permutation10 64 (by rfl)).trans ((lex_skipped s permutation10 63 64 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation10 63) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation10 63 by rw [image10_eq]; rfl))

theorem lex_10_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4361) (Sat.Literal.pos 4360) (Sat.Literal.pos 63) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation10 63 (assignment s)
    (Sat.Literal.pos 4361) (Sat.Literal.pos 4360) (Sat.Literal.pos 63) (Sat.Literal.pos 243) (positive_of_descriptor s 4361 (.lex permutation10 63) (by rfl)) (lex_10_63_prefix s) (positive_select s 63) (lex_10_63_image s)

theorem lex_10_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.pos 63), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation10 63 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4360) (Sat.Literal.pos 63) (Sat.Literal.pos 243) (lex_10_63_prefix s) (positive_select s 63) (lex_10_63_image s)

theorem lex_10_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.pos 4360)] :=
  (lex_10_63_gate s).prop _ (List.Mem.head _)

theorem lex_10_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.neg 63), (Sat.Literal.pos 243)] :=
  (lex_10_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.pos 63), (Sat.Literal.neg 243)] :=
  (lex_10_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.neg 63), (Sat.Literal.neg 243), (Sat.Literal.pos 4361)] :=
  (lex_10_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4360), (Sat.Literal.pos 63), (Sat.Literal.pos 243), (Sat.Literal.pos 4361)] :=
  (lex_10_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4361) = lexBefore s permutation10 62 := by
  exact (positive_lex_of_descriptor s 4361 permutation10 63 (by rfl)).trans ((lex_skipped s permutation10 62 63 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation10 62) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation10 62 by rw [image10_eq]; rfl))

theorem lex_10_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4362) (Sat.Literal.pos 4361) (Sat.Literal.pos 62) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation10 62 (assignment s)
    (Sat.Literal.pos 4362) (Sat.Literal.pos 4361) (Sat.Literal.pos 62) (Sat.Literal.pos 227) (positive_of_descriptor s 4362 (.lex permutation10 62) (by rfl)) (lex_10_62_prefix s) (positive_select s 62) (lex_10_62_image s)

theorem lex_10_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.pos 62), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation10 62 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4361) (Sat.Literal.pos 62) (Sat.Literal.pos 227) (lex_10_62_prefix s) (positive_select s 62) (lex_10_62_image s)

theorem lex_10_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.pos 4361)] :=
  (lex_10_62_gate s).prop _ (List.Mem.head _)

theorem lex_10_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.neg 62), (Sat.Literal.pos 227)] :=
  (lex_10_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.pos 62), (Sat.Literal.neg 227)] :=
  (lex_10_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.neg 62), (Sat.Literal.neg 227), (Sat.Literal.pos 4362)] :=
  (lex_10_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4361), (Sat.Literal.pos 62), (Sat.Literal.pos 227), (Sat.Literal.pos 4362)] :=
  (lex_10_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4362) = lexBefore s permutation10 61 := by
  exact (positive_lex_of_descriptor s 4362 permutation10 62 (by rfl)).trans ((lex_skipped s permutation10 61 62 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation10 61) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation10 61 by rw [image10_eq]; rfl))

theorem lex_10_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4363) (Sat.Literal.pos 4362) (Sat.Literal.pos 61) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation10 61 (assignment s)
    (Sat.Literal.pos 4363) (Sat.Literal.pos 4362) (Sat.Literal.pos 61) (Sat.Literal.pos 211) (positive_of_descriptor s 4363 (.lex permutation10 61) (by rfl)) (lex_10_61_prefix s) (positive_select s 61) (lex_10_61_image s)

theorem lex_10_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.pos 61), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation10 61 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4362) (Sat.Literal.pos 61) (Sat.Literal.pos 211) (lex_10_61_prefix s) (positive_select s 61) (lex_10_61_image s)

theorem lex_10_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.pos 4362)] :=
  (lex_10_61_gate s).prop _ (List.Mem.head _)

theorem lex_10_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.neg 61), (Sat.Literal.pos 211)] :=
  (lex_10_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.pos 61), (Sat.Literal.neg 211)] :=
  (lex_10_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.neg 61), (Sat.Literal.neg 211), (Sat.Literal.pos 4363)] :=
  (lex_10_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4362), (Sat.Literal.pos 61), (Sat.Literal.pos 211), (Sat.Literal.pos 4363)] :=
  (lex_10_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4363) = lexBefore s permutation10 60 := by
  exact (positive_lex_of_descriptor s 4363 permutation10 61 (by rfl)).trans ((lex_skipped s permutation10 60 61 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation10 60) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation10 60 by rw [image10_eq]; rfl))

theorem lex_10_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4364) (Sat.Literal.pos 4363) (Sat.Literal.pos 60) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation10 60 (assignment s)
    (Sat.Literal.pos 4364) (Sat.Literal.pos 4363) (Sat.Literal.pos 60) (Sat.Literal.pos 195) (positive_of_descriptor s 4364 (.lex permutation10 60) (by rfl)) (lex_10_60_prefix s) (positive_select s 60) (lex_10_60_image s)

theorem lex_10_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.pos 60), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation10 60 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4363) (Sat.Literal.pos 60) (Sat.Literal.pos 195) (lex_10_60_prefix s) (positive_select s 60) (lex_10_60_image s)

theorem lex_10_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.pos 4363)] :=
  (lex_10_60_gate s).prop _ (List.Mem.head _)

theorem lex_10_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.neg 60), (Sat.Literal.pos 195)] :=
  (lex_10_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.pos 60), (Sat.Literal.neg 195)] :=
  (lex_10_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.neg 60), (Sat.Literal.neg 195), (Sat.Literal.pos 4364)] :=
  (lex_10_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4363), (Sat.Literal.pos 60), (Sat.Literal.pos 195), (Sat.Literal.pos 4364)] :=
  (lex_10_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4364) = lexBefore s permutation10 59 := by
  exact (positive_lex_of_descriptor s 4364 permutation10 60 (by rfl)).trans ((lex_skipped s permutation10 59 60 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation10 59) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation10 59 by rw [image10_eq]; rfl))

theorem lex_10_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4365) (Sat.Literal.pos 4364) (Sat.Literal.pos 59) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation10 59 (assignment s)
    (Sat.Literal.pos 4365) (Sat.Literal.pos 4364) (Sat.Literal.pos 59) (Sat.Literal.pos 179) (positive_of_descriptor s 4365 (.lex permutation10 59) (by rfl)) (lex_10_59_prefix s) (positive_select s 59) (lex_10_59_image s)

theorem lex_10_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.pos 59), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation10 59 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4364) (Sat.Literal.pos 59) (Sat.Literal.pos 179) (lex_10_59_prefix s) (positive_select s 59) (lex_10_59_image s)

theorem lex_10_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.pos 4364)] :=
  (lex_10_59_gate s).prop _ (List.Mem.head _)

theorem lex_10_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.neg 59), (Sat.Literal.pos 179)] :=
  (lex_10_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.pos 59), (Sat.Literal.neg 179)] :=
  (lex_10_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.neg 59), (Sat.Literal.neg 179), (Sat.Literal.pos 4365)] :=
  (lex_10_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4364), (Sat.Literal.pos 59), (Sat.Literal.pos 179), (Sat.Literal.pos 4365)] :=
  (lex_10_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4365) = lexBefore s permutation10 58 := by
  exact (positive_lex_of_descriptor s 4365 permutation10 59 (by rfl)).trans ((lex_skipped s permutation10 58 59 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation10 58) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation10 58 by rw [image10_eq]; rfl))

theorem lex_10_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4366) (Sat.Literal.pos 4365) (Sat.Literal.pos 58) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation10 58 (assignment s)
    (Sat.Literal.pos 4366) (Sat.Literal.pos 4365) (Sat.Literal.pos 58) (Sat.Literal.pos 163) (positive_of_descriptor s 4366 (.lex permutation10 58) (by rfl)) (lex_10_58_prefix s) (positive_select s 58) (lex_10_58_image s)

theorem lex_10_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.pos 58), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation10 58 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4365) (Sat.Literal.pos 58) (Sat.Literal.pos 163) (lex_10_58_prefix s) (positive_select s 58) (lex_10_58_image s)

theorem lex_10_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.pos 4365)] :=
  (lex_10_58_gate s).prop _ (List.Mem.head _)

theorem lex_10_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.neg 58), (Sat.Literal.pos 163)] :=
  (lex_10_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.pos 58), (Sat.Literal.neg 163)] :=
  (lex_10_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.neg 58), (Sat.Literal.neg 163), (Sat.Literal.pos 4366)] :=
  (lex_10_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4365), (Sat.Literal.pos 58), (Sat.Literal.pos 163), (Sat.Literal.pos 4366)] :=
  (lex_10_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4366) = lexBefore s permutation10 57 := by
  exact (positive_lex_of_descriptor s 4366 permutation10 58 (by rfl)).trans ((lex_skipped s permutation10 57 58 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation10 57) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation10 57 by rw [image10_eq]; rfl))

theorem lex_10_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4367) (Sat.Literal.pos 4366) (Sat.Literal.pos 57) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation10 57 (assignment s)
    (Sat.Literal.pos 4367) (Sat.Literal.pos 4366) (Sat.Literal.pos 57) (Sat.Literal.pos 147) (positive_of_descriptor s 4367 (.lex permutation10 57) (by rfl)) (lex_10_57_prefix s) (positive_select s 57) (lex_10_57_image s)

theorem lex_10_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.pos 57), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation10 57 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4366) (Sat.Literal.pos 57) (Sat.Literal.pos 147) (lex_10_57_prefix s) (positive_select s 57) (lex_10_57_image s)

theorem lex_10_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.pos 4366)] :=
  (lex_10_57_gate s).prop _ (List.Mem.head _)

theorem lex_10_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.neg 57), (Sat.Literal.pos 147)] :=
  (lex_10_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.pos 57), (Sat.Literal.neg 147)] :=
  (lex_10_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.neg 57), (Sat.Literal.neg 147), (Sat.Literal.pos 4367)] :=
  (lex_10_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4366), (Sat.Literal.pos 57), (Sat.Literal.pos 147), (Sat.Literal.pos 4367)] :=
  (lex_10_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4367) = lexBefore s permutation10 56 := by
  exact (positive_lex_of_descriptor s 4367 permutation10 57 (by rfl)).trans ((lex_skipped s permutation10 56 57 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation10 56) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation10 56 by rw [image10_eq]; rfl))

theorem lex_10_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4368) (Sat.Literal.pos 4367) (Sat.Literal.pos 56) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation10 56 (assignment s)
    (Sat.Literal.pos 4368) (Sat.Literal.pos 4367) (Sat.Literal.pos 56) (Sat.Literal.pos 131) (positive_of_descriptor s 4368 (.lex permutation10 56) (by rfl)) (lex_10_56_prefix s) (positive_select s 56) (lex_10_56_image s)

theorem lex_10_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.pos 56), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation10 56 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4367) (Sat.Literal.pos 56) (Sat.Literal.pos 131) (lex_10_56_prefix s) (positive_select s 56) (lex_10_56_image s)

theorem lex_10_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.pos 4367)] :=
  (lex_10_56_gate s).prop _ (List.Mem.head _)

theorem lex_10_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.neg 56), (Sat.Literal.pos 131)] :=
  (lex_10_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.pos 56), (Sat.Literal.neg 131)] :=
  (lex_10_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.neg 56), (Sat.Literal.neg 131), (Sat.Literal.pos 4368)] :=
  (lex_10_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4367), (Sat.Literal.pos 56), (Sat.Literal.pos 131), (Sat.Literal.pos 4368)] :=
  (lex_10_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4368) = lexBefore s permutation10 55 := by
  exact (positive_lex_of_descriptor s 4368 permutation10 56 (by rfl)).trans ((lex_skipped s permutation10 55 56 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation10 55) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation10 55 by rw [image10_eq]; rfl))

theorem lex_10_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4369) (Sat.Literal.pos 4368) (Sat.Literal.pos 55) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation10 55 (assignment s)
    (Sat.Literal.pos 4369) (Sat.Literal.pos 4368) (Sat.Literal.pos 55) (Sat.Literal.pos 115) (positive_of_descriptor s 4369 (.lex permutation10 55) (by rfl)) (lex_10_55_prefix s) (positive_select s 55) (lex_10_55_image s)

theorem lex_10_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.pos 55), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation10 55 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4368) (Sat.Literal.pos 55) (Sat.Literal.pos 115) (lex_10_55_prefix s) (positive_select s 55) (lex_10_55_image s)

theorem lex_10_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.pos 4368)] :=
  (lex_10_55_gate s).prop _ (List.Mem.head _)

theorem lex_10_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.neg 55), (Sat.Literal.pos 115)] :=
  (lex_10_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.pos 55), (Sat.Literal.neg 115)] :=
  (lex_10_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.neg 55), (Sat.Literal.neg 115), (Sat.Literal.pos 4369)] :=
  (lex_10_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4368), (Sat.Literal.pos 55), (Sat.Literal.pos 115), (Sat.Literal.pos 4369)] :=
  (lex_10_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4369) = lexBefore s permutation10 54 := by
  exact (positive_lex_of_descriptor s 4369 permutation10 55 (by rfl)).trans ((lex_skipped s permutation10 54 55 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation10 54) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation10 54 by rw [image10_eq]; rfl))

theorem lex_10_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4370) (Sat.Literal.pos 4369) (Sat.Literal.pos 54) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation10 54 (assignment s)
    (Sat.Literal.pos 4370) (Sat.Literal.pos 4369) (Sat.Literal.pos 54) (Sat.Literal.pos 99) (positive_of_descriptor s 4370 (.lex permutation10 54) (by rfl)) (lex_10_54_prefix s) (positive_select s 54) (lex_10_54_image s)

theorem lex_10_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.pos 54), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation10 54 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4369) (Sat.Literal.pos 54) (Sat.Literal.pos 99) (lex_10_54_prefix s) (positive_select s 54) (lex_10_54_image s)

theorem lex_10_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.pos 4369)] :=
  (lex_10_54_gate s).prop _ (List.Mem.head _)

theorem lex_10_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.neg 54), (Sat.Literal.pos 99)] :=
  (lex_10_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.pos 54), (Sat.Literal.neg 99)] :=
  (lex_10_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.neg 54), (Sat.Literal.neg 99), (Sat.Literal.pos 4370)] :=
  (lex_10_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4369), (Sat.Literal.pos 54), (Sat.Literal.pos 99), (Sat.Literal.pos 4370)] :=
  (lex_10_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4370) = lexBefore s permutation10 53 := by
  exact (positive_lex_of_descriptor s 4370 permutation10 54 (by rfl)).trans ((lex_skipped s permutation10 53 54 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation10 53) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation10 53 by rw [image10_eq]; rfl))

theorem lex_10_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4371) (Sat.Literal.pos 4370) (Sat.Literal.pos 53) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation10 53 (assignment s)
    (Sat.Literal.pos 4371) (Sat.Literal.pos 4370) (Sat.Literal.pos 53) (Sat.Literal.pos 83) (positive_of_descriptor s 4371 (.lex permutation10 53) (by rfl)) (lex_10_53_prefix s) (positive_select s 53) (lex_10_53_image s)

theorem lex_10_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.pos 53), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation10 53 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4370) (Sat.Literal.pos 53) (Sat.Literal.pos 83) (lex_10_53_prefix s) (positive_select s 53) (lex_10_53_image s)

theorem lex_10_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.pos 4370)] :=
  (lex_10_53_gate s).prop _ (List.Mem.head _)

theorem lex_10_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.neg 53), (Sat.Literal.pos 83)] :=
  (lex_10_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.pos 53), (Sat.Literal.neg 83)] :=
  (lex_10_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.neg 53), (Sat.Literal.neg 83), (Sat.Literal.pos 4371)] :=
  (lex_10_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4370), (Sat.Literal.pos 53), (Sat.Literal.pos 83), (Sat.Literal.pos 4371)] :=
  (lex_10_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4371) = lexBefore s permutation10 52 := by
  exact (positive_lex_of_descriptor s 4371 permutation10 53 (by rfl)).trans ((lex_skipped s permutation10 52 53 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation10 52) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation10 52 by rw [image10_eq]; rfl))

theorem lex_10_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4372) (Sat.Literal.pos 4371) (Sat.Literal.pos 52) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation10 52 (assignment s)
    (Sat.Literal.pos 4372) (Sat.Literal.pos 4371) (Sat.Literal.pos 52) (Sat.Literal.pos 67) (positive_of_descriptor s 4372 (.lex permutation10 52) (by rfl)) (lex_10_52_prefix s) (positive_select s 52) (lex_10_52_image s)

theorem lex_10_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.pos 52), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation10 52 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4371) (Sat.Literal.pos 52) (Sat.Literal.pos 67) (lex_10_52_prefix s) (positive_select s 52) (lex_10_52_image s)

theorem lex_10_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.pos 4371)] :=
  (lex_10_52_gate s).prop _ (List.Mem.head _)

theorem lex_10_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.neg 52), (Sat.Literal.pos 67)] :=
  (lex_10_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.pos 52), (Sat.Literal.neg 67)] :=
  (lex_10_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.neg 52), (Sat.Literal.neg 67), (Sat.Literal.pos 4372)] :=
  (lex_10_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4371), (Sat.Literal.pos 52), (Sat.Literal.pos 67), (Sat.Literal.pos 4372)] :=
  (lex_10_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4372) = lexBefore s permutation10 50 := by
  exact (positive_lex_of_descriptor s 4372 permutation10 52 (by rfl)).trans ((lex_skipped s permutation10 50 52 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 51 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation10 50) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation10 50 by rw [image10_eq]; rfl))

theorem lex_10_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4373) (Sat.Literal.pos 4372) (Sat.Literal.pos 50) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation10 50 (assignment s)
    (Sat.Literal.pos 4373) (Sat.Literal.pos 4372) (Sat.Literal.pos 50) (Sat.Literal.pos 35) (positive_of_descriptor s 4373 (.lex permutation10 50) (by rfl)) (lex_10_50_prefix s) (positive_select s 50) (lex_10_50_image s)

theorem lex_10_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.pos 50), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation10 50 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4372) (Sat.Literal.pos 50) (Sat.Literal.pos 35) (lex_10_50_prefix s) (positive_select s 50) (lex_10_50_image s)

theorem lex_10_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.pos 4372)] :=
  (lex_10_50_gate s).prop _ (List.Mem.head _)

theorem lex_10_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.neg 50), (Sat.Literal.pos 35)] :=
  (lex_10_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.pos 50), (Sat.Literal.neg 35)] :=
  (lex_10_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.neg 50), (Sat.Literal.neg 35), (Sat.Literal.pos 4373)] :=
  (lex_10_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4372), (Sat.Literal.pos 50), (Sat.Literal.pos 35), (Sat.Literal.pos 4373)] :=
  (lex_10_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4373) = lexBefore s permutation10 49 := by
  exact (positive_lex_of_descriptor s 4373 permutation10 50 (by rfl)).trans ((lex_skipped s permutation10 49 50 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation10 49) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation10 49 by rw [image10_eq]; rfl))

theorem lex_10_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4374) (Sat.Literal.pos 4373) (Sat.Literal.pos 49) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation10 49 (assignment s)
    (Sat.Literal.pos 4374) (Sat.Literal.pos 4373) (Sat.Literal.pos 49) (Sat.Literal.pos 19) (positive_of_descriptor s 4374 (.lex permutation10 49) (by rfl)) (lex_10_49_prefix s) (positive_select s 49) (lex_10_49_image s)

theorem lex_10_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.pos 49), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation10 49 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4373) (Sat.Literal.pos 49) (Sat.Literal.pos 19) (lex_10_49_prefix s) (positive_select s 49) (lex_10_49_image s)

theorem lex_10_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.pos 4373)] :=
  (lex_10_49_gate s).prop _ (List.Mem.head _)

theorem lex_10_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.neg 49), (Sat.Literal.pos 19)] :=
  (lex_10_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.pos 49), (Sat.Literal.neg 19)] :=
  (lex_10_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.neg 49), (Sat.Literal.neg 19), (Sat.Literal.pos 4374)] :=
  (lex_10_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4373), (Sat.Literal.pos 49), (Sat.Literal.pos 19), (Sat.Literal.pos 4374)] :=
  (lex_10_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4374) = lexBefore s permutation10 48 := by
  exact (positive_lex_of_descriptor s 4374 permutation10 49 (by rfl)).trans ((lex_skipped s permutation10 48 49 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation10 48) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation10 48 by rw [image10_eq]; rfl))

theorem lex_10_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4375) (Sat.Literal.pos 4374) (Sat.Literal.pos 48) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation10 48 (assignment s)
    (Sat.Literal.pos 4375) (Sat.Literal.pos 4374) (Sat.Literal.pos 48) (Sat.Literal.pos 3) (positive_of_descriptor s 4375 (.lex permutation10 48) (by rfl)) (lex_10_48_prefix s) (positive_select s 48) (lex_10_48_image s)

theorem lex_10_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.pos 48), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation10 48 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4374) (Sat.Literal.pos 48) (Sat.Literal.pos 3) (lex_10_48_prefix s) (positive_select s 48) (lex_10_48_image s)

theorem lex_10_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.pos 4374)] :=
  (lex_10_48_gate s).prop _ (List.Mem.head _)

theorem lex_10_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.neg 48), (Sat.Literal.pos 3)] :=
  (lex_10_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.pos 48), (Sat.Literal.neg 3)] :=
  (lex_10_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.neg 48), (Sat.Literal.neg 3), (Sat.Literal.pos 4375)] :=
  (lex_10_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4374), (Sat.Literal.pos 48), (Sat.Literal.pos 3), (Sat.Literal.pos 4375)] :=
  (lex_10_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4375) = lexBefore s permutation10 47 := by
  exact (positive_lex_of_descriptor s 4375 permutation10 48 (by rfl)).trans ((lex_skipped s permutation10 47 48 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation10 47) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation10 47 by rw [image10_eq]; rfl))

theorem lex_10_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4376) (Sat.Literal.pos 4375) (Sat.Literal.pos 47) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation10 47 (assignment s)
    (Sat.Literal.pos 4376) (Sat.Literal.pos 4375) (Sat.Literal.pos 47) (Sat.Literal.pos 242) (positive_of_descriptor s 4376 (.lex permutation10 47) (by rfl)) (lex_10_47_prefix s) (positive_select s 47) (lex_10_47_image s)

theorem lex_10_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.pos 47), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation10 47 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4375) (Sat.Literal.pos 47) (Sat.Literal.pos 242) (lex_10_47_prefix s) (positive_select s 47) (lex_10_47_image s)

theorem lex_10_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.pos 4375)] :=
  (lex_10_47_gate s).prop _ (List.Mem.head _)

theorem lex_10_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.neg 47), (Sat.Literal.pos 242)] :=
  (lex_10_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.pos 47), (Sat.Literal.neg 242)] :=
  (lex_10_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.neg 47), (Sat.Literal.neg 242), (Sat.Literal.pos 4376)] :=
  (lex_10_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4375), (Sat.Literal.pos 47), (Sat.Literal.pos 242), (Sat.Literal.pos 4376)] :=
  (lex_10_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4376) = lexBefore s permutation10 46 := by
  exact (positive_lex_of_descriptor s 4376 permutation10 47 (by rfl)).trans ((lex_skipped s permutation10 46 47 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation10 46) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation10 46 by rw [image10_eq]; rfl))

theorem lex_10_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4377) (Sat.Literal.pos 4376) (Sat.Literal.pos 46) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation10 46 (assignment s)
    (Sat.Literal.pos 4377) (Sat.Literal.pos 4376) (Sat.Literal.pos 46) (Sat.Literal.pos 226) (positive_of_descriptor s 4377 (.lex permutation10 46) (by rfl)) (lex_10_46_prefix s) (positive_select s 46) (lex_10_46_image s)

theorem lex_10_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.pos 46), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation10 46 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4376) (Sat.Literal.pos 46) (Sat.Literal.pos 226) (lex_10_46_prefix s) (positive_select s 46) (lex_10_46_image s)

theorem lex_10_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.pos 4376)] :=
  (lex_10_46_gate s).prop _ (List.Mem.head _)

theorem lex_10_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.neg 46), (Sat.Literal.pos 226)] :=
  (lex_10_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.pos 46), (Sat.Literal.neg 226)] :=
  (lex_10_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.neg 46), (Sat.Literal.neg 226), (Sat.Literal.pos 4377)] :=
  (lex_10_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4376), (Sat.Literal.pos 46), (Sat.Literal.pos 226), (Sat.Literal.pos 4377)] :=
  (lex_10_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4377) = lexBefore s permutation10 45 := by
  exact (positive_lex_of_descriptor s 4377 permutation10 46 (by rfl)).trans ((lex_skipped s permutation10 45 46 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation10 45) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation10 45 by rw [image10_eq]; rfl))

theorem lex_10_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4378) (Sat.Literal.pos 4377) (Sat.Literal.pos 45) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation10 45 (assignment s)
    (Sat.Literal.pos 4378) (Sat.Literal.pos 4377) (Sat.Literal.pos 45) (Sat.Literal.pos 210) (positive_of_descriptor s 4378 (.lex permutation10 45) (by rfl)) (lex_10_45_prefix s) (positive_select s 45) (lex_10_45_image s)

theorem lex_10_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.pos 45), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation10 45 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4377) (Sat.Literal.pos 45) (Sat.Literal.pos 210) (lex_10_45_prefix s) (positive_select s 45) (lex_10_45_image s)

theorem lex_10_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.pos 4377)] :=
  (lex_10_45_gate s).prop _ (List.Mem.head _)

theorem lex_10_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.neg 45), (Sat.Literal.pos 210)] :=
  (lex_10_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.pos 45), (Sat.Literal.neg 210)] :=
  (lex_10_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.neg 45), (Sat.Literal.neg 210), (Sat.Literal.pos 4378)] :=
  (lex_10_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4377), (Sat.Literal.pos 45), (Sat.Literal.pos 210), (Sat.Literal.pos 4378)] :=
  (lex_10_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4378) = lexBefore s permutation10 44 := by
  exact (positive_lex_of_descriptor s 4378 permutation10 45 (by rfl)).trans ((lex_skipped s permutation10 44 45 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation10 44) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation10 44 by rw [image10_eq]; rfl))

theorem lex_10_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4379) (Sat.Literal.pos 4378) (Sat.Literal.pos 44) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation10 44 (assignment s)
    (Sat.Literal.pos 4379) (Sat.Literal.pos 4378) (Sat.Literal.pos 44) (Sat.Literal.pos 194) (positive_of_descriptor s 4379 (.lex permutation10 44) (by rfl)) (lex_10_44_prefix s) (positive_select s 44) (lex_10_44_image s)

theorem lex_10_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.pos 44), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation10 44 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4378) (Sat.Literal.pos 44) (Sat.Literal.pos 194) (lex_10_44_prefix s) (positive_select s 44) (lex_10_44_image s)

theorem lex_10_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.pos 4378)] :=
  (lex_10_44_gate s).prop _ (List.Mem.head _)

theorem lex_10_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.neg 44), (Sat.Literal.pos 194)] :=
  (lex_10_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.pos 44), (Sat.Literal.neg 194)] :=
  (lex_10_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.neg 44), (Sat.Literal.neg 194), (Sat.Literal.pos 4379)] :=
  (lex_10_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4378), (Sat.Literal.pos 44), (Sat.Literal.pos 194), (Sat.Literal.pos 4379)] :=
  (lex_10_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4379) = lexBefore s permutation10 43 := by
  exact (positive_lex_of_descriptor s 4379 permutation10 44 (by rfl)).trans ((lex_skipped s permutation10 43 44 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation10 43) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation10 43 by rw [image10_eq]; rfl))

theorem lex_10_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4380) (Sat.Literal.pos 4379) (Sat.Literal.pos 43) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation10 43 (assignment s)
    (Sat.Literal.pos 4380) (Sat.Literal.pos 4379) (Sat.Literal.pos 43) (Sat.Literal.pos 178) (positive_of_descriptor s 4380 (.lex permutation10 43) (by rfl)) (lex_10_43_prefix s) (positive_select s 43) (lex_10_43_image s)

theorem lex_10_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.pos 43), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation10 43 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4379) (Sat.Literal.pos 43) (Sat.Literal.pos 178) (lex_10_43_prefix s) (positive_select s 43) (lex_10_43_image s)

theorem lex_10_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.pos 4379)] :=
  (lex_10_43_gate s).prop _ (List.Mem.head _)

theorem lex_10_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.neg 43), (Sat.Literal.pos 178)] :=
  (lex_10_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.pos 43), (Sat.Literal.neg 178)] :=
  (lex_10_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.neg 43), (Sat.Literal.neg 178), (Sat.Literal.pos 4380)] :=
  (lex_10_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4379), (Sat.Literal.pos 43), (Sat.Literal.pos 178), (Sat.Literal.pos 4380)] :=
  (lex_10_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4380) = lexBefore s permutation10 42 := by
  exact (positive_lex_of_descriptor s 4380 permutation10 43 (by rfl)).trans ((lex_skipped s permutation10 42 43 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation10 42) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation10 42 by rw [image10_eq]; rfl))

theorem lex_10_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4381) (Sat.Literal.pos 4380) (Sat.Literal.pos 42) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation10 42 (assignment s)
    (Sat.Literal.pos 4381) (Sat.Literal.pos 4380) (Sat.Literal.pos 42) (Sat.Literal.pos 162) (positive_of_descriptor s 4381 (.lex permutation10 42) (by rfl)) (lex_10_42_prefix s) (positive_select s 42) (lex_10_42_image s)

theorem lex_10_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.pos 42), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation10 42 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4380) (Sat.Literal.pos 42) (Sat.Literal.pos 162) (lex_10_42_prefix s) (positive_select s 42) (lex_10_42_image s)

theorem lex_10_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.pos 4380)] :=
  (lex_10_42_gate s).prop _ (List.Mem.head _)

theorem lex_10_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.neg 42), (Sat.Literal.pos 162)] :=
  (lex_10_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.pos 42), (Sat.Literal.neg 162)] :=
  (lex_10_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.neg 42), (Sat.Literal.neg 162), (Sat.Literal.pos 4381)] :=
  (lex_10_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4380), (Sat.Literal.pos 42), (Sat.Literal.pos 162), (Sat.Literal.pos 4381)] :=
  (lex_10_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4381) = lexBefore s permutation10 41 := by
  exact (positive_lex_of_descriptor s 4381 permutation10 42 (by rfl)).trans ((lex_skipped s permutation10 41 42 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation10 41) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation10 41 by rw [image10_eq]; rfl))

theorem lex_10_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4382) (Sat.Literal.pos 4381) (Sat.Literal.pos 41) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation10 41 (assignment s)
    (Sat.Literal.pos 4382) (Sat.Literal.pos 4381) (Sat.Literal.pos 41) (Sat.Literal.pos 146) (positive_of_descriptor s 4382 (.lex permutation10 41) (by rfl)) (lex_10_41_prefix s) (positive_select s 41) (lex_10_41_image s)

theorem lex_10_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.pos 41), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation10 41 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4381) (Sat.Literal.pos 41) (Sat.Literal.pos 146) (lex_10_41_prefix s) (positive_select s 41) (lex_10_41_image s)

theorem lex_10_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.pos 4381)] :=
  (lex_10_41_gate s).prop _ (List.Mem.head _)

theorem lex_10_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.neg 41), (Sat.Literal.pos 146)] :=
  (lex_10_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.pos 41), (Sat.Literal.neg 146)] :=
  (lex_10_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.neg 41), (Sat.Literal.neg 146), (Sat.Literal.pos 4382)] :=
  (lex_10_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4381), (Sat.Literal.pos 41), (Sat.Literal.pos 146), (Sat.Literal.pos 4382)] :=
  (lex_10_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4382) = lexBefore s permutation10 40 := by
  exact (positive_lex_of_descriptor s 4382 permutation10 41 (by rfl)).trans ((lex_skipped s permutation10 40 41 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation10 40) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation10 40 by rw [image10_eq]; rfl))

theorem lex_10_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4383) (Sat.Literal.pos 4382) (Sat.Literal.pos 40) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation10 40 (assignment s)
    (Sat.Literal.pos 4383) (Sat.Literal.pos 4382) (Sat.Literal.pos 40) (Sat.Literal.pos 130) (positive_of_descriptor s 4383 (.lex permutation10 40) (by rfl)) (lex_10_40_prefix s) (positive_select s 40) (lex_10_40_image s)

theorem lex_10_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.pos 40), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation10 40 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4382) (Sat.Literal.pos 40) (Sat.Literal.pos 130) (lex_10_40_prefix s) (positive_select s 40) (lex_10_40_image s)

theorem lex_10_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.pos 4382)] :=
  (lex_10_40_gate s).prop _ (List.Mem.head _)

theorem lex_10_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.neg 40), (Sat.Literal.pos 130)] :=
  (lex_10_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.pos 40), (Sat.Literal.neg 130)] :=
  (lex_10_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.neg 40), (Sat.Literal.neg 130), (Sat.Literal.pos 4383)] :=
  (lex_10_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4382), (Sat.Literal.pos 40), (Sat.Literal.pos 130), (Sat.Literal.pos 4383)] :=
  (lex_10_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4383) = lexBefore s permutation10 39 := by
  exact (positive_lex_of_descriptor s 4383 permutation10 40 (by rfl)).trans ((lex_skipped s permutation10 39 40 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation10 39) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation10 39 by rw [image10_eq]; rfl))

theorem lex_10_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4384) (Sat.Literal.pos 4383) (Sat.Literal.pos 39) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation10 39 (assignment s)
    (Sat.Literal.pos 4384) (Sat.Literal.pos 4383) (Sat.Literal.pos 39) (Sat.Literal.pos 114) (positive_of_descriptor s 4384 (.lex permutation10 39) (by rfl)) (lex_10_39_prefix s) (positive_select s 39) (lex_10_39_image s)

theorem lex_10_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.pos 39), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation10 39 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4383) (Sat.Literal.pos 39) (Sat.Literal.pos 114) (lex_10_39_prefix s) (positive_select s 39) (lex_10_39_image s)

theorem lex_10_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.pos 4383)] :=
  (lex_10_39_gate s).prop _ (List.Mem.head _)

theorem lex_10_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.neg 39), (Sat.Literal.pos 114)] :=
  (lex_10_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.pos 39), (Sat.Literal.neg 114)] :=
  (lex_10_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.neg 39), (Sat.Literal.neg 114), (Sat.Literal.pos 4384)] :=
  (lex_10_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4383), (Sat.Literal.pos 39), (Sat.Literal.pos 114), (Sat.Literal.pos 4384)] :=
  (lex_10_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4384) = lexBefore s permutation10 38 := by
  exact (positive_lex_of_descriptor s 4384 permutation10 39 (by rfl)).trans ((lex_skipped s permutation10 38 39 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation10 38) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation10 38 by rw [image10_eq]; rfl))

theorem lex_10_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4385) (Sat.Literal.pos 4384) (Sat.Literal.pos 38) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation10 38 (assignment s)
    (Sat.Literal.pos 4385) (Sat.Literal.pos 4384) (Sat.Literal.pos 38) (Sat.Literal.pos 98) (positive_of_descriptor s 4385 (.lex permutation10 38) (by rfl)) (lex_10_38_prefix s) (positive_select s 38) (lex_10_38_image s)

theorem lex_10_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.pos 38), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation10 38 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4384) (Sat.Literal.pos 38) (Sat.Literal.pos 98) (lex_10_38_prefix s) (positive_select s 38) (lex_10_38_image s)

theorem lex_10_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.pos 4384)] :=
  (lex_10_38_gate s).prop _ (List.Mem.head _)

theorem lex_10_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.neg 38), (Sat.Literal.pos 98)] :=
  (lex_10_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.pos 38), (Sat.Literal.neg 98)] :=
  (lex_10_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.neg 38), (Sat.Literal.neg 98), (Sat.Literal.pos 4385)] :=
  (lex_10_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4384), (Sat.Literal.pos 38), (Sat.Literal.pos 98), (Sat.Literal.pos 4385)] :=
  (lex_10_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4385) = lexBefore s permutation10 37 := by
  exact (positive_lex_of_descriptor s 4385 permutation10 38 (by rfl)).trans ((lex_skipped s permutation10 37 38 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation10 37) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation10 37 by rw [image10_eq]; rfl))

theorem lex_10_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4386) (Sat.Literal.pos 4385) (Sat.Literal.pos 37) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation10 37 (assignment s)
    (Sat.Literal.pos 4386) (Sat.Literal.pos 4385) (Sat.Literal.pos 37) (Sat.Literal.pos 82) (positive_of_descriptor s 4386 (.lex permutation10 37) (by rfl)) (lex_10_37_prefix s) (positive_select s 37) (lex_10_37_image s)

theorem lex_10_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.pos 37), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation10 37 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4385) (Sat.Literal.pos 37) (Sat.Literal.pos 82) (lex_10_37_prefix s) (positive_select s 37) (lex_10_37_image s)

theorem lex_10_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.pos 4385)] :=
  (lex_10_37_gate s).prop _ (List.Mem.head _)

theorem lex_10_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.neg 37), (Sat.Literal.pos 82)] :=
  (lex_10_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.pos 37), (Sat.Literal.neg 82)] :=
  (lex_10_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.neg 37), (Sat.Literal.neg 82), (Sat.Literal.pos 4386)] :=
  (lex_10_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4385), (Sat.Literal.pos 37), (Sat.Literal.pos 82), (Sat.Literal.pos 4386)] :=
  (lex_10_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4386) = lexBefore s permutation10 36 := by
  exact (positive_lex_of_descriptor s 4386 permutation10 37 (by rfl)).trans ((lex_skipped s permutation10 36 37 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation10 36) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation10 36 by rw [image10_eq]; rfl))

theorem lex_10_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4387) (Sat.Literal.pos 4386) (Sat.Literal.pos 36) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation10 36 (assignment s)
    (Sat.Literal.pos 4387) (Sat.Literal.pos 4386) (Sat.Literal.pos 36) (Sat.Literal.pos 66) (positive_of_descriptor s 4387 (.lex permutation10 36) (by rfl)) (lex_10_36_prefix s) (positive_select s 36) (lex_10_36_image s)

theorem lex_10_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.pos 36), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation10 36 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4386) (Sat.Literal.pos 36) (Sat.Literal.pos 66) (lex_10_36_prefix s) (positive_select s 36) (lex_10_36_image s)

theorem lex_10_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.pos 4386)] :=
  (lex_10_36_gate s).prop _ (List.Mem.head _)

theorem lex_10_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.neg 36), (Sat.Literal.pos 66)] :=
  (lex_10_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.pos 36), (Sat.Literal.neg 66)] :=
  (lex_10_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.neg 36), (Sat.Literal.neg 66), (Sat.Literal.pos 4387)] :=
  (lex_10_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4386), (Sat.Literal.pos 36), (Sat.Literal.pos 66), (Sat.Literal.pos 4387)] :=
  (lex_10_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4387) = lexBefore s permutation10 35 := by
  exact (positive_lex_of_descriptor s 4387 permutation10 36 (by rfl)).trans ((lex_skipped s permutation10 35 36 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation10 35) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation10 35 by rw [image10_eq]; rfl))

theorem lex_10_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4388) (Sat.Literal.pos 4387) (Sat.Literal.pos 35) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation10 35 (assignment s)
    (Sat.Literal.pos 4388) (Sat.Literal.pos 4387) (Sat.Literal.pos 35) (Sat.Literal.pos 50) (positive_of_descriptor s 4388 (.lex permutation10 35) (by rfl)) (lex_10_35_prefix s) (positive_select s 35) (lex_10_35_image s)

theorem lex_10_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.pos 35), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation10 35 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4387) (Sat.Literal.pos 35) (Sat.Literal.pos 50) (lex_10_35_prefix s) (positive_select s 35) (lex_10_35_image s)

theorem lex_10_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.pos 4387)] :=
  (lex_10_35_gate s).prop _ (List.Mem.head _)

theorem lex_10_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.neg 35), (Sat.Literal.pos 50)] :=
  (lex_10_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.pos 35), (Sat.Literal.neg 50)] :=
  (lex_10_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.neg 35), (Sat.Literal.neg 50), (Sat.Literal.pos 4388)] :=
  (lex_10_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4387), (Sat.Literal.pos 35), (Sat.Literal.pos 50), (Sat.Literal.pos 4388)] :=
  (lex_10_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4388) = lexBefore s permutation10 33 := by
  exact (positive_lex_of_descriptor s 4388 permutation10 35 (by rfl)).trans ((lex_skipped s permutation10 33 35 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 34 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation10 33) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation10 33 by rw [image10_eq]; rfl))

theorem lex_10_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4389) (Sat.Literal.pos 4388) (Sat.Literal.pos 33) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation10 33 (assignment s)
    (Sat.Literal.pos 4389) (Sat.Literal.pos 4388) (Sat.Literal.pos 33) (Sat.Literal.pos 18) (positive_of_descriptor s 4389 (.lex permutation10 33) (by rfl)) (lex_10_33_prefix s) (positive_select s 33) (lex_10_33_image s)

theorem lex_10_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.pos 33), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation10 33 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4388) (Sat.Literal.pos 33) (Sat.Literal.pos 18) (lex_10_33_prefix s) (positive_select s 33) (lex_10_33_image s)

theorem lex_10_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.pos 4388)] :=
  (lex_10_33_gate s).prop _ (List.Mem.head _)

theorem lex_10_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.neg 33), (Sat.Literal.pos 18)] :=
  (lex_10_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.pos 33), (Sat.Literal.neg 18)] :=
  (lex_10_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.neg 33), (Sat.Literal.neg 18), (Sat.Literal.pos 4389)] :=
  (lex_10_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4388), (Sat.Literal.pos 33), (Sat.Literal.pos 18), (Sat.Literal.pos 4389)] :=
  (lex_10_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4389) = lexBefore s permutation10 32 := by
  exact (positive_lex_of_descriptor s 4389 permutation10 33 (by rfl)).trans ((lex_skipped s permutation10 32 33 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation10 32) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation10 32 by rw [image10_eq]; rfl))

theorem lex_10_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4390) (Sat.Literal.pos 4389) (Sat.Literal.pos 32) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation10 32 (assignment s)
    (Sat.Literal.pos 4390) (Sat.Literal.pos 4389) (Sat.Literal.pos 32) (Sat.Literal.pos 2) (positive_of_descriptor s 4390 (.lex permutation10 32) (by rfl)) (lex_10_32_prefix s) (positive_select s 32) (lex_10_32_image s)

theorem lex_10_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.pos 32), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation10 32 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4389) (Sat.Literal.pos 32) (Sat.Literal.pos 2) (lex_10_32_prefix s) (positive_select s 32) (lex_10_32_image s)

theorem lex_10_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.pos 4389)] :=
  (lex_10_32_gate s).prop _ (List.Mem.head _)

theorem lex_10_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.neg 32), (Sat.Literal.pos 2)] :=
  (lex_10_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.pos 32), (Sat.Literal.neg 2)] :=
  (lex_10_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.neg 32), (Sat.Literal.neg 2), (Sat.Literal.pos 4390)] :=
  (lex_10_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4389), (Sat.Literal.pos 32), (Sat.Literal.pos 2), (Sat.Literal.pos 4390)] :=
  (lex_10_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4390) = lexBefore s permutation10 31 := by
  exact (positive_lex_of_descriptor s 4390 permutation10 32 (by rfl)).trans ((lex_skipped s permutation10 31 32 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation10 31) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation10 31 by rw [image10_eq]; rfl))

theorem lex_10_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4391) (Sat.Literal.pos 4390) (Sat.Literal.pos 31) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation10 31 (assignment s)
    (Sat.Literal.pos 4391) (Sat.Literal.pos 4390) (Sat.Literal.pos 31) (Sat.Literal.pos 241) (positive_of_descriptor s 4391 (.lex permutation10 31) (by rfl)) (lex_10_31_prefix s) (positive_select s 31) (lex_10_31_image s)

theorem lex_10_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.pos 31), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation10 31 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4390) (Sat.Literal.pos 31) (Sat.Literal.pos 241) (lex_10_31_prefix s) (positive_select s 31) (lex_10_31_image s)

theorem lex_10_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.pos 4390)] :=
  (lex_10_31_gate s).prop _ (List.Mem.head _)

theorem lex_10_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.neg 31), (Sat.Literal.pos 241)] :=
  (lex_10_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.pos 31), (Sat.Literal.neg 241)] :=
  (lex_10_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.neg 31), (Sat.Literal.neg 241), (Sat.Literal.pos 4391)] :=
  (lex_10_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4390), (Sat.Literal.pos 31), (Sat.Literal.pos 241), (Sat.Literal.pos 4391)] :=
  (lex_10_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4391) = lexBefore s permutation10 30 := by
  exact (positive_lex_of_descriptor s 4391 permutation10 31 (by rfl)).trans ((lex_skipped s permutation10 30 31 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation10 30) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation10 30 by rw [image10_eq]; rfl))

theorem lex_10_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4392) (Sat.Literal.pos 4391) (Sat.Literal.pos 30) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation10 30 (assignment s)
    (Sat.Literal.pos 4392) (Sat.Literal.pos 4391) (Sat.Literal.pos 30) (Sat.Literal.pos 225) (positive_of_descriptor s 4392 (.lex permutation10 30) (by rfl)) (lex_10_30_prefix s) (positive_select s 30) (lex_10_30_image s)

theorem lex_10_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.pos 30), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation10 30 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4391) (Sat.Literal.pos 30) (Sat.Literal.pos 225) (lex_10_30_prefix s) (positive_select s 30) (lex_10_30_image s)

theorem lex_10_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.pos 4391)] :=
  (lex_10_30_gate s).prop _ (List.Mem.head _)

theorem lex_10_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.neg 30), (Sat.Literal.pos 225)] :=
  (lex_10_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.pos 30), (Sat.Literal.neg 225)] :=
  (lex_10_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.neg 30), (Sat.Literal.neg 225), (Sat.Literal.pos 4392)] :=
  (lex_10_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4391), (Sat.Literal.pos 30), (Sat.Literal.pos 225), (Sat.Literal.pos 4392)] :=
  (lex_10_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4392) = lexBefore s permutation10 29 := by
  exact (positive_lex_of_descriptor s 4392 permutation10 30 (by rfl)).trans ((lex_skipped s permutation10 29 30 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation10 29) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation10 29 by rw [image10_eq]; rfl))

theorem lex_10_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4393) (Sat.Literal.pos 4392) (Sat.Literal.pos 29) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation10 29 (assignment s)
    (Sat.Literal.pos 4393) (Sat.Literal.pos 4392) (Sat.Literal.pos 29) (Sat.Literal.pos 209) (positive_of_descriptor s 4393 (.lex permutation10 29) (by rfl)) (lex_10_29_prefix s) (positive_select s 29) (lex_10_29_image s)

theorem lex_10_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.pos 29), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation10 29 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4392) (Sat.Literal.pos 29) (Sat.Literal.pos 209) (lex_10_29_prefix s) (positive_select s 29) (lex_10_29_image s)

theorem lex_10_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.pos 4392)] :=
  (lex_10_29_gate s).prop _ (List.Mem.head _)

theorem lex_10_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.neg 29), (Sat.Literal.pos 209)] :=
  (lex_10_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.pos 29), (Sat.Literal.neg 209)] :=
  (lex_10_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.neg 29), (Sat.Literal.neg 209), (Sat.Literal.pos 4393)] :=
  (lex_10_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4392), (Sat.Literal.pos 29), (Sat.Literal.pos 209), (Sat.Literal.pos 4393)] :=
  (lex_10_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4393) = lexBefore s permutation10 28 := by
  exact (positive_lex_of_descriptor s 4393 permutation10 29 (by rfl)).trans ((lex_skipped s permutation10 28 29 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation10 28) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation10 28 by rw [image10_eq]; rfl))

theorem lex_10_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4394) (Sat.Literal.pos 4393) (Sat.Literal.pos 28) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation10 28 (assignment s)
    (Sat.Literal.pos 4394) (Sat.Literal.pos 4393) (Sat.Literal.pos 28) (Sat.Literal.pos 193) (positive_of_descriptor s 4394 (.lex permutation10 28) (by rfl)) (lex_10_28_prefix s) (positive_select s 28) (lex_10_28_image s)

theorem lex_10_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.pos 28), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation10 28 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4393) (Sat.Literal.pos 28) (Sat.Literal.pos 193) (lex_10_28_prefix s) (positive_select s 28) (lex_10_28_image s)

theorem lex_10_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.pos 4393)] :=
  (lex_10_28_gate s).prop _ (List.Mem.head _)

theorem lex_10_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.neg 28), (Sat.Literal.pos 193)] :=
  (lex_10_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.pos 28), (Sat.Literal.neg 193)] :=
  (lex_10_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.neg 28), (Sat.Literal.neg 193), (Sat.Literal.pos 4394)] :=
  (lex_10_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4393), (Sat.Literal.pos 28), (Sat.Literal.pos 193), (Sat.Literal.pos 4394)] :=
  (lex_10_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4394) = lexBefore s permutation10 27 := by
  exact (positive_lex_of_descriptor s 4394 permutation10 28 (by rfl)).trans ((lex_skipped s permutation10 27 28 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation10 27) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation10 27 by rw [image10_eq]; rfl))

theorem lex_10_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4395) (Sat.Literal.pos 4394) (Sat.Literal.pos 27) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation10 27 (assignment s)
    (Sat.Literal.pos 4395) (Sat.Literal.pos 4394) (Sat.Literal.pos 27) (Sat.Literal.pos 177) (positive_of_descriptor s 4395 (.lex permutation10 27) (by rfl)) (lex_10_27_prefix s) (positive_select s 27) (lex_10_27_image s)

theorem lex_10_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.pos 27), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation10 27 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4394) (Sat.Literal.pos 27) (Sat.Literal.pos 177) (lex_10_27_prefix s) (positive_select s 27) (lex_10_27_image s)

theorem lex_10_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.pos 4394)] :=
  (lex_10_27_gate s).prop _ (List.Mem.head _)

theorem lex_10_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.neg 27), (Sat.Literal.pos 177)] :=
  (lex_10_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.pos 27), (Sat.Literal.neg 177)] :=
  (lex_10_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.neg 27), (Sat.Literal.neg 177), (Sat.Literal.pos 4395)] :=
  (lex_10_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4394), (Sat.Literal.pos 27), (Sat.Literal.pos 177), (Sat.Literal.pos 4395)] :=
  (lex_10_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4395) = lexBefore s permutation10 26 := by
  exact (positive_lex_of_descriptor s 4395 permutation10 27 (by rfl)).trans ((lex_skipped s permutation10 26 27 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation10 26) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation10 26 by rw [image10_eq]; rfl))

theorem lex_10_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4396) (Sat.Literal.pos 4395) (Sat.Literal.pos 26) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation10 26 (assignment s)
    (Sat.Literal.pos 4396) (Sat.Literal.pos 4395) (Sat.Literal.pos 26) (Sat.Literal.pos 161) (positive_of_descriptor s 4396 (.lex permutation10 26) (by rfl)) (lex_10_26_prefix s) (positive_select s 26) (lex_10_26_image s)

theorem lex_10_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.pos 26), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation10 26 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4395) (Sat.Literal.pos 26) (Sat.Literal.pos 161) (lex_10_26_prefix s) (positive_select s 26) (lex_10_26_image s)

theorem lex_10_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.pos 4395)] :=
  (lex_10_26_gate s).prop _ (List.Mem.head _)

theorem lex_10_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.neg 26), (Sat.Literal.pos 161)] :=
  (lex_10_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.pos 26), (Sat.Literal.neg 161)] :=
  (lex_10_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.neg 26), (Sat.Literal.neg 161), (Sat.Literal.pos 4396)] :=
  (lex_10_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4395), (Sat.Literal.pos 26), (Sat.Literal.pos 161), (Sat.Literal.pos 4396)] :=
  (lex_10_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4396) = lexBefore s permutation10 25 := by
  exact (positive_lex_of_descriptor s 4396 permutation10 26 (by rfl)).trans ((lex_skipped s permutation10 25 26 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation10 25) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation10 25 by rw [image10_eq]; rfl))

theorem lex_10_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4397) (Sat.Literal.pos 4396) (Sat.Literal.pos 25) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation10 25 (assignment s)
    (Sat.Literal.pos 4397) (Sat.Literal.pos 4396) (Sat.Literal.pos 25) (Sat.Literal.pos 145) (positive_of_descriptor s 4397 (.lex permutation10 25) (by rfl)) (lex_10_25_prefix s) (positive_select s 25) (lex_10_25_image s)

theorem lex_10_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.pos 25), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation10 25 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4396) (Sat.Literal.pos 25) (Sat.Literal.pos 145) (lex_10_25_prefix s) (positive_select s 25) (lex_10_25_image s)

theorem lex_10_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.pos 4396)] :=
  (lex_10_25_gate s).prop _ (List.Mem.head _)

theorem lex_10_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.neg 25), (Sat.Literal.pos 145)] :=
  (lex_10_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.pos 25), (Sat.Literal.neg 145)] :=
  (lex_10_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.neg 25), (Sat.Literal.neg 145), (Sat.Literal.pos 4397)] :=
  (lex_10_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4396), (Sat.Literal.pos 25), (Sat.Literal.pos 145), (Sat.Literal.pos 4397)] :=
  (lex_10_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4397) = lexBefore s permutation10 24 := by
  exact (positive_lex_of_descriptor s 4397 permutation10 25 (by rfl)).trans ((lex_skipped s permutation10 24 25 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation10 24) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation10 24 by rw [image10_eq]; rfl))

theorem lex_10_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4398) (Sat.Literal.pos 4397) (Sat.Literal.pos 24) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation10 24 (assignment s)
    (Sat.Literal.pos 4398) (Sat.Literal.pos 4397) (Sat.Literal.pos 24) (Sat.Literal.pos 129) (positive_of_descriptor s 4398 (.lex permutation10 24) (by rfl)) (lex_10_24_prefix s) (positive_select s 24) (lex_10_24_image s)

theorem lex_10_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.pos 24), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation10 24 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4397) (Sat.Literal.pos 24) (Sat.Literal.pos 129) (lex_10_24_prefix s) (positive_select s 24) (lex_10_24_image s)

theorem lex_10_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.pos 4397)] :=
  (lex_10_24_gate s).prop _ (List.Mem.head _)

theorem lex_10_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.neg 24), (Sat.Literal.pos 129)] :=
  (lex_10_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.pos 24), (Sat.Literal.neg 129)] :=
  (lex_10_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.neg 24), (Sat.Literal.neg 129), (Sat.Literal.pos 4398)] :=
  (lex_10_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4397), (Sat.Literal.pos 24), (Sat.Literal.pos 129), (Sat.Literal.pos 4398)] :=
  (lex_10_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4398) = lexBefore s permutation10 23 := by
  exact (positive_lex_of_descriptor s 4398 permutation10 24 (by rfl)).trans ((lex_skipped s permutation10 23 24 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation10 23) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation10 23 by rw [image10_eq]; rfl))

theorem lex_10_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4399) (Sat.Literal.pos 4398) (Sat.Literal.pos 23) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation10 23 (assignment s)
    (Sat.Literal.pos 4399) (Sat.Literal.pos 4398) (Sat.Literal.pos 23) (Sat.Literal.pos 113) (positive_of_descriptor s 4399 (.lex permutation10 23) (by rfl)) (lex_10_23_prefix s) (positive_select s 23) (lex_10_23_image s)

theorem lex_10_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.pos 23), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation10 23 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4398) (Sat.Literal.pos 23) (Sat.Literal.pos 113) (lex_10_23_prefix s) (positive_select s 23) (lex_10_23_image s)

theorem lex_10_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.pos 4398)] :=
  (lex_10_23_gate s).prop _ (List.Mem.head _)

theorem lex_10_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.neg 23), (Sat.Literal.pos 113)] :=
  (lex_10_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.pos 23), (Sat.Literal.neg 113)] :=
  (lex_10_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.neg 23), (Sat.Literal.neg 113), (Sat.Literal.pos 4399)] :=
  (lex_10_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4398), (Sat.Literal.pos 23), (Sat.Literal.pos 113), (Sat.Literal.pos 4399)] :=
  (lex_10_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4399) = lexBefore s permutation10 22 := by
  exact (positive_lex_of_descriptor s 4399 permutation10 23 (by rfl)).trans ((lex_skipped s permutation10 22 23 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation10 22) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation10 22 by rw [image10_eq]; rfl))

theorem lex_10_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4400) (Sat.Literal.pos 4399) (Sat.Literal.pos 22) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation10 22 (assignment s)
    (Sat.Literal.pos 4400) (Sat.Literal.pos 4399) (Sat.Literal.pos 22) (Sat.Literal.pos 97) (positive_of_descriptor s 4400 (.lex permutation10 22) (by rfl)) (lex_10_22_prefix s) (positive_select s 22) (lex_10_22_image s)

theorem lex_10_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.pos 22), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation10 22 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4399) (Sat.Literal.pos 22) (Sat.Literal.pos 97) (lex_10_22_prefix s) (positive_select s 22) (lex_10_22_image s)

theorem lex_10_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.pos 4399)] :=
  (lex_10_22_gate s).prop _ (List.Mem.head _)

theorem lex_10_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.neg 22), (Sat.Literal.pos 97)] :=
  (lex_10_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.pos 22), (Sat.Literal.neg 97)] :=
  (lex_10_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.neg 22), (Sat.Literal.neg 97), (Sat.Literal.pos 4400)] :=
  (lex_10_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4399), (Sat.Literal.pos 22), (Sat.Literal.pos 97), (Sat.Literal.pos 4400)] :=
  (lex_10_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4400) = lexBefore s permutation10 21 := by
  exact (positive_lex_of_descriptor s 4400 permutation10 22 (by rfl)).trans ((lex_skipped s permutation10 21 22 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation10 21) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation10 21 by rw [image10_eq]; rfl))

theorem lex_10_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4401) (Sat.Literal.pos 4400) (Sat.Literal.pos 21) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation10 21 (assignment s)
    (Sat.Literal.pos 4401) (Sat.Literal.pos 4400) (Sat.Literal.pos 21) (Sat.Literal.pos 81) (positive_of_descriptor s 4401 (.lex permutation10 21) (by rfl)) (lex_10_21_prefix s) (positive_select s 21) (lex_10_21_image s)

theorem lex_10_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.pos 21), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation10 21 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4400) (Sat.Literal.pos 21) (Sat.Literal.pos 81) (lex_10_21_prefix s) (positive_select s 21) (lex_10_21_image s)

theorem lex_10_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.pos 4400)] :=
  (lex_10_21_gate s).prop _ (List.Mem.head _)

theorem lex_10_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.neg 21), (Sat.Literal.pos 81)] :=
  (lex_10_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.pos 21), (Sat.Literal.neg 81)] :=
  (lex_10_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.neg 21), (Sat.Literal.neg 81), (Sat.Literal.pos 4401)] :=
  (lex_10_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4400), (Sat.Literal.pos 21), (Sat.Literal.pos 81), (Sat.Literal.pos 4401)] :=
  (lex_10_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4401) = lexBefore s permutation10 20 := by
  exact (positive_lex_of_descriptor s 4401 permutation10 21 (by rfl)).trans ((lex_skipped s permutation10 20 21 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation10 20) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation10 20 by rw [image10_eq]; rfl))

theorem lex_10_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4402) (Sat.Literal.pos 4401) (Sat.Literal.pos 20) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation10 20 (assignment s)
    (Sat.Literal.pos 4402) (Sat.Literal.pos 4401) (Sat.Literal.pos 20) (Sat.Literal.pos 65) (positive_of_descriptor s 4402 (.lex permutation10 20) (by rfl)) (lex_10_20_prefix s) (positive_select s 20) (lex_10_20_image s)

theorem lex_10_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.pos 20), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation10 20 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4401) (Sat.Literal.pos 20) (Sat.Literal.pos 65) (lex_10_20_prefix s) (positive_select s 20) (lex_10_20_image s)

theorem lex_10_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.pos 4401)] :=
  (lex_10_20_gate s).prop _ (List.Mem.head _)

theorem lex_10_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.neg 20), (Sat.Literal.pos 65)] :=
  (lex_10_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.pos 20), (Sat.Literal.neg 65)] :=
  (lex_10_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.neg 20), (Sat.Literal.neg 65), (Sat.Literal.pos 4402)] :=
  (lex_10_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4401), (Sat.Literal.pos 20), (Sat.Literal.pos 65), (Sat.Literal.pos 4402)] :=
  (lex_10_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4402) = lexBefore s permutation10 19 := by
  exact (positive_lex_of_descriptor s 4402 permutation10 20 (by rfl)).trans ((lex_skipped s permutation10 19 20 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation10 19) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation10 19 by rw [image10_eq]; rfl))

theorem lex_10_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4403) (Sat.Literal.pos 4402) (Sat.Literal.pos 19) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation10 19 (assignment s)
    (Sat.Literal.pos 4403) (Sat.Literal.pos 4402) (Sat.Literal.pos 19) (Sat.Literal.pos 49) (positive_of_descriptor s 4403 (.lex permutation10 19) (by rfl)) (lex_10_19_prefix s) (positive_select s 19) (lex_10_19_image s)

theorem lex_10_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.pos 19), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation10 19 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4402) (Sat.Literal.pos 19) (Sat.Literal.pos 49) (lex_10_19_prefix s) (positive_select s 19) (lex_10_19_image s)

theorem lex_10_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.pos 4402)] :=
  (lex_10_19_gate s).prop _ (List.Mem.head _)

theorem lex_10_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.neg 19), (Sat.Literal.pos 49)] :=
  (lex_10_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.pos 19), (Sat.Literal.neg 49)] :=
  (lex_10_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.neg 19), (Sat.Literal.neg 49), (Sat.Literal.pos 4403)] :=
  (lex_10_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4402), (Sat.Literal.pos 19), (Sat.Literal.pos 49), (Sat.Literal.pos 4403)] :=
  (lex_10_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4403) = lexBefore s permutation10 18 := by
  exact (positive_lex_of_descriptor s 4403 permutation10 19 (by rfl)).trans ((lex_skipped s permutation10 18 19 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation10 18) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation10 18 by rw [image10_eq]; rfl))

theorem lex_10_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4404) (Sat.Literal.pos 4403) (Sat.Literal.pos 18) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation10 18 (assignment s)
    (Sat.Literal.pos 4404) (Sat.Literal.pos 4403) (Sat.Literal.pos 18) (Sat.Literal.pos 33) (positive_of_descriptor s 4404 (.lex permutation10 18) (by rfl)) (lex_10_18_prefix s) (positive_select s 18) (lex_10_18_image s)

theorem lex_10_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.pos 18), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation10 18 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4403) (Sat.Literal.pos 18) (Sat.Literal.pos 33) (lex_10_18_prefix s) (positive_select s 18) (lex_10_18_image s)

theorem lex_10_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.pos 4403)] :=
  (lex_10_18_gate s).prop _ (List.Mem.head _)

theorem lex_10_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.neg 18), (Sat.Literal.pos 33)] :=
  (lex_10_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.pos 18), (Sat.Literal.neg 33)] :=
  (lex_10_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.neg 18), (Sat.Literal.neg 33), (Sat.Literal.pos 4404)] :=
  (lex_10_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4403), (Sat.Literal.pos 18), (Sat.Literal.pos 33), (Sat.Literal.pos 4404)] :=
  (lex_10_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4404) = lexBefore s permutation10 16 := by
  exact (positive_lex_of_descriptor s 4404 permutation10 18 (by rfl)).trans ((lex_skipped s permutation10 16 18 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 17 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation10 16) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation10 16 by rw [image10_eq]; rfl))

theorem lex_10_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4405) (Sat.Literal.pos 4404) (Sat.Literal.pos 16) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation10 16 (assignment s)
    (Sat.Literal.pos 4405) (Sat.Literal.pos 4404) (Sat.Literal.pos 16) (Sat.Literal.pos 1) (positive_of_descriptor s 4405 (.lex permutation10 16) (by rfl)) (lex_10_16_prefix s) (positive_select s 16) (lex_10_16_image s)

theorem lex_10_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.pos 16), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation10 16 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4404) (Sat.Literal.pos 16) (Sat.Literal.pos 1) (lex_10_16_prefix s) (positive_select s 16) (lex_10_16_image s)

theorem lex_10_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.pos 4404)] :=
  (lex_10_16_gate s).prop _ (List.Mem.head _)

theorem lex_10_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.neg 16), (Sat.Literal.pos 1)] :=
  (lex_10_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.pos 16), (Sat.Literal.neg 1)] :=
  (lex_10_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.neg 16), (Sat.Literal.neg 1), (Sat.Literal.pos 4405)] :=
  (lex_10_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4404), (Sat.Literal.pos 16), (Sat.Literal.pos 1), (Sat.Literal.pos 4405)] :=
  (lex_10_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4405) = lexBefore s permutation10 15 := by
  exact (positive_lex_of_descriptor s 4405 permutation10 16 (by rfl)).trans ((lex_skipped s permutation10 15 16 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation10 15) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation10 15 by rw [image10_eq]; rfl))

theorem lex_10_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4406) (Sat.Literal.pos 4405) (Sat.Literal.pos 15) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation10 15 (assignment s)
    (Sat.Literal.pos 4406) (Sat.Literal.pos 4405) (Sat.Literal.pos 15) (Sat.Literal.pos 240) (positive_of_descriptor s 4406 (.lex permutation10 15) (by rfl)) (lex_10_15_prefix s) (positive_select s 15) (lex_10_15_image s)

theorem lex_10_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.pos 15), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation10 15 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4405) (Sat.Literal.pos 15) (Sat.Literal.pos 240) (lex_10_15_prefix s) (positive_select s 15) (lex_10_15_image s)

theorem lex_10_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.pos 4405)] :=
  (lex_10_15_gate s).prop _ (List.Mem.head _)

theorem lex_10_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.neg 15), (Sat.Literal.pos 240)] :=
  (lex_10_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.pos 15), (Sat.Literal.neg 240)] :=
  (lex_10_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.neg 15), (Sat.Literal.neg 240), (Sat.Literal.pos 4406)] :=
  (lex_10_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4405), (Sat.Literal.pos 15), (Sat.Literal.pos 240), (Sat.Literal.pos 4406)] :=
  (lex_10_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4406) = lexBefore s permutation10 14 := by
  exact (positive_lex_of_descriptor s 4406 permutation10 15 (by rfl)).trans ((lex_skipped s permutation10 14 15 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation10 14) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation10 14 by rw [image10_eq]; rfl))

theorem lex_10_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4407) (Sat.Literal.pos 4406) (Sat.Literal.pos 14) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation10 14 (assignment s)
    (Sat.Literal.pos 4407) (Sat.Literal.pos 4406) (Sat.Literal.pos 14) (Sat.Literal.pos 224) (positive_of_descriptor s 4407 (.lex permutation10 14) (by rfl)) (lex_10_14_prefix s) (positive_select s 14) (lex_10_14_image s)

theorem lex_10_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.pos 14), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation10 14 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4406) (Sat.Literal.pos 14) (Sat.Literal.pos 224) (lex_10_14_prefix s) (positive_select s 14) (lex_10_14_image s)

theorem lex_10_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.pos 4406)] :=
  (lex_10_14_gate s).prop _ (List.Mem.head _)

theorem lex_10_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.neg 14), (Sat.Literal.pos 224)] :=
  (lex_10_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.pos 14), (Sat.Literal.neg 224)] :=
  (lex_10_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.neg 14), (Sat.Literal.neg 224), (Sat.Literal.pos 4407)] :=
  (lex_10_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4406), (Sat.Literal.pos 14), (Sat.Literal.pos 224), (Sat.Literal.pos 4407)] :=
  (lex_10_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4407) = lexBefore s permutation10 13 := by
  exact (positive_lex_of_descriptor s 4407 permutation10 14 (by rfl)).trans ((lex_skipped s permutation10 13 14 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation10 13) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation10 13 by rw [image10_eq]; rfl))

theorem lex_10_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4408) (Sat.Literal.pos 4407) (Sat.Literal.pos 13) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation10 13 (assignment s)
    (Sat.Literal.pos 4408) (Sat.Literal.pos 4407) (Sat.Literal.pos 13) (Sat.Literal.pos 208) (positive_of_descriptor s 4408 (.lex permutation10 13) (by rfl)) (lex_10_13_prefix s) (positive_select s 13) (lex_10_13_image s)

theorem lex_10_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.pos 13), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation10 13 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4407) (Sat.Literal.pos 13) (Sat.Literal.pos 208) (lex_10_13_prefix s) (positive_select s 13) (lex_10_13_image s)

theorem lex_10_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.pos 4407)] :=
  (lex_10_13_gate s).prop _ (List.Mem.head _)

theorem lex_10_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.neg 13), (Sat.Literal.pos 208)] :=
  (lex_10_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.pos 13), (Sat.Literal.neg 208)] :=
  (lex_10_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.neg 13), (Sat.Literal.neg 208), (Sat.Literal.pos 4408)] :=
  (lex_10_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4407), (Sat.Literal.pos 13), (Sat.Literal.pos 208), (Sat.Literal.pos 4408)] :=
  (lex_10_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4408) = lexBefore s permutation10 12 := by
  exact (positive_lex_of_descriptor s 4408 permutation10 13 (by rfl)).trans ((lex_skipped s permutation10 12 13 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation10 12) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation10 12 by rw [image10_eq]; rfl))

theorem lex_10_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4409) (Sat.Literal.pos 4408) (Sat.Literal.pos 12) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation10 12 (assignment s)
    (Sat.Literal.pos 4409) (Sat.Literal.pos 4408) (Sat.Literal.pos 12) (Sat.Literal.pos 192) (positive_of_descriptor s 4409 (.lex permutation10 12) (by rfl)) (lex_10_12_prefix s) (positive_select s 12) (lex_10_12_image s)

theorem lex_10_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.pos 12), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation10 12 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4408) (Sat.Literal.pos 12) (Sat.Literal.pos 192) (lex_10_12_prefix s) (positive_select s 12) (lex_10_12_image s)

theorem lex_10_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.pos 4408)] :=
  (lex_10_12_gate s).prop _ (List.Mem.head _)

theorem lex_10_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.neg 12), (Sat.Literal.pos 192)] :=
  (lex_10_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.pos 12), (Sat.Literal.neg 192)] :=
  (lex_10_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.neg 12), (Sat.Literal.neg 192), (Sat.Literal.pos 4409)] :=
  (lex_10_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4408), (Sat.Literal.pos 12), (Sat.Literal.pos 192), (Sat.Literal.pos 4409)] :=
  (lex_10_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4409) = lexBefore s permutation10 11 := by
  exact (positive_lex_of_descriptor s 4409 permutation10 12 (by rfl)).trans ((lex_skipped s permutation10 11 12 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation10 11) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation10 11 by rw [image10_eq]; rfl))

theorem lex_10_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4410) (Sat.Literal.pos 4409) (Sat.Literal.pos 11) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation10 11 (assignment s)
    (Sat.Literal.pos 4410) (Sat.Literal.pos 4409) (Sat.Literal.pos 11) (Sat.Literal.pos 176) (positive_of_descriptor s 4410 (.lex permutation10 11) (by rfl)) (lex_10_11_prefix s) (positive_select s 11) (lex_10_11_image s)

theorem lex_10_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.pos 11), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation10 11 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4409) (Sat.Literal.pos 11) (Sat.Literal.pos 176) (lex_10_11_prefix s) (positive_select s 11) (lex_10_11_image s)

theorem lex_10_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.pos 4409)] :=
  (lex_10_11_gate s).prop _ (List.Mem.head _)

theorem lex_10_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.neg 11), (Sat.Literal.pos 176)] :=
  (lex_10_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.pos 11), (Sat.Literal.neg 176)] :=
  (lex_10_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.neg 11), (Sat.Literal.neg 176), (Sat.Literal.pos 4410)] :=
  (lex_10_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4409), (Sat.Literal.pos 11), (Sat.Literal.pos 176), (Sat.Literal.pos 4410)] :=
  (lex_10_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4410) = lexBefore s permutation10 10 := by
  exact (positive_lex_of_descriptor s 4410 permutation10 11 (by rfl)).trans ((lex_skipped s permutation10 10 11 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation10 10) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation10 10 by rw [image10_eq]; rfl))

theorem lex_10_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4411) (Sat.Literal.pos 4410) (Sat.Literal.pos 10) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation10 10 (assignment s)
    (Sat.Literal.pos 4411) (Sat.Literal.pos 4410) (Sat.Literal.pos 10) (Sat.Literal.pos 160) (positive_of_descriptor s 4411 (.lex permutation10 10) (by rfl)) (lex_10_10_prefix s) (positive_select s 10) (lex_10_10_image s)

theorem lex_10_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.pos 10), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation10 10 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4410) (Sat.Literal.pos 10) (Sat.Literal.pos 160) (lex_10_10_prefix s) (positive_select s 10) (lex_10_10_image s)

theorem lex_10_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.pos 4410)] :=
  (lex_10_10_gate s).prop _ (List.Mem.head _)

theorem lex_10_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.neg 10), (Sat.Literal.pos 160)] :=
  (lex_10_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.pos 10), (Sat.Literal.neg 160)] :=
  (lex_10_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.neg 10), (Sat.Literal.neg 160), (Sat.Literal.pos 4411)] :=
  (lex_10_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4410), (Sat.Literal.pos 10), (Sat.Literal.pos 160), (Sat.Literal.pos 4411)] :=
  (lex_10_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4411) = lexBefore s permutation10 9 := by
  exact (positive_lex_of_descriptor s 4411 permutation10 10 (by rfl)).trans ((lex_skipped s permutation10 9 10 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation10 9) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation10 9 by rw [image10_eq]; rfl))

theorem lex_10_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4412) (Sat.Literal.pos 4411) (Sat.Literal.pos 9) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation10 9 (assignment s)
    (Sat.Literal.pos 4412) (Sat.Literal.pos 4411) (Sat.Literal.pos 9) (Sat.Literal.pos 144) (positive_of_descriptor s 4412 (.lex permutation10 9) (by rfl)) (lex_10_9_prefix s) (positive_select s 9) (lex_10_9_image s)

theorem lex_10_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.pos 9), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation10 9 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4411) (Sat.Literal.pos 9) (Sat.Literal.pos 144) (lex_10_9_prefix s) (positive_select s 9) (lex_10_9_image s)

theorem lex_10_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.pos 4411)] :=
  (lex_10_9_gate s).prop _ (List.Mem.head _)

theorem lex_10_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.neg 9), (Sat.Literal.pos 144)] :=
  (lex_10_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.pos 9), (Sat.Literal.neg 144)] :=
  (lex_10_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.neg 9), (Sat.Literal.neg 144), (Sat.Literal.pos 4412)] :=
  (lex_10_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4411), (Sat.Literal.pos 9), (Sat.Literal.pos 144), (Sat.Literal.pos 4412)] :=
  (lex_10_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4412) = lexBefore s permutation10 8 := by
  exact (positive_lex_of_descriptor s 4412 permutation10 9 (by rfl)).trans ((lex_skipped s permutation10 8 9 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation10 8) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation10 8 by rw [image10_eq]; rfl))

theorem lex_10_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4413) (Sat.Literal.pos 4412) (Sat.Literal.pos 8) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation10 8 (assignment s)
    (Sat.Literal.pos 4413) (Sat.Literal.pos 4412) (Sat.Literal.pos 8) (Sat.Literal.pos 128) (positive_of_descriptor s 4413 (.lex permutation10 8) (by rfl)) (lex_10_8_prefix s) (positive_select s 8) (lex_10_8_image s)

theorem lex_10_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.pos 8), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation10 8 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4412) (Sat.Literal.pos 8) (Sat.Literal.pos 128) (lex_10_8_prefix s) (positive_select s 8) (lex_10_8_image s)

theorem lex_10_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.pos 4412)] :=
  (lex_10_8_gate s).prop _ (List.Mem.head _)

theorem lex_10_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.neg 8), (Sat.Literal.pos 128)] :=
  (lex_10_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.pos 8), (Sat.Literal.neg 128)] :=
  (lex_10_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.neg 8), (Sat.Literal.neg 128), (Sat.Literal.pos 4413)] :=
  (lex_10_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4412), (Sat.Literal.pos 8), (Sat.Literal.pos 128), (Sat.Literal.pos 4413)] :=
  (lex_10_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4413) = lexBefore s permutation10 7 := by
  exact (positive_lex_of_descriptor s 4413 permutation10 8 (by rfl)).trans ((lex_skipped s permutation10 7 8 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation10 7) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation10 7 by rw [image10_eq]; rfl))

theorem lex_10_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4414) (Sat.Literal.pos 4413) (Sat.Literal.pos 7) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation10 7 (assignment s)
    (Sat.Literal.pos 4414) (Sat.Literal.pos 4413) (Sat.Literal.pos 7) (Sat.Literal.pos 112) (positive_of_descriptor s 4414 (.lex permutation10 7) (by rfl)) (lex_10_7_prefix s) (positive_select s 7) (lex_10_7_image s)

theorem lex_10_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.pos 7), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation10 7 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4413) (Sat.Literal.pos 7) (Sat.Literal.pos 112) (lex_10_7_prefix s) (positive_select s 7) (lex_10_7_image s)

theorem lex_10_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.pos 4413)] :=
  (lex_10_7_gate s).prop _ (List.Mem.head _)

theorem lex_10_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.neg 7), (Sat.Literal.pos 112)] :=
  (lex_10_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.pos 7), (Sat.Literal.neg 112)] :=
  (lex_10_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.neg 7), (Sat.Literal.neg 112), (Sat.Literal.pos 4414)] :=
  (lex_10_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4413), (Sat.Literal.pos 7), (Sat.Literal.pos 112), (Sat.Literal.pos 4414)] :=
  (lex_10_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4414) = lexBefore s permutation10 6 := by
  exact (positive_lex_of_descriptor s 4414 permutation10 7 (by rfl)).trans ((lex_skipped s permutation10 6 7 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation10 6) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation10 6 by rw [image10_eq]; rfl))

theorem lex_10_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4415) (Sat.Literal.pos 4414) (Sat.Literal.pos 6) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation10 6 (assignment s)
    (Sat.Literal.pos 4415) (Sat.Literal.pos 4414) (Sat.Literal.pos 6) (Sat.Literal.pos 96) (positive_of_descriptor s 4415 (.lex permutation10 6) (by rfl)) (lex_10_6_prefix s) (positive_select s 6) (lex_10_6_image s)

theorem lex_10_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.pos 6), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation10 6 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4414) (Sat.Literal.pos 6) (Sat.Literal.pos 96) (lex_10_6_prefix s) (positive_select s 6) (lex_10_6_image s)

theorem lex_10_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.pos 4414)] :=
  (lex_10_6_gate s).prop _ (List.Mem.head _)

theorem lex_10_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.neg 6), (Sat.Literal.pos 96)] :=
  (lex_10_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.pos 6), (Sat.Literal.neg 96)] :=
  (lex_10_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.neg 6), (Sat.Literal.neg 96), (Sat.Literal.pos 4415)] :=
  (lex_10_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4414), (Sat.Literal.pos 6), (Sat.Literal.pos 96), (Sat.Literal.pos 4415)] :=
  (lex_10_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4415) = lexBefore s permutation10 5 := by
  exact (positive_lex_of_descriptor s 4415 permutation10 6 (by rfl)).trans ((lex_skipped s permutation10 5 6 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation10 5) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation10 5 by rw [image10_eq]; rfl))

theorem lex_10_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4416) (Sat.Literal.pos 4415) (Sat.Literal.pos 5) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation10 5 (assignment s)
    (Sat.Literal.pos 4416) (Sat.Literal.pos 4415) (Sat.Literal.pos 5) (Sat.Literal.pos 80) (positive_of_descriptor s 4416 (.lex permutation10 5) (by rfl)) (lex_10_5_prefix s) (positive_select s 5) (lex_10_5_image s)

theorem lex_10_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.pos 5), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation10 5 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4415) (Sat.Literal.pos 5) (Sat.Literal.pos 80) (lex_10_5_prefix s) (positive_select s 5) (lex_10_5_image s)

theorem lex_10_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.pos 4415)] :=
  (lex_10_5_gate s).prop _ (List.Mem.head _)

theorem lex_10_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.neg 5), (Sat.Literal.pos 80)] :=
  (lex_10_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.pos 5), (Sat.Literal.neg 80)] :=
  (lex_10_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.neg 5), (Sat.Literal.neg 80), (Sat.Literal.pos 4416)] :=
  (lex_10_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4415), (Sat.Literal.pos 5), (Sat.Literal.pos 80), (Sat.Literal.pos 4416)] :=
  (lex_10_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4416) = lexBefore s permutation10 4 := by
  exact (positive_lex_of_descriptor s 4416 permutation10 5 (by rfl)).trans ((lex_skipped s permutation10 4 5 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation10 4) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation10 4 by rw [image10_eq]; rfl))

theorem lex_10_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4417) (Sat.Literal.pos 4416) (Sat.Literal.pos 4) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation10 4 (assignment s)
    (Sat.Literal.pos 4417) (Sat.Literal.pos 4416) (Sat.Literal.pos 4) (Sat.Literal.pos 64) (positive_of_descriptor s 4417 (.lex permutation10 4) (by rfl)) (lex_10_4_prefix s) (positive_select s 4) (lex_10_4_image s)

theorem lex_10_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.pos 4), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation10 4 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4416) (Sat.Literal.pos 4) (Sat.Literal.pos 64) (lex_10_4_prefix s) (positive_select s 4) (lex_10_4_image s)

theorem lex_10_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.pos 4416)] :=
  (lex_10_4_gate s).prop _ (List.Mem.head _)

theorem lex_10_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.neg 4), (Sat.Literal.pos 64)] :=
  (lex_10_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.pos 4), (Sat.Literal.neg 64)] :=
  (lex_10_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.neg 4), (Sat.Literal.neg 64), (Sat.Literal.pos 4417)] :=
  (lex_10_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4416), (Sat.Literal.pos 4), (Sat.Literal.pos 64), (Sat.Literal.pos 4417)] :=
  (lex_10_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4417) = lexBefore s permutation10 3 := by
  exact (positive_lex_of_descriptor s 4417 permutation10 4 (by rfl)).trans ((lex_skipped s permutation10 3 4 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation10 3) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation10 3 by rw [image10_eq]; rfl))

theorem lex_10_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4418) (Sat.Literal.pos 4417) (Sat.Literal.pos 3) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation10 3 (assignment s)
    (Sat.Literal.pos 4418) (Sat.Literal.pos 4417) (Sat.Literal.pos 3) (Sat.Literal.pos 48) (positive_of_descriptor s 4418 (.lex permutation10 3) (by rfl)) (lex_10_3_prefix s) (positive_select s 3) (lex_10_3_image s)

theorem lex_10_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.pos 3), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation10 3 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4417) (Sat.Literal.pos 3) (Sat.Literal.pos 48) (lex_10_3_prefix s) (positive_select s 3) (lex_10_3_image s)

theorem lex_10_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.pos 4417)] :=
  (lex_10_3_gate s).prop _ (List.Mem.head _)

theorem lex_10_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.neg 3), (Sat.Literal.pos 48)] :=
  (lex_10_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.pos 3), (Sat.Literal.neg 48)] :=
  (lex_10_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.neg 3), (Sat.Literal.neg 48), (Sat.Literal.pos 4418)] :=
  (lex_10_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4417), (Sat.Literal.pos 3), (Sat.Literal.pos 48), (Sat.Literal.pos 4418)] :=
  (lex_10_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4418) = lexBefore s permutation10 2 := by
  exact (positive_lex_of_descriptor s 4418 permutation10 3 (by rfl)).trans ((lex_skipped s permutation10 2 3 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation10 2) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation10 2 by rw [image10_eq]; rfl))

theorem lex_10_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4419) (Sat.Literal.pos 4418) (Sat.Literal.pos 2) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation10 2 (assignment s)
    (Sat.Literal.pos 4419) (Sat.Literal.pos 4418) (Sat.Literal.pos 2) (Sat.Literal.pos 32) (positive_of_descriptor s 4419 (.lex permutation10 2) (by rfl)) (lex_10_2_prefix s) (positive_select s 2) (lex_10_2_image s)

theorem lex_10_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.pos 2), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation10 2 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4418) (Sat.Literal.pos 2) (Sat.Literal.pos 32) (lex_10_2_prefix s) (positive_select s 2) (lex_10_2_image s)

theorem lex_10_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.pos 4418)] :=
  (lex_10_2_gate s).prop _ (List.Mem.head _)

theorem lex_10_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.neg 2), (Sat.Literal.pos 32)] :=
  (lex_10_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.pos 2), (Sat.Literal.neg 32)] :=
  (lex_10_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.neg 2), (Sat.Literal.neg 32), (Sat.Literal.pos 4419)] :=
  (lex_10_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4418), (Sat.Literal.pos 2), (Sat.Literal.pos 32), (Sat.Literal.pos 4419)] :=
  (lex_10_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4419) = lexBefore s permutation10 1 := by
  exact (positive_lex_of_descriptor s 4419 permutation10 2 (by rfl)).trans ((lex_skipped s permutation10 1 2 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation10 1) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation10 1 by rw [image10_eq]; rfl))

theorem lex_10_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4420) (Sat.Literal.pos 4419) (Sat.Literal.pos 1) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation10 1 (assignment s)
    (Sat.Literal.pos 4420) (Sat.Literal.pos 4419) (Sat.Literal.pos 1) (Sat.Literal.pos 16) (positive_of_descriptor s 4420 (.lex permutation10 1) (by rfl)) (lex_10_1_prefix s) (positive_select s 1) (lex_10_1_image s)

theorem lex_10_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.pos 1), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation10 1 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4419) (Sat.Literal.pos 1) (Sat.Literal.pos 16) (lex_10_1_prefix s) (positive_select s 1) (lex_10_1_image s)

theorem lex_10_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4420), (Sat.Literal.pos 4419)] :=
  (lex_10_1_gate s).prop _ (List.Mem.head _)

theorem lex_10_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4420), (Sat.Literal.neg 1), (Sat.Literal.pos 16)] :=
  (lex_10_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4420), (Sat.Literal.pos 1), (Sat.Literal.neg 16)] :=
  (lex_10_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.neg 1), (Sat.Literal.neg 16), (Sat.Literal.pos 4420)] :=
  (lex_10_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4419), (Sat.Literal.pos 1), (Sat.Literal.pos 16), (Sat.Literal.pos 4420)] :=
  (lex_10_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation11 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation11 254 (by intro j hj; rw [image11_eq]; exact fixedOnRange_spec image11 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_11_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation11 254) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation11 254 by rw [image11_eq]; rfl))

theorem lex_11_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4421) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation11 254 (assignment s)
    (Sat.Literal.pos 4421) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 223) (positive_of_descriptor s 4421 (.lex permutation11 254) (by rfl)) (lex_11_254_prefix s) (positive_select s 254) (lex_11_254_image s)

theorem lex_11_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation11 254 (hmax permutation11) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 223) (lex_11_254_prefix s) (positive_select s 254) (lex_11_254_image s)

theorem lex_11_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.neg 256)] :=
  (lex_11_254_gate s).prop _ (List.Mem.head _)

theorem lex_11_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.neg 254), (Sat.Literal.pos 223)] :=
  (lex_11_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.pos 254), (Sat.Literal.neg 223)] :=
  (lex_11_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 223), (Sat.Literal.pos 4421)] :=
  (lex_11_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 223), (Sat.Literal.pos 4421)] :=
  (lex_11_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4421) = lexBefore s permutation11 253 := by
  exact (positive_lex_of_descriptor s 4421 permutation11 254 (by rfl)).trans ((lex_skipped s permutation11 253 254 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation11 253) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation11 253 by rw [image11_eq]; rfl))

theorem lex_11_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4422) (Sat.Literal.pos 4421) (Sat.Literal.pos 253) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation11 253 (assignment s)
    (Sat.Literal.pos 4422) (Sat.Literal.pos 4421) (Sat.Literal.pos 253) (Sat.Literal.pos 191) (positive_of_descriptor s 4422 (.lex permutation11 253) (by rfl)) (lex_11_253_prefix s) (positive_select s 253) (lex_11_253_image s)

theorem lex_11_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.pos 253), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation11 253 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4421) (Sat.Literal.pos 253) (Sat.Literal.pos 191) (lex_11_253_prefix s) (positive_select s 253) (lex_11_253_image s)

theorem lex_11_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.pos 4421)] :=
  (lex_11_253_gate s).prop _ (List.Mem.head _)

theorem lex_11_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.neg 253), (Sat.Literal.pos 191)] :=
  (lex_11_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.pos 253), (Sat.Literal.neg 191)] :=
  (lex_11_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.neg 253), (Sat.Literal.neg 191), (Sat.Literal.pos 4422)] :=
  (lex_11_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4421), (Sat.Literal.pos 253), (Sat.Literal.pos 191), (Sat.Literal.pos 4422)] :=
  (lex_11_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4422) = lexBefore s permutation11 252 := by
  exact (positive_lex_of_descriptor s 4422 permutation11 253 (by rfl)).trans ((lex_skipped s permutation11 252 253 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation11 252) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation11 252 by rw [image11_eq]; rfl))

theorem lex_11_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4423) (Sat.Literal.pos 4422) (Sat.Literal.pos 252) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation11 252 (assignment s)
    (Sat.Literal.pos 4423) (Sat.Literal.pos 4422) (Sat.Literal.pos 252) (Sat.Literal.pos 159) (positive_of_descriptor s 4423 (.lex permutation11 252) (by rfl)) (lex_11_252_prefix s) (positive_select s 252) (lex_11_252_image s)

theorem lex_11_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.pos 252), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation11 252 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4422) (Sat.Literal.pos 252) (Sat.Literal.pos 159) (lex_11_252_prefix s) (positive_select s 252) (lex_11_252_image s)

theorem lex_11_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.pos 4422)] :=
  (lex_11_252_gate s).prop _ (List.Mem.head _)

theorem lex_11_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.neg 252), (Sat.Literal.pos 159)] :=
  (lex_11_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.pos 252), (Sat.Literal.neg 159)] :=
  (lex_11_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.neg 252), (Sat.Literal.neg 159), (Sat.Literal.pos 4423)] :=
  (lex_11_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4422), (Sat.Literal.pos 252), (Sat.Literal.pos 159), (Sat.Literal.pos 4423)] :=
  (lex_11_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4423) = lexBefore s permutation11 251 := by
  exact (positive_lex_of_descriptor s 4423 permutation11 252 (by rfl)).trans ((lex_skipped s permutation11 251 252 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation11 251) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation11 251 by rw [image11_eq]; rfl))

theorem lex_11_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4424) (Sat.Literal.pos 4423) (Sat.Literal.pos 251) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation11 251 (assignment s)
    (Sat.Literal.pos 4424) (Sat.Literal.pos 4423) (Sat.Literal.pos 251) (Sat.Literal.pos 127) (positive_of_descriptor s 4424 (.lex permutation11 251) (by rfl)) (lex_11_251_prefix s) (positive_select s 251) (lex_11_251_image s)

theorem lex_11_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.pos 251), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation11 251 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4423) (Sat.Literal.pos 251) (Sat.Literal.pos 127) (lex_11_251_prefix s) (positive_select s 251) (lex_11_251_image s)

theorem lex_11_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.pos 4423)] :=
  (lex_11_251_gate s).prop _ (List.Mem.head _)

theorem lex_11_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.neg 251), (Sat.Literal.pos 127)] :=
  (lex_11_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.pos 251), (Sat.Literal.neg 127)] :=
  (lex_11_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.neg 251), (Sat.Literal.neg 127), (Sat.Literal.pos 4424)] :=
  (lex_11_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4423), (Sat.Literal.pos 251), (Sat.Literal.pos 127), (Sat.Literal.pos 4424)] :=
  (lex_11_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_10_101_gate

end Crown.CertificateData
