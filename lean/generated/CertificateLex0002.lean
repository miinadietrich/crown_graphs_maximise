import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_1_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2724) = lexBefore s permutation1 109 := by
  exact (positive_lex_of_descriptor s 2724 permutation1 114 (by rfl)).trans ((lex_skipped s permutation1 109 114 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 110 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation1 109) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation1 109 by rw [image1_eq]; rfl))

theorem lex_1_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2725) (Sat.Literal.pos 2724) (Sat.Literal.pos 109) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation1 109 (assignment s)
    (Sat.Literal.pos 2725) (Sat.Literal.pos 2724) (Sat.Literal.pos 109) (Sat.Literal.pos 107) (positive_of_descriptor s 2725 (.lex permutation1 109) (by rfl)) (lex_1_109_prefix s) (positive_select s 109) (lex_1_109_image s)

theorem lex_1_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.pos 109), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation1 109 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2724) (Sat.Literal.pos 109) (Sat.Literal.pos 107) (lex_1_109_prefix s) (positive_select s 109) (lex_1_109_image s)

theorem lex_1_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.pos 2724)] :=
  (lex_1_109_gate s).prop _ (List.Mem.head _)

theorem lex_1_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.neg 109), (Sat.Literal.pos 107)] :=
  (lex_1_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.pos 109), (Sat.Literal.neg 107)] :=
  (lex_1_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.neg 109), (Sat.Literal.neg 107), (Sat.Literal.pos 2725)] :=
  (lex_1_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.pos 109), (Sat.Literal.pos 107), (Sat.Literal.pos 2725)] :=
  (lex_1_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2725) = lexBefore s permutation1 108 := by
  exact (positive_lex_of_descriptor s 2725 permutation1 109 (by rfl)).trans ((lex_skipped s permutation1 108 109 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation1 108) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation1 108 by rw [image1_eq]; rfl))

theorem lex_1_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2726) (Sat.Literal.pos 2725) (Sat.Literal.pos 108) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation1 108 (assignment s)
    (Sat.Literal.pos 2726) (Sat.Literal.pos 2725) (Sat.Literal.pos 108) (Sat.Literal.pos 106) (positive_of_descriptor s 2726 (.lex permutation1 108) (by rfl)) (lex_1_108_prefix s) (positive_select s 108) (lex_1_108_image s)

theorem lex_1_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.pos 108), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation1 108 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2725) (Sat.Literal.pos 108) (Sat.Literal.pos 106) (lex_1_108_prefix s) (positive_select s 108) (lex_1_108_image s)

theorem lex_1_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.pos 2725)] :=
  (lex_1_108_gate s).prop _ (List.Mem.head _)

theorem lex_1_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.neg 108), (Sat.Literal.pos 106)] :=
  (lex_1_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.pos 108), (Sat.Literal.neg 106)] :=
  (lex_1_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.neg 108), (Sat.Literal.neg 106), (Sat.Literal.pos 2726)] :=
  (lex_1_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2725), (Sat.Literal.pos 108), (Sat.Literal.pos 106), (Sat.Literal.pos 2726)] :=
  (lex_1_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2726) = lexBefore s permutation1 107 := by
  exact (positive_lex_of_descriptor s 2726 permutation1 108 (by rfl)).trans ((lex_skipped s permutation1 107 108 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation1 107) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation1 107 by rw [image1_eq]; rfl))

theorem lex_1_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2727) (Sat.Literal.pos 2726) (Sat.Literal.pos 107) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation1 107 (assignment s)
    (Sat.Literal.pos 2727) (Sat.Literal.pos 2726) (Sat.Literal.pos 107) (Sat.Literal.pos 109) (positive_of_descriptor s 2727 (.lex permutation1 107) (by rfl)) (lex_1_107_prefix s) (positive_select s 107) (lex_1_107_image s)

theorem lex_1_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.pos 107), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation1 107 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2726) (Sat.Literal.pos 107) (Sat.Literal.pos 109) (lex_1_107_prefix s) (positive_select s 107) (lex_1_107_image s)

theorem lex_1_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.pos 2726)] :=
  (lex_1_107_gate s).prop _ (List.Mem.head _)

theorem lex_1_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.neg 107), (Sat.Literal.pos 109)] :=
  (lex_1_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.pos 107), (Sat.Literal.neg 109)] :=
  (lex_1_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.neg 107), (Sat.Literal.neg 109), (Sat.Literal.pos 2727)] :=
  (lex_1_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2726), (Sat.Literal.pos 107), (Sat.Literal.pos 109), (Sat.Literal.pos 2727)] :=
  (lex_1_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2727) = lexBefore s permutation1 106 := by
  exact (positive_lex_of_descriptor s 2727 permutation1 107 (by rfl)).trans ((lex_skipped s permutation1 106 107 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation1 106) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation1 106 by rw [image1_eq]; rfl))

theorem lex_1_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2728) (Sat.Literal.pos 2727) (Sat.Literal.pos 106) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation1 106 (assignment s)
    (Sat.Literal.pos 2728) (Sat.Literal.pos 2727) (Sat.Literal.pos 106) (Sat.Literal.pos 108) (positive_of_descriptor s 2728 (.lex permutation1 106) (by rfl)) (lex_1_106_prefix s) (positive_select s 106) (lex_1_106_image s)

theorem lex_1_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.pos 106), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation1 106 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2727) (Sat.Literal.pos 106) (Sat.Literal.pos 108) (lex_1_106_prefix s) (positive_select s 106) (lex_1_106_image s)

theorem lex_1_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.pos 2727)] :=
  (lex_1_106_gate s).prop _ (List.Mem.head _)

theorem lex_1_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.neg 106), (Sat.Literal.pos 108)] :=
  (lex_1_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.pos 106), (Sat.Literal.neg 108)] :=
  (lex_1_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.neg 106), (Sat.Literal.neg 108), (Sat.Literal.pos 2728)] :=
  (lex_1_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2727), (Sat.Literal.pos 106), (Sat.Literal.pos 108), (Sat.Literal.pos 2728)] :=
  (lex_1_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2728) = lexBefore s permutation1 101 := by
  exact (positive_lex_of_descriptor s 2728 permutation1 106 (by rfl)).trans ((lex_skipped s permutation1 101 106 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 102 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation1 101) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation1 101 by rw [image1_eq]; rfl))

theorem lex_1_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2729) (Sat.Literal.pos 2728) (Sat.Literal.pos 101) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation1 101 (assignment s)
    (Sat.Literal.pos 2729) (Sat.Literal.pos 2728) (Sat.Literal.pos 101) (Sat.Literal.pos 99) (positive_of_descriptor s 2729 (.lex permutation1 101) (by rfl)) (lex_1_101_prefix s) (positive_select s 101) (lex_1_101_image s)

theorem lex_1_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.pos 101), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation1 101 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2728) (Sat.Literal.pos 101) (Sat.Literal.pos 99) (lex_1_101_prefix s) (positive_select s 101) (lex_1_101_image s)

theorem lex_1_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.pos 2728)] :=
  (lex_1_101_gate s).prop _ (List.Mem.head _)

theorem lex_1_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.neg 101), (Sat.Literal.pos 99)] :=
  (lex_1_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.pos 101), (Sat.Literal.neg 99)] :=
  (lex_1_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.neg 101), (Sat.Literal.neg 99), (Sat.Literal.pos 2729)] :=
  (lex_1_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2728), (Sat.Literal.pos 101), (Sat.Literal.pos 99), (Sat.Literal.pos 2729)] :=
  (lex_1_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2729) = lexBefore s permutation1 100 := by
  exact (positive_lex_of_descriptor s 2729 permutation1 101 (by rfl)).trans ((lex_skipped s permutation1 100 101 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation1 100) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation1 100 by rw [image1_eq]; rfl))

theorem lex_1_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2730) (Sat.Literal.pos 2729) (Sat.Literal.pos 100) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation1 100 (assignment s)
    (Sat.Literal.pos 2730) (Sat.Literal.pos 2729) (Sat.Literal.pos 100) (Sat.Literal.pos 98) (positive_of_descriptor s 2730 (.lex permutation1 100) (by rfl)) (lex_1_100_prefix s) (positive_select s 100) (lex_1_100_image s)

theorem lex_1_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.pos 100), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation1 100 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2729) (Sat.Literal.pos 100) (Sat.Literal.pos 98) (lex_1_100_prefix s) (positive_select s 100) (lex_1_100_image s)

theorem lex_1_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.pos 2729)] :=
  (lex_1_100_gate s).prop _ (List.Mem.head _)

theorem lex_1_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.neg 100), (Sat.Literal.pos 98)] :=
  (lex_1_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.pos 100), (Sat.Literal.neg 98)] :=
  (lex_1_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.neg 100), (Sat.Literal.neg 98), (Sat.Literal.pos 2730)] :=
  (lex_1_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2729), (Sat.Literal.pos 100), (Sat.Literal.pos 98), (Sat.Literal.pos 2730)] :=
  (lex_1_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2730) = lexBefore s permutation1 99 := by
  exact (positive_lex_of_descriptor s 2730 permutation1 100 (by rfl)).trans ((lex_skipped s permutation1 99 100 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation1 99) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation1 99 by rw [image1_eq]; rfl))

theorem lex_1_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2731) (Sat.Literal.pos 2730) (Sat.Literal.pos 99) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation1 99 (assignment s)
    (Sat.Literal.pos 2731) (Sat.Literal.pos 2730) (Sat.Literal.pos 99) (Sat.Literal.pos 101) (positive_of_descriptor s 2731 (.lex permutation1 99) (by rfl)) (lex_1_99_prefix s) (positive_select s 99) (lex_1_99_image s)

theorem lex_1_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.pos 99), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation1 99 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2730) (Sat.Literal.pos 99) (Sat.Literal.pos 101) (lex_1_99_prefix s) (positive_select s 99) (lex_1_99_image s)

theorem lex_1_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.pos 2730)] :=
  (lex_1_99_gate s).prop _ (List.Mem.head _)

theorem lex_1_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.neg 99), (Sat.Literal.pos 101)] :=
  (lex_1_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.pos 99), (Sat.Literal.neg 101)] :=
  (lex_1_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.neg 99), (Sat.Literal.neg 101), (Sat.Literal.pos 2731)] :=
  (lex_1_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2730), (Sat.Literal.pos 99), (Sat.Literal.pos 101), (Sat.Literal.pos 2731)] :=
  (lex_1_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2731) = lexBefore s permutation1 98 := by
  exact (positive_lex_of_descriptor s 2731 permutation1 99 (by rfl)).trans ((lex_skipped s permutation1 98 99 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation1 98) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation1 98 by rw [image1_eq]; rfl))

theorem lex_1_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2732) (Sat.Literal.pos 2731) (Sat.Literal.pos 98) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation1 98 (assignment s)
    (Sat.Literal.pos 2732) (Sat.Literal.pos 2731) (Sat.Literal.pos 98) (Sat.Literal.pos 100) (positive_of_descriptor s 2732 (.lex permutation1 98) (by rfl)) (lex_1_98_prefix s) (positive_select s 98) (lex_1_98_image s)

theorem lex_1_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.pos 98), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation1 98 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2731) (Sat.Literal.pos 98) (Sat.Literal.pos 100) (lex_1_98_prefix s) (positive_select s 98) (lex_1_98_image s)

theorem lex_1_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.pos 2731)] :=
  (lex_1_98_gate s).prop _ (List.Mem.head _)

theorem lex_1_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.neg 98), (Sat.Literal.pos 100)] :=
  (lex_1_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.pos 98), (Sat.Literal.neg 100)] :=
  (lex_1_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.neg 98), (Sat.Literal.neg 100), (Sat.Literal.pos 2732)] :=
  (lex_1_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2731), (Sat.Literal.pos 98), (Sat.Literal.pos 100), (Sat.Literal.pos 2732)] :=
  (lex_1_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2732) = lexBefore s permutation1 93 := by
  exact (positive_lex_of_descriptor s 2732 permutation1 98 (by rfl)).trans ((lex_skipped s permutation1 93 98 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 94 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation1 93) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation1 93 by rw [image1_eq]; rfl))

theorem lex_1_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2733) (Sat.Literal.pos 2732) (Sat.Literal.pos 93) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation1 93 (assignment s)
    (Sat.Literal.pos 2733) (Sat.Literal.pos 2732) (Sat.Literal.pos 93) (Sat.Literal.pos 91) (positive_of_descriptor s 2733 (.lex permutation1 93) (by rfl)) (lex_1_93_prefix s) (positive_select s 93) (lex_1_93_image s)

theorem lex_1_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.pos 93), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation1 93 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2732) (Sat.Literal.pos 93) (Sat.Literal.pos 91) (lex_1_93_prefix s) (positive_select s 93) (lex_1_93_image s)

theorem lex_1_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.pos 2732)] :=
  (lex_1_93_gate s).prop _ (List.Mem.head _)

theorem lex_1_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.neg 93), (Sat.Literal.pos 91)] :=
  (lex_1_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.pos 93), (Sat.Literal.neg 91)] :=
  (lex_1_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.neg 93), (Sat.Literal.neg 91), (Sat.Literal.pos 2733)] :=
  (lex_1_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2732), (Sat.Literal.pos 93), (Sat.Literal.pos 91), (Sat.Literal.pos 2733)] :=
  (lex_1_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2733) = lexBefore s permutation1 92 := by
  exact (positive_lex_of_descriptor s 2733 permutation1 93 (by rfl)).trans ((lex_skipped s permutation1 92 93 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation1 92) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation1 92 by rw [image1_eq]; rfl))

theorem lex_1_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2734) (Sat.Literal.pos 2733) (Sat.Literal.pos 92) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation1 92 (assignment s)
    (Sat.Literal.pos 2734) (Sat.Literal.pos 2733) (Sat.Literal.pos 92) (Sat.Literal.pos 90) (positive_of_descriptor s 2734 (.lex permutation1 92) (by rfl)) (lex_1_92_prefix s) (positive_select s 92) (lex_1_92_image s)

theorem lex_1_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.pos 92), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation1 92 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2733) (Sat.Literal.pos 92) (Sat.Literal.pos 90) (lex_1_92_prefix s) (positive_select s 92) (lex_1_92_image s)

theorem lex_1_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.pos 2733)] :=
  (lex_1_92_gate s).prop _ (List.Mem.head _)

theorem lex_1_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.neg 92), (Sat.Literal.pos 90)] :=
  (lex_1_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.pos 92), (Sat.Literal.neg 90)] :=
  (lex_1_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.neg 92), (Sat.Literal.neg 90), (Sat.Literal.pos 2734)] :=
  (lex_1_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2733), (Sat.Literal.pos 92), (Sat.Literal.pos 90), (Sat.Literal.pos 2734)] :=
  (lex_1_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2734) = lexBefore s permutation1 91 := by
  exact (positive_lex_of_descriptor s 2734 permutation1 92 (by rfl)).trans ((lex_skipped s permutation1 91 92 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation1 91) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation1 91 by rw [image1_eq]; rfl))

theorem lex_1_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2735) (Sat.Literal.pos 2734) (Sat.Literal.pos 91) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation1 91 (assignment s)
    (Sat.Literal.pos 2735) (Sat.Literal.pos 2734) (Sat.Literal.pos 91) (Sat.Literal.pos 93) (positive_of_descriptor s 2735 (.lex permutation1 91) (by rfl)) (lex_1_91_prefix s) (positive_select s 91) (lex_1_91_image s)

theorem lex_1_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.pos 91), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation1 91 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2734) (Sat.Literal.pos 91) (Sat.Literal.pos 93) (lex_1_91_prefix s) (positive_select s 91) (lex_1_91_image s)

theorem lex_1_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.pos 2734)] :=
  (lex_1_91_gate s).prop _ (List.Mem.head _)

theorem lex_1_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.neg 91), (Sat.Literal.pos 93)] :=
  (lex_1_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.pos 91), (Sat.Literal.neg 93)] :=
  (lex_1_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.neg 91), (Sat.Literal.neg 93), (Sat.Literal.pos 2735)] :=
  (lex_1_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2734), (Sat.Literal.pos 91), (Sat.Literal.pos 93), (Sat.Literal.pos 2735)] :=
  (lex_1_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2735) = lexBefore s permutation1 90 := by
  exact (positive_lex_of_descriptor s 2735 permutation1 91 (by rfl)).trans ((lex_skipped s permutation1 90 91 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation1 90) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation1 90 by rw [image1_eq]; rfl))

theorem lex_1_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2736) (Sat.Literal.pos 2735) (Sat.Literal.pos 90) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation1 90 (assignment s)
    (Sat.Literal.pos 2736) (Sat.Literal.pos 2735) (Sat.Literal.pos 90) (Sat.Literal.pos 92) (positive_of_descriptor s 2736 (.lex permutation1 90) (by rfl)) (lex_1_90_prefix s) (positive_select s 90) (lex_1_90_image s)

theorem lex_1_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.pos 90), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation1 90 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2735) (Sat.Literal.pos 90) (Sat.Literal.pos 92) (lex_1_90_prefix s) (positive_select s 90) (lex_1_90_image s)

theorem lex_1_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.pos 2735)] :=
  (lex_1_90_gate s).prop _ (List.Mem.head _)

theorem lex_1_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.neg 90), (Sat.Literal.pos 92)] :=
  (lex_1_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.pos 90), (Sat.Literal.neg 92)] :=
  (lex_1_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.neg 90), (Sat.Literal.neg 92), (Sat.Literal.pos 2736)] :=
  (lex_1_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2735), (Sat.Literal.pos 90), (Sat.Literal.pos 92), (Sat.Literal.pos 2736)] :=
  (lex_1_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2736) = lexBefore s permutation1 85 := by
  exact (positive_lex_of_descriptor s 2736 permutation1 90 (by rfl)).trans ((lex_skipped s permutation1 85 90 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 86 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation1 85) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation1 85 by rw [image1_eq]; rfl))

theorem lex_1_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2737) (Sat.Literal.pos 2736) (Sat.Literal.pos 85) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation1 85 (assignment s)
    (Sat.Literal.pos 2737) (Sat.Literal.pos 2736) (Sat.Literal.pos 85) (Sat.Literal.pos 83) (positive_of_descriptor s 2737 (.lex permutation1 85) (by rfl)) (lex_1_85_prefix s) (positive_select s 85) (lex_1_85_image s)

theorem lex_1_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.pos 85), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation1 85 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2736) (Sat.Literal.pos 85) (Sat.Literal.pos 83) (lex_1_85_prefix s) (positive_select s 85) (lex_1_85_image s)

theorem lex_1_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.pos 2736)] :=
  (lex_1_85_gate s).prop _ (List.Mem.head _)

theorem lex_1_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.neg 85), (Sat.Literal.pos 83)] :=
  (lex_1_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.pos 85), (Sat.Literal.neg 83)] :=
  (lex_1_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.neg 85), (Sat.Literal.neg 83), (Sat.Literal.pos 2737)] :=
  (lex_1_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2736), (Sat.Literal.pos 85), (Sat.Literal.pos 83), (Sat.Literal.pos 2737)] :=
  (lex_1_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2737) = lexBefore s permutation1 84 := by
  exact (positive_lex_of_descriptor s 2737 permutation1 85 (by rfl)).trans ((lex_skipped s permutation1 84 85 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation1 84) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation1 84 by rw [image1_eq]; rfl))

theorem lex_1_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2738) (Sat.Literal.pos 2737) (Sat.Literal.pos 84) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation1 84 (assignment s)
    (Sat.Literal.pos 2738) (Sat.Literal.pos 2737) (Sat.Literal.pos 84) (Sat.Literal.pos 82) (positive_of_descriptor s 2738 (.lex permutation1 84) (by rfl)) (lex_1_84_prefix s) (positive_select s 84) (lex_1_84_image s)

theorem lex_1_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.pos 84), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation1 84 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2737) (Sat.Literal.pos 84) (Sat.Literal.pos 82) (lex_1_84_prefix s) (positive_select s 84) (lex_1_84_image s)

theorem lex_1_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.pos 2737)] :=
  (lex_1_84_gate s).prop _ (List.Mem.head _)

theorem lex_1_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.neg 84), (Sat.Literal.pos 82)] :=
  (lex_1_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.pos 84), (Sat.Literal.neg 82)] :=
  (lex_1_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.neg 84), (Sat.Literal.neg 82), (Sat.Literal.pos 2738)] :=
  (lex_1_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2737), (Sat.Literal.pos 84), (Sat.Literal.pos 82), (Sat.Literal.pos 2738)] :=
  (lex_1_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2738) = lexBefore s permutation1 83 := by
  exact (positive_lex_of_descriptor s 2738 permutation1 84 (by rfl)).trans ((lex_skipped s permutation1 83 84 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation1 83) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation1 83 by rw [image1_eq]; rfl))

theorem lex_1_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2739) (Sat.Literal.pos 2738) (Sat.Literal.pos 83) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation1 83 (assignment s)
    (Sat.Literal.pos 2739) (Sat.Literal.pos 2738) (Sat.Literal.pos 83) (Sat.Literal.pos 85) (positive_of_descriptor s 2739 (.lex permutation1 83) (by rfl)) (lex_1_83_prefix s) (positive_select s 83) (lex_1_83_image s)

theorem lex_1_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.pos 83), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation1 83 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2738) (Sat.Literal.pos 83) (Sat.Literal.pos 85) (lex_1_83_prefix s) (positive_select s 83) (lex_1_83_image s)

theorem lex_1_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.pos 2738)] :=
  (lex_1_83_gate s).prop _ (List.Mem.head _)

theorem lex_1_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.neg 83), (Sat.Literal.pos 85)] :=
  (lex_1_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.pos 83), (Sat.Literal.neg 85)] :=
  (lex_1_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.neg 83), (Sat.Literal.neg 85), (Sat.Literal.pos 2739)] :=
  (lex_1_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2738), (Sat.Literal.pos 83), (Sat.Literal.pos 85), (Sat.Literal.pos 2739)] :=
  (lex_1_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2739) = lexBefore s permutation1 82 := by
  exact (positive_lex_of_descriptor s 2739 permutation1 83 (by rfl)).trans ((lex_skipped s permutation1 82 83 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation1 82) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation1 82 by rw [image1_eq]; rfl))

theorem lex_1_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2740) (Sat.Literal.pos 2739) (Sat.Literal.pos 82) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation1 82 (assignment s)
    (Sat.Literal.pos 2740) (Sat.Literal.pos 2739) (Sat.Literal.pos 82) (Sat.Literal.pos 84) (positive_of_descriptor s 2740 (.lex permutation1 82) (by rfl)) (lex_1_82_prefix s) (positive_select s 82) (lex_1_82_image s)

theorem lex_1_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.pos 82), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation1 82 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2739) (Sat.Literal.pos 82) (Sat.Literal.pos 84) (lex_1_82_prefix s) (positive_select s 82) (lex_1_82_image s)

theorem lex_1_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.pos 2739)] :=
  (lex_1_82_gate s).prop _ (List.Mem.head _)

theorem lex_1_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.neg 82), (Sat.Literal.pos 84)] :=
  (lex_1_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.pos 82), (Sat.Literal.neg 84)] :=
  (lex_1_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.neg 82), (Sat.Literal.neg 84), (Sat.Literal.pos 2740)] :=
  (lex_1_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2739), (Sat.Literal.pos 82), (Sat.Literal.pos 84), (Sat.Literal.pos 2740)] :=
  (lex_1_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2740) = lexBefore s permutation1 77 := by
  exact (positive_lex_of_descriptor s 2740 permutation1 82 (by rfl)).trans ((lex_skipped s permutation1 77 82 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 78 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation1 77) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation1 77 by rw [image1_eq]; rfl))

theorem lex_1_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2741) (Sat.Literal.pos 2740) (Sat.Literal.pos 77) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation1 77 (assignment s)
    (Sat.Literal.pos 2741) (Sat.Literal.pos 2740) (Sat.Literal.pos 77) (Sat.Literal.pos 75) (positive_of_descriptor s 2741 (.lex permutation1 77) (by rfl)) (lex_1_77_prefix s) (positive_select s 77) (lex_1_77_image s)

theorem lex_1_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.pos 77), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation1 77 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2740) (Sat.Literal.pos 77) (Sat.Literal.pos 75) (lex_1_77_prefix s) (positive_select s 77) (lex_1_77_image s)

theorem lex_1_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.pos 2740)] :=
  (lex_1_77_gate s).prop _ (List.Mem.head _)

theorem lex_1_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.neg 77), (Sat.Literal.pos 75)] :=
  (lex_1_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.pos 77), (Sat.Literal.neg 75)] :=
  (lex_1_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.neg 77), (Sat.Literal.neg 75), (Sat.Literal.pos 2741)] :=
  (lex_1_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2740), (Sat.Literal.pos 77), (Sat.Literal.pos 75), (Sat.Literal.pos 2741)] :=
  (lex_1_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2741) = lexBefore s permutation1 76 := by
  exact (positive_lex_of_descriptor s 2741 permutation1 77 (by rfl)).trans ((lex_skipped s permutation1 76 77 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation1 76) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation1 76 by rw [image1_eq]; rfl))

theorem lex_1_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2742) (Sat.Literal.pos 2741) (Sat.Literal.pos 76) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation1 76 (assignment s)
    (Sat.Literal.pos 2742) (Sat.Literal.pos 2741) (Sat.Literal.pos 76) (Sat.Literal.pos 74) (positive_of_descriptor s 2742 (.lex permutation1 76) (by rfl)) (lex_1_76_prefix s) (positive_select s 76) (lex_1_76_image s)

theorem lex_1_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.pos 76), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation1 76 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2741) (Sat.Literal.pos 76) (Sat.Literal.pos 74) (lex_1_76_prefix s) (positive_select s 76) (lex_1_76_image s)

theorem lex_1_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.pos 2741)] :=
  (lex_1_76_gate s).prop _ (List.Mem.head _)

theorem lex_1_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.neg 76), (Sat.Literal.pos 74)] :=
  (lex_1_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.pos 76), (Sat.Literal.neg 74)] :=
  (lex_1_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.neg 76), (Sat.Literal.neg 74), (Sat.Literal.pos 2742)] :=
  (lex_1_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2741), (Sat.Literal.pos 76), (Sat.Literal.pos 74), (Sat.Literal.pos 2742)] :=
  (lex_1_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2742) = lexBefore s permutation1 75 := by
  exact (positive_lex_of_descriptor s 2742 permutation1 76 (by rfl)).trans ((lex_skipped s permutation1 75 76 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation1 75) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation1 75 by rw [image1_eq]; rfl))

theorem lex_1_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2743) (Sat.Literal.pos 2742) (Sat.Literal.pos 75) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation1 75 (assignment s)
    (Sat.Literal.pos 2743) (Sat.Literal.pos 2742) (Sat.Literal.pos 75) (Sat.Literal.pos 77) (positive_of_descriptor s 2743 (.lex permutation1 75) (by rfl)) (lex_1_75_prefix s) (positive_select s 75) (lex_1_75_image s)

theorem lex_1_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.pos 75), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation1 75 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2742) (Sat.Literal.pos 75) (Sat.Literal.pos 77) (lex_1_75_prefix s) (positive_select s 75) (lex_1_75_image s)

theorem lex_1_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.pos 2742)] :=
  (lex_1_75_gate s).prop _ (List.Mem.head _)

theorem lex_1_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.neg 75), (Sat.Literal.pos 77)] :=
  (lex_1_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.pos 75), (Sat.Literal.neg 77)] :=
  (lex_1_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.neg 75), (Sat.Literal.neg 77), (Sat.Literal.pos 2743)] :=
  (lex_1_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2742), (Sat.Literal.pos 75), (Sat.Literal.pos 77), (Sat.Literal.pos 2743)] :=
  (lex_1_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2743) = lexBefore s permutation1 74 := by
  exact (positive_lex_of_descriptor s 2743 permutation1 75 (by rfl)).trans ((lex_skipped s permutation1 74 75 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation1 74) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation1 74 by rw [image1_eq]; rfl))

theorem lex_1_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2744) (Sat.Literal.pos 2743) (Sat.Literal.pos 74) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation1 74 (assignment s)
    (Sat.Literal.pos 2744) (Sat.Literal.pos 2743) (Sat.Literal.pos 74) (Sat.Literal.pos 76) (positive_of_descriptor s 2744 (.lex permutation1 74) (by rfl)) (lex_1_74_prefix s) (positive_select s 74) (lex_1_74_image s)

theorem lex_1_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.pos 74), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation1 74 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2743) (Sat.Literal.pos 74) (Sat.Literal.pos 76) (lex_1_74_prefix s) (positive_select s 74) (lex_1_74_image s)

theorem lex_1_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.pos 2743)] :=
  (lex_1_74_gate s).prop _ (List.Mem.head _)

theorem lex_1_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.neg 74), (Sat.Literal.pos 76)] :=
  (lex_1_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.pos 74), (Sat.Literal.neg 76)] :=
  (lex_1_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.neg 74), (Sat.Literal.neg 76), (Sat.Literal.pos 2744)] :=
  (lex_1_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2743), (Sat.Literal.pos 74), (Sat.Literal.pos 76), (Sat.Literal.pos 2744)] :=
  (lex_1_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2744) = lexBefore s permutation1 69 := by
  exact (positive_lex_of_descriptor s 2744 permutation1 74 (by rfl)).trans ((lex_skipped s permutation1 69 74 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 70 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation1 69) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation1 69 by rw [image1_eq]; rfl))

theorem lex_1_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2745) (Sat.Literal.pos 2744) (Sat.Literal.pos 69) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation1 69 (assignment s)
    (Sat.Literal.pos 2745) (Sat.Literal.pos 2744) (Sat.Literal.pos 69) (Sat.Literal.pos 67) (positive_of_descriptor s 2745 (.lex permutation1 69) (by rfl)) (lex_1_69_prefix s) (positive_select s 69) (lex_1_69_image s)

theorem lex_1_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.pos 69), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation1 69 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2744) (Sat.Literal.pos 69) (Sat.Literal.pos 67) (lex_1_69_prefix s) (positive_select s 69) (lex_1_69_image s)

theorem lex_1_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.pos 2744)] :=
  (lex_1_69_gate s).prop _ (List.Mem.head _)

theorem lex_1_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.neg 69), (Sat.Literal.pos 67)] :=
  (lex_1_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.pos 69), (Sat.Literal.neg 67)] :=
  (lex_1_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.neg 69), (Sat.Literal.neg 67), (Sat.Literal.pos 2745)] :=
  (lex_1_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2744), (Sat.Literal.pos 69), (Sat.Literal.pos 67), (Sat.Literal.pos 2745)] :=
  (lex_1_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2745) = lexBefore s permutation1 68 := by
  exact (positive_lex_of_descriptor s 2745 permutation1 69 (by rfl)).trans ((lex_skipped s permutation1 68 69 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation1 68) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation1 68 by rw [image1_eq]; rfl))

theorem lex_1_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2746) (Sat.Literal.pos 2745) (Sat.Literal.pos 68) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation1 68 (assignment s)
    (Sat.Literal.pos 2746) (Sat.Literal.pos 2745) (Sat.Literal.pos 68) (Sat.Literal.pos 66) (positive_of_descriptor s 2746 (.lex permutation1 68) (by rfl)) (lex_1_68_prefix s) (positive_select s 68) (lex_1_68_image s)

theorem lex_1_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.pos 68), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation1 68 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2745) (Sat.Literal.pos 68) (Sat.Literal.pos 66) (lex_1_68_prefix s) (positive_select s 68) (lex_1_68_image s)

theorem lex_1_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.pos 2745)] :=
  (lex_1_68_gate s).prop _ (List.Mem.head _)

theorem lex_1_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.neg 68), (Sat.Literal.pos 66)] :=
  (lex_1_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.pos 68), (Sat.Literal.neg 66)] :=
  (lex_1_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.neg 68), (Sat.Literal.neg 66), (Sat.Literal.pos 2746)] :=
  (lex_1_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2745), (Sat.Literal.pos 68), (Sat.Literal.pos 66), (Sat.Literal.pos 2746)] :=
  (lex_1_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2746) = lexBefore s permutation1 67 := by
  exact (positive_lex_of_descriptor s 2746 permutation1 68 (by rfl)).trans ((lex_skipped s permutation1 67 68 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation1 67) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation1 67 by rw [image1_eq]; rfl))

theorem lex_1_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2747) (Sat.Literal.pos 2746) (Sat.Literal.pos 67) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation1 67 (assignment s)
    (Sat.Literal.pos 2747) (Sat.Literal.pos 2746) (Sat.Literal.pos 67) (Sat.Literal.pos 69) (positive_of_descriptor s 2747 (.lex permutation1 67) (by rfl)) (lex_1_67_prefix s) (positive_select s 67) (lex_1_67_image s)

theorem lex_1_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.pos 67), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation1 67 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2746) (Sat.Literal.pos 67) (Sat.Literal.pos 69) (lex_1_67_prefix s) (positive_select s 67) (lex_1_67_image s)

theorem lex_1_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.pos 2746)] :=
  (lex_1_67_gate s).prop _ (List.Mem.head _)

theorem lex_1_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.neg 67), (Sat.Literal.pos 69)] :=
  (lex_1_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.pos 67), (Sat.Literal.neg 69)] :=
  (lex_1_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.neg 67), (Sat.Literal.neg 69), (Sat.Literal.pos 2747)] :=
  (lex_1_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2746), (Sat.Literal.pos 67), (Sat.Literal.pos 69), (Sat.Literal.pos 2747)] :=
  (lex_1_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2747) = lexBefore s permutation1 66 := by
  exact (positive_lex_of_descriptor s 2747 permutation1 67 (by rfl)).trans ((lex_skipped s permutation1 66 67 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation1 66) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation1 66 by rw [image1_eq]; rfl))

theorem lex_1_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2748) (Sat.Literal.pos 2747) (Sat.Literal.pos 66) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation1 66 (assignment s)
    (Sat.Literal.pos 2748) (Sat.Literal.pos 2747) (Sat.Literal.pos 66) (Sat.Literal.pos 68) (positive_of_descriptor s 2748 (.lex permutation1 66) (by rfl)) (lex_1_66_prefix s) (positive_select s 66) (lex_1_66_image s)

theorem lex_1_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.pos 66), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation1 66 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2747) (Sat.Literal.pos 66) (Sat.Literal.pos 68) (lex_1_66_prefix s) (positive_select s 66) (lex_1_66_image s)

theorem lex_1_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.pos 2747)] :=
  (lex_1_66_gate s).prop _ (List.Mem.head _)

theorem lex_1_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.neg 66), (Sat.Literal.pos 68)] :=
  (lex_1_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.pos 66), (Sat.Literal.neg 68)] :=
  (lex_1_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.neg 66), (Sat.Literal.neg 68), (Sat.Literal.pos 2748)] :=
  (lex_1_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2747), (Sat.Literal.pos 66), (Sat.Literal.pos 68), (Sat.Literal.pos 2748)] :=
  (lex_1_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2748) = lexBefore s permutation1 61 := by
  exact (positive_lex_of_descriptor s 2748 permutation1 66 (by rfl)).trans ((lex_skipped s permutation1 61 66 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 62 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation1 61) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation1 61 by rw [image1_eq]; rfl))

theorem lex_1_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2749) (Sat.Literal.pos 2748) (Sat.Literal.pos 61) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation1 61 (assignment s)
    (Sat.Literal.pos 2749) (Sat.Literal.pos 2748) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (positive_of_descriptor s 2749 (.lex permutation1 61) (by rfl)) (lex_1_61_prefix s) (positive_select s 61) (lex_1_61_image s)

theorem lex_1_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation1 61 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2748) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (lex_1_61_prefix s) (positive_select s 61) (lex_1_61_image s)

theorem lex_1_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.pos 2748)] :=
  (lex_1_61_gate s).prop _ (List.Mem.head _)

theorem lex_1_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.neg 61), (Sat.Literal.pos 59)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.neg 61), (Sat.Literal.neg 59), (Sat.Literal.pos 2749)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2748), (Sat.Literal.pos 61), (Sat.Literal.pos 59), (Sat.Literal.pos 2749)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2749) = lexBefore s permutation1 60 := by
  exact (positive_lex_of_descriptor s 2749 permutation1 61 (by rfl)).trans ((lex_skipped s permutation1 60 61 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation1 60) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation1 60 by rw [image1_eq]; rfl))

theorem lex_1_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2750) (Sat.Literal.pos 2749) (Sat.Literal.pos 60) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation1 60 (assignment s)
    (Sat.Literal.pos 2750) (Sat.Literal.pos 2749) (Sat.Literal.pos 60) (Sat.Literal.pos 58) (positive_of_descriptor s 2750 (.lex permutation1 60) (by rfl)) (lex_1_60_prefix s) (positive_select s 60) (lex_1_60_image s)

theorem lex_1_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.pos 60), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation1 60 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2749) (Sat.Literal.pos 60) (Sat.Literal.pos 58) (lex_1_60_prefix s) (positive_select s 60) (lex_1_60_image s)

theorem lex_1_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.pos 2749)] :=
  (lex_1_60_gate s).prop _ (List.Mem.head _)

theorem lex_1_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.neg 60), (Sat.Literal.pos 58)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.pos 60), (Sat.Literal.neg 58)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.neg 60), (Sat.Literal.neg 58), (Sat.Literal.pos 2750)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2749), (Sat.Literal.pos 60), (Sat.Literal.pos 58), (Sat.Literal.pos 2750)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2750) = lexBefore s permutation1 59 := by
  exact (positive_lex_of_descriptor s 2750 permutation1 60 (by rfl)).trans ((lex_skipped s permutation1 59 60 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation1 59) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation1 59 by rw [image1_eq]; rfl))

theorem lex_1_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2751) (Sat.Literal.pos 2750) (Sat.Literal.pos 59) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation1 59 (assignment s)
    (Sat.Literal.pos 2751) (Sat.Literal.pos 2750) (Sat.Literal.pos 59) (Sat.Literal.pos 61) (positive_of_descriptor s 2751 (.lex permutation1 59) (by rfl)) (lex_1_59_prefix s) (positive_select s 59) (lex_1_59_image s)

theorem lex_1_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.pos 59), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation1 59 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2750) (Sat.Literal.pos 59) (Sat.Literal.pos 61) (lex_1_59_prefix s) (positive_select s 59) (lex_1_59_image s)

theorem lex_1_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.pos 2750)] :=
  (lex_1_59_gate s).prop _ (List.Mem.head _)

theorem lex_1_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.neg 59), (Sat.Literal.pos 61)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.pos 59), (Sat.Literal.neg 61)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.neg 59), (Sat.Literal.neg 61), (Sat.Literal.pos 2751)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2750), (Sat.Literal.pos 59), (Sat.Literal.pos 61), (Sat.Literal.pos 2751)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2751) = lexBefore s permutation1 58 := by
  exact (positive_lex_of_descriptor s 2751 permutation1 59 (by rfl)).trans ((lex_skipped s permutation1 58 59 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation1 58) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation1 58 by rw [image1_eq]; rfl))

theorem lex_1_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2752) (Sat.Literal.pos 2751) (Sat.Literal.pos 58) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation1 58 (assignment s)
    (Sat.Literal.pos 2752) (Sat.Literal.pos 2751) (Sat.Literal.pos 58) (Sat.Literal.pos 60) (positive_of_descriptor s 2752 (.lex permutation1 58) (by rfl)) (lex_1_58_prefix s) (positive_select s 58) (lex_1_58_image s)

theorem lex_1_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.pos 58), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation1 58 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2751) (Sat.Literal.pos 58) (Sat.Literal.pos 60) (lex_1_58_prefix s) (positive_select s 58) (lex_1_58_image s)

theorem lex_1_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.pos 2751)] :=
  (lex_1_58_gate s).prop _ (List.Mem.head _)

theorem lex_1_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.neg 58), (Sat.Literal.pos 60)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.pos 58), (Sat.Literal.neg 60)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.neg 58), (Sat.Literal.neg 60), (Sat.Literal.pos 2752)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2751), (Sat.Literal.pos 58), (Sat.Literal.pos 60), (Sat.Literal.pos 2752)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2752) = lexBefore s permutation1 53 := by
  exact (positive_lex_of_descriptor s 2752 permutation1 58 (by rfl)).trans ((lex_skipped s permutation1 53 58 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 54 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation1 53) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation1 53 by rw [image1_eq]; rfl))

theorem lex_1_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2753) (Sat.Literal.pos 2752) (Sat.Literal.pos 53) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation1 53 (assignment s)
    (Sat.Literal.pos 2753) (Sat.Literal.pos 2752) (Sat.Literal.pos 53) (Sat.Literal.pos 51) (positive_of_descriptor s 2753 (.lex permutation1 53) (by rfl)) (lex_1_53_prefix s) (positive_select s 53) (lex_1_53_image s)

theorem lex_1_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.pos 53), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation1 53 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2752) (Sat.Literal.pos 53) (Sat.Literal.pos 51) (lex_1_53_prefix s) (positive_select s 53) (lex_1_53_image s)

theorem lex_1_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.pos 2752)] :=
  (lex_1_53_gate s).prop _ (List.Mem.head _)

theorem lex_1_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.neg 53), (Sat.Literal.pos 51)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.pos 53), (Sat.Literal.neg 51)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.neg 53), (Sat.Literal.neg 51), (Sat.Literal.pos 2753)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2752), (Sat.Literal.pos 53), (Sat.Literal.pos 51), (Sat.Literal.pos 2753)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2753) = lexBefore s permutation1 52 := by
  exact (positive_lex_of_descriptor s 2753 permutation1 53 (by rfl)).trans ((lex_skipped s permutation1 52 53 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation1 52) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation1 52 by rw [image1_eq]; rfl))

theorem lex_1_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2754) (Sat.Literal.pos 2753) (Sat.Literal.pos 52) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation1 52 (assignment s)
    (Sat.Literal.pos 2754) (Sat.Literal.pos 2753) (Sat.Literal.pos 52) (Sat.Literal.pos 50) (positive_of_descriptor s 2754 (.lex permutation1 52) (by rfl)) (lex_1_52_prefix s) (positive_select s 52) (lex_1_52_image s)

theorem lex_1_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.pos 52), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation1 52 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2753) (Sat.Literal.pos 52) (Sat.Literal.pos 50) (lex_1_52_prefix s) (positive_select s 52) (lex_1_52_image s)

theorem lex_1_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.pos 2753)] :=
  (lex_1_52_gate s).prop _ (List.Mem.head _)

theorem lex_1_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.neg 52), (Sat.Literal.pos 50)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.pos 52), (Sat.Literal.neg 50)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.neg 52), (Sat.Literal.neg 50), (Sat.Literal.pos 2754)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2753), (Sat.Literal.pos 52), (Sat.Literal.pos 50), (Sat.Literal.pos 2754)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2754) = lexBefore s permutation1 51 := by
  exact (positive_lex_of_descriptor s 2754 permutation1 52 (by rfl)).trans ((lex_skipped s permutation1 51 52 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation1 51) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation1 51 by rw [image1_eq]; rfl))

theorem lex_1_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2755) (Sat.Literal.pos 2754) (Sat.Literal.pos 51) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation1 51 (assignment s)
    (Sat.Literal.pos 2755) (Sat.Literal.pos 2754) (Sat.Literal.pos 51) (Sat.Literal.pos 53) (positive_of_descriptor s 2755 (.lex permutation1 51) (by rfl)) (lex_1_51_prefix s) (positive_select s 51) (lex_1_51_image s)

theorem lex_1_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.pos 51), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation1 51 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2754) (Sat.Literal.pos 51) (Sat.Literal.pos 53) (lex_1_51_prefix s) (positive_select s 51) (lex_1_51_image s)

theorem lex_1_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.pos 2754)] :=
  (lex_1_51_gate s).prop _ (List.Mem.head _)

theorem lex_1_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.neg 51), (Sat.Literal.pos 53)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.pos 51), (Sat.Literal.neg 53)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.neg 51), (Sat.Literal.neg 53), (Sat.Literal.pos 2755)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2754), (Sat.Literal.pos 51), (Sat.Literal.pos 53), (Sat.Literal.pos 2755)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2755) = lexBefore s permutation1 50 := by
  exact (positive_lex_of_descriptor s 2755 permutation1 51 (by rfl)).trans ((lex_skipped s permutation1 50 51 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation1 50) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation1 50 by rw [image1_eq]; rfl))

theorem lex_1_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2756) (Sat.Literal.pos 2755) (Sat.Literal.pos 50) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation1 50 (assignment s)
    (Sat.Literal.pos 2756) (Sat.Literal.pos 2755) (Sat.Literal.pos 50) (Sat.Literal.pos 52) (positive_of_descriptor s 2756 (.lex permutation1 50) (by rfl)) (lex_1_50_prefix s) (positive_select s 50) (lex_1_50_image s)

theorem lex_1_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.pos 50), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation1 50 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2755) (Sat.Literal.pos 50) (Sat.Literal.pos 52) (lex_1_50_prefix s) (positive_select s 50) (lex_1_50_image s)

theorem lex_1_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.pos 2755)] :=
  (lex_1_50_gate s).prop _ (List.Mem.head _)

theorem lex_1_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.neg 50), (Sat.Literal.pos 52)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.pos 50), (Sat.Literal.neg 52)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.neg 50), (Sat.Literal.neg 52), (Sat.Literal.pos 2756)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2755), (Sat.Literal.pos 50), (Sat.Literal.pos 52), (Sat.Literal.pos 2756)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2756) = lexBefore s permutation1 45 := by
  exact (positive_lex_of_descriptor s 2756 permutation1 50 (by rfl)).trans ((lex_skipped s permutation1 45 50 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 46 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation1 45) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation1 45 by rw [image1_eq]; rfl))

theorem lex_1_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2757) (Sat.Literal.pos 2756) (Sat.Literal.pos 45) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation1 45 (assignment s)
    (Sat.Literal.pos 2757) (Sat.Literal.pos 2756) (Sat.Literal.pos 45) (Sat.Literal.pos 43) (positive_of_descriptor s 2757 (.lex permutation1 45) (by rfl)) (lex_1_45_prefix s) (positive_select s 45) (lex_1_45_image s)

theorem lex_1_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.pos 45), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation1 45 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2756) (Sat.Literal.pos 45) (Sat.Literal.pos 43) (lex_1_45_prefix s) (positive_select s 45) (lex_1_45_image s)

theorem lex_1_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.pos 2756)] :=
  (lex_1_45_gate s).prop _ (List.Mem.head _)

theorem lex_1_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.neg 45), (Sat.Literal.pos 43)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.pos 45), (Sat.Literal.neg 43)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.neg 45), (Sat.Literal.neg 43), (Sat.Literal.pos 2757)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2756), (Sat.Literal.pos 45), (Sat.Literal.pos 43), (Sat.Literal.pos 2757)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2757) = lexBefore s permutation1 44 := by
  exact (positive_lex_of_descriptor s 2757 permutation1 45 (by rfl)).trans ((lex_skipped s permutation1 44 45 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation1 44) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation1 44 by rw [image1_eq]; rfl))

theorem lex_1_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2758) (Sat.Literal.pos 2757) (Sat.Literal.pos 44) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation1 44 (assignment s)
    (Sat.Literal.pos 2758) (Sat.Literal.pos 2757) (Sat.Literal.pos 44) (Sat.Literal.pos 42) (positive_of_descriptor s 2758 (.lex permutation1 44) (by rfl)) (lex_1_44_prefix s) (positive_select s 44) (lex_1_44_image s)

theorem lex_1_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.pos 44), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation1 44 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2757) (Sat.Literal.pos 44) (Sat.Literal.pos 42) (lex_1_44_prefix s) (positive_select s 44) (lex_1_44_image s)

theorem lex_1_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.pos 2757)] :=
  (lex_1_44_gate s).prop _ (List.Mem.head _)

theorem lex_1_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.neg 44), (Sat.Literal.pos 42)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.pos 44), (Sat.Literal.neg 42)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.neg 44), (Sat.Literal.neg 42), (Sat.Literal.pos 2758)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2757), (Sat.Literal.pos 44), (Sat.Literal.pos 42), (Sat.Literal.pos 2758)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2758) = lexBefore s permutation1 43 := by
  exact (positive_lex_of_descriptor s 2758 permutation1 44 (by rfl)).trans ((lex_skipped s permutation1 43 44 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation1 43) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation1 43 by rw [image1_eq]; rfl))

theorem lex_1_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2759) (Sat.Literal.pos 2758) (Sat.Literal.pos 43) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation1 43 (assignment s)
    (Sat.Literal.pos 2759) (Sat.Literal.pos 2758) (Sat.Literal.pos 43) (Sat.Literal.pos 45) (positive_of_descriptor s 2759 (.lex permutation1 43) (by rfl)) (lex_1_43_prefix s) (positive_select s 43) (lex_1_43_image s)

theorem lex_1_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.pos 43), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation1 43 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2758) (Sat.Literal.pos 43) (Sat.Literal.pos 45) (lex_1_43_prefix s) (positive_select s 43) (lex_1_43_image s)

theorem lex_1_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.pos 2758)] :=
  (lex_1_43_gate s).prop _ (List.Mem.head _)

theorem lex_1_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.neg 43), (Sat.Literal.pos 45)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.pos 43), (Sat.Literal.neg 45)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.neg 43), (Sat.Literal.neg 45), (Sat.Literal.pos 2759)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2758), (Sat.Literal.pos 43), (Sat.Literal.pos 45), (Sat.Literal.pos 2759)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2759) = lexBefore s permutation1 42 := by
  exact (positive_lex_of_descriptor s 2759 permutation1 43 (by rfl)).trans ((lex_skipped s permutation1 42 43 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation1 42) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation1 42 by rw [image1_eq]; rfl))

theorem lex_1_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2760) (Sat.Literal.pos 2759) (Sat.Literal.pos 42) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation1 42 (assignment s)
    (Sat.Literal.pos 2760) (Sat.Literal.pos 2759) (Sat.Literal.pos 42) (Sat.Literal.pos 44) (positive_of_descriptor s 2760 (.lex permutation1 42) (by rfl)) (lex_1_42_prefix s) (positive_select s 42) (lex_1_42_image s)

theorem lex_1_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.pos 42), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation1 42 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2759) (Sat.Literal.pos 42) (Sat.Literal.pos 44) (lex_1_42_prefix s) (positive_select s 42) (lex_1_42_image s)

theorem lex_1_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.pos 2759)] :=
  (lex_1_42_gate s).prop _ (List.Mem.head _)

theorem lex_1_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.neg 42), (Sat.Literal.pos 44)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.pos 42), (Sat.Literal.neg 44)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.neg 42), (Sat.Literal.neg 44), (Sat.Literal.pos 2760)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2759), (Sat.Literal.pos 42), (Sat.Literal.pos 44), (Sat.Literal.pos 2760)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2760) = lexBefore s permutation1 37 := by
  exact (positive_lex_of_descriptor s 2760 permutation1 42 (by rfl)).trans ((lex_skipped s permutation1 37 42 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 38 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation1 37) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation1 37 by rw [image1_eq]; rfl))

theorem lex_1_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2761) (Sat.Literal.pos 2760) (Sat.Literal.pos 37) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation1 37 (assignment s)
    (Sat.Literal.pos 2761) (Sat.Literal.pos 2760) (Sat.Literal.pos 37) (Sat.Literal.pos 35) (positive_of_descriptor s 2761 (.lex permutation1 37) (by rfl)) (lex_1_37_prefix s) (positive_select s 37) (lex_1_37_image s)

theorem lex_1_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.pos 37), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation1 37 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2760) (Sat.Literal.pos 37) (Sat.Literal.pos 35) (lex_1_37_prefix s) (positive_select s 37) (lex_1_37_image s)

theorem lex_1_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.pos 2760)] :=
  (lex_1_37_gate s).prop _ (List.Mem.head _)

theorem lex_1_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.neg 37), (Sat.Literal.pos 35)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.pos 37), (Sat.Literal.neg 35)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.neg 37), (Sat.Literal.neg 35), (Sat.Literal.pos 2761)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2760), (Sat.Literal.pos 37), (Sat.Literal.pos 35), (Sat.Literal.pos 2761)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2761) = lexBefore s permutation1 36 := by
  exact (positive_lex_of_descriptor s 2761 permutation1 37 (by rfl)).trans ((lex_skipped s permutation1 36 37 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation1 36) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation1 36 by rw [image1_eq]; rfl))

theorem lex_1_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2762) (Sat.Literal.pos 2761) (Sat.Literal.pos 36) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation1 36 (assignment s)
    (Sat.Literal.pos 2762) (Sat.Literal.pos 2761) (Sat.Literal.pos 36) (Sat.Literal.pos 34) (positive_of_descriptor s 2762 (.lex permutation1 36) (by rfl)) (lex_1_36_prefix s) (positive_select s 36) (lex_1_36_image s)

theorem lex_1_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.pos 36), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation1 36 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2761) (Sat.Literal.pos 36) (Sat.Literal.pos 34) (lex_1_36_prefix s) (positive_select s 36) (lex_1_36_image s)

theorem lex_1_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.pos 2761)] :=
  (lex_1_36_gate s).prop _ (List.Mem.head _)

theorem lex_1_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.neg 36), (Sat.Literal.pos 34)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.pos 36), (Sat.Literal.neg 34)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.neg 36), (Sat.Literal.neg 34), (Sat.Literal.pos 2762)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2761), (Sat.Literal.pos 36), (Sat.Literal.pos 34), (Sat.Literal.pos 2762)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2762) = lexBefore s permutation1 35 := by
  exact (positive_lex_of_descriptor s 2762 permutation1 36 (by rfl)).trans ((lex_skipped s permutation1 35 36 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation1 35) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation1 35 by rw [image1_eq]; rfl))

theorem lex_1_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2763) (Sat.Literal.pos 2762) (Sat.Literal.pos 35) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation1 35 (assignment s)
    (Sat.Literal.pos 2763) (Sat.Literal.pos 2762) (Sat.Literal.pos 35) (Sat.Literal.pos 37) (positive_of_descriptor s 2763 (.lex permutation1 35) (by rfl)) (lex_1_35_prefix s) (positive_select s 35) (lex_1_35_image s)

theorem lex_1_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.pos 35), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation1 35 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2762) (Sat.Literal.pos 35) (Sat.Literal.pos 37) (lex_1_35_prefix s) (positive_select s 35) (lex_1_35_image s)

theorem lex_1_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.pos 2762)] :=
  (lex_1_35_gate s).prop _ (List.Mem.head _)

theorem lex_1_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.neg 35), (Sat.Literal.pos 37)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.pos 35), (Sat.Literal.neg 37)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.neg 35), (Sat.Literal.neg 37), (Sat.Literal.pos 2763)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2762), (Sat.Literal.pos 35), (Sat.Literal.pos 37), (Sat.Literal.pos 2763)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2763) = lexBefore s permutation1 34 := by
  exact (positive_lex_of_descriptor s 2763 permutation1 35 (by rfl)).trans ((lex_skipped s permutation1 34 35 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation1 34) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation1 34 by rw [image1_eq]; rfl))

theorem lex_1_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2764) (Sat.Literal.pos 2763) (Sat.Literal.pos 34) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation1 34 (assignment s)
    (Sat.Literal.pos 2764) (Sat.Literal.pos 2763) (Sat.Literal.pos 34) (Sat.Literal.pos 36) (positive_of_descriptor s 2764 (.lex permutation1 34) (by rfl)) (lex_1_34_prefix s) (positive_select s 34) (lex_1_34_image s)

theorem lex_1_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.pos 34), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation1 34 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2763) (Sat.Literal.pos 34) (Sat.Literal.pos 36) (lex_1_34_prefix s) (positive_select s 34) (lex_1_34_image s)

theorem lex_1_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.pos 2763)] :=
  (lex_1_34_gate s).prop _ (List.Mem.head _)

theorem lex_1_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.neg 34), (Sat.Literal.pos 36)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.pos 34), (Sat.Literal.neg 36)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.neg 34), (Sat.Literal.neg 36), (Sat.Literal.pos 2764)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2763), (Sat.Literal.pos 34), (Sat.Literal.pos 36), (Sat.Literal.pos 2764)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2764) = lexBefore s permutation1 29 := by
  exact (positive_lex_of_descriptor s 2764 permutation1 34 (by rfl)).trans ((lex_skipped s permutation1 29 34 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 30 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation1 29) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation1 29 by rw [image1_eq]; rfl))

theorem lex_1_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2765) (Sat.Literal.pos 2764) (Sat.Literal.pos 29) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation1 29 (assignment s)
    (Sat.Literal.pos 2765) (Sat.Literal.pos 2764) (Sat.Literal.pos 29) (Sat.Literal.pos 27) (positive_of_descriptor s 2765 (.lex permutation1 29) (by rfl)) (lex_1_29_prefix s) (positive_select s 29) (lex_1_29_image s)

theorem lex_1_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.pos 29), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation1 29 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2764) (Sat.Literal.pos 29) (Sat.Literal.pos 27) (lex_1_29_prefix s) (positive_select s 29) (lex_1_29_image s)

theorem lex_1_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.pos 2764)] :=
  (lex_1_29_gate s).prop _ (List.Mem.head _)

theorem lex_1_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.neg 29), (Sat.Literal.pos 27)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.pos 29), (Sat.Literal.neg 27)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.neg 29), (Sat.Literal.neg 27), (Sat.Literal.pos 2765)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2764), (Sat.Literal.pos 29), (Sat.Literal.pos 27), (Sat.Literal.pos 2765)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2765) = lexBefore s permutation1 28 := by
  exact (positive_lex_of_descriptor s 2765 permutation1 29 (by rfl)).trans ((lex_skipped s permutation1 28 29 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation1 28) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation1 28 by rw [image1_eq]; rfl))

theorem lex_1_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2766) (Sat.Literal.pos 2765) (Sat.Literal.pos 28) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation1 28 (assignment s)
    (Sat.Literal.pos 2766) (Sat.Literal.pos 2765) (Sat.Literal.pos 28) (Sat.Literal.pos 26) (positive_of_descriptor s 2766 (.lex permutation1 28) (by rfl)) (lex_1_28_prefix s) (positive_select s 28) (lex_1_28_image s)

theorem lex_1_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.pos 28), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation1 28 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2765) (Sat.Literal.pos 28) (Sat.Literal.pos 26) (lex_1_28_prefix s) (positive_select s 28) (lex_1_28_image s)

theorem lex_1_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.pos 2765)] :=
  (lex_1_28_gate s).prop _ (List.Mem.head _)

theorem lex_1_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.neg 28), (Sat.Literal.pos 26)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.pos 28), (Sat.Literal.neg 26)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.neg 28), (Sat.Literal.neg 26), (Sat.Literal.pos 2766)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2765), (Sat.Literal.pos 28), (Sat.Literal.pos 26), (Sat.Literal.pos 2766)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2766) = lexBefore s permutation1 27 := by
  exact (positive_lex_of_descriptor s 2766 permutation1 28 (by rfl)).trans ((lex_skipped s permutation1 27 28 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation1 27) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation1 27 by rw [image1_eq]; rfl))

theorem lex_1_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2767) (Sat.Literal.pos 2766) (Sat.Literal.pos 27) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation1 27 (assignment s)
    (Sat.Literal.pos 2767) (Sat.Literal.pos 2766) (Sat.Literal.pos 27) (Sat.Literal.pos 29) (positive_of_descriptor s 2767 (.lex permutation1 27) (by rfl)) (lex_1_27_prefix s) (positive_select s 27) (lex_1_27_image s)

theorem lex_1_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.pos 27), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation1 27 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2766) (Sat.Literal.pos 27) (Sat.Literal.pos 29) (lex_1_27_prefix s) (positive_select s 27) (lex_1_27_image s)

theorem lex_1_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.pos 2766)] :=
  (lex_1_27_gate s).prop _ (List.Mem.head _)

theorem lex_1_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.neg 27), (Sat.Literal.pos 29)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.pos 27), (Sat.Literal.neg 29)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.neg 27), (Sat.Literal.neg 29), (Sat.Literal.pos 2767)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2766), (Sat.Literal.pos 27), (Sat.Literal.pos 29), (Sat.Literal.pos 2767)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2767) = lexBefore s permutation1 26 := by
  exact (positive_lex_of_descriptor s 2767 permutation1 27 (by rfl)).trans ((lex_skipped s permutation1 26 27 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation1 26) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation1 26 by rw [image1_eq]; rfl))

theorem lex_1_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2768) (Sat.Literal.pos 2767) (Sat.Literal.pos 26) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation1 26 (assignment s)
    (Sat.Literal.pos 2768) (Sat.Literal.pos 2767) (Sat.Literal.pos 26) (Sat.Literal.pos 28) (positive_of_descriptor s 2768 (.lex permutation1 26) (by rfl)) (lex_1_26_prefix s) (positive_select s 26) (lex_1_26_image s)

theorem lex_1_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.pos 26), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation1 26 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2767) (Sat.Literal.pos 26) (Sat.Literal.pos 28) (lex_1_26_prefix s) (positive_select s 26) (lex_1_26_image s)

theorem lex_1_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.pos 2767)] :=
  (lex_1_26_gate s).prop _ (List.Mem.head _)

theorem lex_1_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.neg 26), (Sat.Literal.pos 28)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.pos 26), (Sat.Literal.neg 28)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.neg 26), (Sat.Literal.neg 28), (Sat.Literal.pos 2768)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2767), (Sat.Literal.pos 26), (Sat.Literal.pos 28), (Sat.Literal.pos 2768)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2768) = lexBefore s permutation1 21 := by
  exact (positive_lex_of_descriptor s 2768 permutation1 26 (by rfl)).trans ((lex_skipped s permutation1 21 26 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 22 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation1 21) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation1 21 by rw [image1_eq]; rfl))

theorem lex_1_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2769) (Sat.Literal.pos 2768) (Sat.Literal.pos 21) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation1 21 (assignment s)
    (Sat.Literal.pos 2769) (Sat.Literal.pos 2768) (Sat.Literal.pos 21) (Sat.Literal.pos 19) (positive_of_descriptor s 2769 (.lex permutation1 21) (by rfl)) (lex_1_21_prefix s) (positive_select s 21) (lex_1_21_image s)

theorem lex_1_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.pos 21), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation1 21 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2768) (Sat.Literal.pos 21) (Sat.Literal.pos 19) (lex_1_21_prefix s) (positive_select s 21) (lex_1_21_image s)

theorem lex_1_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.pos 2768)] :=
  (lex_1_21_gate s).prop _ (List.Mem.head _)

theorem lex_1_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.neg 21), (Sat.Literal.pos 19)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.pos 21), (Sat.Literal.neg 19)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.neg 21), (Sat.Literal.neg 19), (Sat.Literal.pos 2769)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2768), (Sat.Literal.pos 21), (Sat.Literal.pos 19), (Sat.Literal.pos 2769)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2769) = lexBefore s permutation1 20 := by
  exact (positive_lex_of_descriptor s 2769 permutation1 21 (by rfl)).trans ((lex_skipped s permutation1 20 21 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation1 20) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation1 20 by rw [image1_eq]; rfl))

theorem lex_1_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2770) (Sat.Literal.pos 2769) (Sat.Literal.pos 20) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation1 20 (assignment s)
    (Sat.Literal.pos 2770) (Sat.Literal.pos 2769) (Sat.Literal.pos 20) (Sat.Literal.pos 18) (positive_of_descriptor s 2770 (.lex permutation1 20) (by rfl)) (lex_1_20_prefix s) (positive_select s 20) (lex_1_20_image s)

theorem lex_1_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.pos 20), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation1 20 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2769) (Sat.Literal.pos 20) (Sat.Literal.pos 18) (lex_1_20_prefix s) (positive_select s 20) (lex_1_20_image s)

theorem lex_1_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.pos 2769)] :=
  (lex_1_20_gate s).prop _ (List.Mem.head _)

theorem lex_1_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.neg 20), (Sat.Literal.pos 18)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.pos 20), (Sat.Literal.neg 18)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.neg 20), (Sat.Literal.neg 18), (Sat.Literal.pos 2770)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2769), (Sat.Literal.pos 20), (Sat.Literal.pos 18), (Sat.Literal.pos 2770)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2770) = lexBefore s permutation1 19 := by
  exact (positive_lex_of_descriptor s 2770 permutation1 20 (by rfl)).trans ((lex_skipped s permutation1 19 20 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation1 19) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation1 19 by rw [image1_eq]; rfl))

theorem lex_1_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2771) (Sat.Literal.pos 2770) (Sat.Literal.pos 19) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation1 19 (assignment s)
    (Sat.Literal.pos 2771) (Sat.Literal.pos 2770) (Sat.Literal.pos 19) (Sat.Literal.pos 21) (positive_of_descriptor s 2771 (.lex permutation1 19) (by rfl)) (lex_1_19_prefix s) (positive_select s 19) (lex_1_19_image s)

theorem lex_1_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.pos 19), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation1 19 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2770) (Sat.Literal.pos 19) (Sat.Literal.pos 21) (lex_1_19_prefix s) (positive_select s 19) (lex_1_19_image s)

theorem lex_1_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.pos 2770)] :=
  (lex_1_19_gate s).prop _ (List.Mem.head _)

theorem lex_1_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.neg 19), (Sat.Literal.pos 21)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.pos 19), (Sat.Literal.neg 21)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.neg 19), (Sat.Literal.neg 21), (Sat.Literal.pos 2771)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2770), (Sat.Literal.pos 19), (Sat.Literal.pos 21), (Sat.Literal.pos 2771)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2771) = lexBefore s permutation1 18 := by
  exact (positive_lex_of_descriptor s 2771 permutation1 19 (by rfl)).trans ((lex_skipped s permutation1 18 19 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation1 18) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation1 18 by rw [image1_eq]; rfl))

theorem lex_1_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2772) (Sat.Literal.pos 2771) (Sat.Literal.pos 18) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation1 18 (assignment s)
    (Sat.Literal.pos 2772) (Sat.Literal.pos 2771) (Sat.Literal.pos 18) (Sat.Literal.pos 20) (positive_of_descriptor s 2772 (.lex permutation1 18) (by rfl)) (lex_1_18_prefix s) (positive_select s 18) (lex_1_18_image s)

theorem lex_1_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.pos 18), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation1 18 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2771) (Sat.Literal.pos 18) (Sat.Literal.pos 20) (lex_1_18_prefix s) (positive_select s 18) (lex_1_18_image s)

theorem lex_1_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.pos 2771)] :=
  (lex_1_18_gate s).prop _ (List.Mem.head _)

theorem lex_1_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.neg 18), (Sat.Literal.pos 20)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.pos 18), (Sat.Literal.neg 20)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.neg 18), (Sat.Literal.neg 20), (Sat.Literal.pos 2772)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2771), (Sat.Literal.pos 18), (Sat.Literal.pos 20), (Sat.Literal.pos 2772)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2772) = lexBefore s permutation1 13 := by
  exact (positive_lex_of_descriptor s 2772 permutation1 18 (by rfl)).trans ((lex_skipped s permutation1 13 18 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 14 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation1 13) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation1 13 by rw [image1_eq]; rfl))

theorem lex_1_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2773) (Sat.Literal.pos 2772) (Sat.Literal.pos 13) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation1 13 (assignment s)
    (Sat.Literal.pos 2773) (Sat.Literal.pos 2772) (Sat.Literal.pos 13) (Sat.Literal.pos 11) (positive_of_descriptor s 2773 (.lex permutation1 13) (by rfl)) (lex_1_13_prefix s) (positive_select s 13) (lex_1_13_image s)

theorem lex_1_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.pos 13), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation1 13 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2772) (Sat.Literal.pos 13) (Sat.Literal.pos 11) (lex_1_13_prefix s) (positive_select s 13) (lex_1_13_image s)

theorem lex_1_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.pos 2772)] :=
  (lex_1_13_gate s).prop _ (List.Mem.head _)

theorem lex_1_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.neg 13), (Sat.Literal.pos 11)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.pos 13), (Sat.Literal.neg 11)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.neg 13), (Sat.Literal.neg 11), (Sat.Literal.pos 2773)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2772), (Sat.Literal.pos 13), (Sat.Literal.pos 11), (Sat.Literal.pos 2773)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2773) = lexBefore s permutation1 12 := by
  exact (positive_lex_of_descriptor s 2773 permutation1 13 (by rfl)).trans ((lex_skipped s permutation1 12 13 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation1 12) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation1 12 by rw [image1_eq]; rfl))

theorem lex_1_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2774) (Sat.Literal.pos 2773) (Sat.Literal.pos 12) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation1 12 (assignment s)
    (Sat.Literal.pos 2774) (Sat.Literal.pos 2773) (Sat.Literal.pos 12) (Sat.Literal.pos 10) (positive_of_descriptor s 2774 (.lex permutation1 12) (by rfl)) (lex_1_12_prefix s) (positive_select s 12) (lex_1_12_image s)

theorem lex_1_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.pos 12), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation1 12 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2773) (Sat.Literal.pos 12) (Sat.Literal.pos 10) (lex_1_12_prefix s) (positive_select s 12) (lex_1_12_image s)

theorem lex_1_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.pos 2773)] :=
  (lex_1_12_gate s).prop _ (List.Mem.head _)

theorem lex_1_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.neg 12), (Sat.Literal.pos 10)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.pos 12), (Sat.Literal.neg 10)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.neg 12), (Sat.Literal.neg 10), (Sat.Literal.pos 2774)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2773), (Sat.Literal.pos 12), (Sat.Literal.pos 10), (Sat.Literal.pos 2774)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2774) = lexBefore s permutation1 11 := by
  exact (positive_lex_of_descriptor s 2774 permutation1 12 (by rfl)).trans ((lex_skipped s permutation1 11 12 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation1 11) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation1 11 by rw [image1_eq]; rfl))

theorem lex_1_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2775) (Sat.Literal.pos 2774) (Sat.Literal.pos 11) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation1 11 (assignment s)
    (Sat.Literal.pos 2775) (Sat.Literal.pos 2774) (Sat.Literal.pos 11) (Sat.Literal.pos 13) (positive_of_descriptor s 2775 (.lex permutation1 11) (by rfl)) (lex_1_11_prefix s) (positive_select s 11) (lex_1_11_image s)

theorem lex_1_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.pos 11), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation1 11 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2774) (Sat.Literal.pos 11) (Sat.Literal.pos 13) (lex_1_11_prefix s) (positive_select s 11) (lex_1_11_image s)

theorem lex_1_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.pos 2774)] :=
  (lex_1_11_gate s).prop _ (List.Mem.head _)

theorem lex_1_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.neg 11), (Sat.Literal.pos 13)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.pos 11), (Sat.Literal.neg 13)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.neg 11), (Sat.Literal.neg 13), (Sat.Literal.pos 2775)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2774), (Sat.Literal.pos 11), (Sat.Literal.pos 13), (Sat.Literal.pos 2775)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2775) = lexBefore s permutation1 10 := by
  exact (positive_lex_of_descriptor s 2775 permutation1 11 (by rfl)).trans ((lex_skipped s permutation1 10 11 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation1 10) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation1 10 by rw [image1_eq]; rfl))

theorem lex_1_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2776) (Sat.Literal.pos 2775) (Sat.Literal.pos 10) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation1 10 (assignment s)
    (Sat.Literal.pos 2776) (Sat.Literal.pos 2775) (Sat.Literal.pos 10) (Sat.Literal.pos 12) (positive_of_descriptor s 2776 (.lex permutation1 10) (by rfl)) (lex_1_10_prefix s) (positive_select s 10) (lex_1_10_image s)

theorem lex_1_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.pos 10), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation1 10 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2775) (Sat.Literal.pos 10) (Sat.Literal.pos 12) (lex_1_10_prefix s) (positive_select s 10) (lex_1_10_image s)

theorem lex_1_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.pos 2775)] :=
  (lex_1_10_gate s).prop _ (List.Mem.head _)

theorem lex_1_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.neg 10), (Sat.Literal.pos 12)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.pos 10), (Sat.Literal.neg 12)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.neg 10), (Sat.Literal.neg 12), (Sat.Literal.pos 2776)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2775), (Sat.Literal.pos 10), (Sat.Literal.pos 12), (Sat.Literal.pos 2776)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2776) = lexBefore s permutation1 5 := by
  exact (positive_lex_of_descriptor s 2776 permutation1 10 (by rfl)).trans ((lex_skipped s permutation1 5 10 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 6 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation1 5) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation1 5 by rw [image1_eq]; rfl))

theorem lex_1_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2777) (Sat.Literal.pos 2776) (Sat.Literal.pos 5) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation1 5 (assignment s)
    (Sat.Literal.pos 2777) (Sat.Literal.pos 2776) (Sat.Literal.pos 5) (Sat.Literal.pos 3) (positive_of_descriptor s 2777 (.lex permutation1 5) (by rfl)) (lex_1_5_prefix s) (positive_select s 5) (lex_1_5_image s)

theorem lex_1_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.pos 5), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation1 5 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2776) (Sat.Literal.pos 5) (Sat.Literal.pos 3) (lex_1_5_prefix s) (positive_select s 5) (lex_1_5_image s)

theorem lex_1_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.pos 2776)] :=
  (lex_1_5_gate s).prop _ (List.Mem.head _)

theorem lex_1_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.neg 5), (Sat.Literal.pos 3)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.pos 5), (Sat.Literal.neg 3)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.neg 5), (Sat.Literal.neg 3), (Sat.Literal.pos 2777)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2776), (Sat.Literal.pos 5), (Sat.Literal.pos 3), (Sat.Literal.pos 2777)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2777) = lexBefore s permutation1 4 := by
  exact (positive_lex_of_descriptor s 2777 permutation1 5 (by rfl)).trans ((lex_skipped s permutation1 4 5 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation1 4) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation1 4 by rw [image1_eq]; rfl))

theorem lex_1_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2778) (Sat.Literal.pos 2777) (Sat.Literal.pos 4) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation1 4 (assignment s)
    (Sat.Literal.pos 2778) (Sat.Literal.pos 2777) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (positive_of_descriptor s 2778 (.lex permutation1 4) (by rfl)) (lex_1_4_prefix s) (positive_select s 4) (lex_1_4_image s)

theorem lex_1_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation1 4 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2777) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (lex_1_4_prefix s) (positive_select s 4) (lex_1_4_image s)

theorem lex_1_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.pos 2777)] :=
  (lex_1_4_gate s).prop _ (List.Mem.head _)

theorem lex_1_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.neg 4), (Sat.Literal.pos 2)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.neg 4), (Sat.Literal.neg 2), (Sat.Literal.pos 2778)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2777), (Sat.Literal.pos 4), (Sat.Literal.pos 2), (Sat.Literal.pos 2778)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2778) = lexBefore s permutation1 3 := by
  exact (positive_lex_of_descriptor s 2778 permutation1 4 (by rfl)).trans ((lex_skipped s permutation1 3 4 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation1 3) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation1 3 by rw [image1_eq]; rfl))

theorem lex_1_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2779) (Sat.Literal.pos 2778) (Sat.Literal.pos 3) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation1 3 (assignment s)
    (Sat.Literal.pos 2779) (Sat.Literal.pos 2778) (Sat.Literal.pos 3) (Sat.Literal.pos 5) (positive_of_descriptor s 2779 (.lex permutation1 3) (by rfl)) (lex_1_3_prefix s) (positive_select s 3) (lex_1_3_image s)

theorem lex_1_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.pos 3), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation1 3 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2778) (Sat.Literal.pos 3) (Sat.Literal.pos 5) (lex_1_3_prefix s) (positive_select s 3) (lex_1_3_image s)

theorem lex_1_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.pos 2778)] :=
  (lex_1_3_gate s).prop _ (List.Mem.head _)

theorem lex_1_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.neg 3), (Sat.Literal.pos 5)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.pos 3), (Sat.Literal.neg 5)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.neg 3), (Sat.Literal.neg 5), (Sat.Literal.pos 2779)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2778), (Sat.Literal.pos 3), (Sat.Literal.pos 5), (Sat.Literal.pos 2779)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2779) = lexBefore s permutation1 2 := by
  exact (positive_lex_of_descriptor s 2779 permutation1 3 (by rfl)).trans ((lex_skipped s permutation1 2 3 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation1 2) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation1 2 by rw [image1_eq]; rfl))

theorem lex_1_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2780) (Sat.Literal.pos 2779) (Sat.Literal.pos 2) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation1 2 (assignment s)
    (Sat.Literal.pos 2780) (Sat.Literal.pos 2779) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (positive_of_descriptor s 2780 (.lex permutation1 2) (by rfl)) (lex_1_2_prefix s) (positive_select s 2) (lex_1_2_image s)

theorem lex_1_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation1 2 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2779) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (lex_1_2_prefix s) (positive_select s 2) (lex_1_2_image s)

theorem lex_1_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2780), (Sat.Literal.pos 2779)] :=
  (lex_1_2_gate s).prop _ (List.Mem.head _)

theorem lex_1_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2780), (Sat.Literal.neg 2), (Sat.Literal.pos 4)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2780), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.neg 2), (Sat.Literal.neg 4), (Sat.Literal.pos 2780)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2779), (Sat.Literal.pos 2), (Sat.Literal.pos 4), (Sat.Literal.pos 2780)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation2 251 := by
  exact (negative_falsum s).trans ((lex_first s permutation2 251 (by intro j hj; rw [image2_eq]; exact fixedOnRange_spec image2 252 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_2_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation2 251) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation2 251 by rw [image2_eq]; rfl))

theorem lex_2_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2781) (Sat.Literal.neg 256) (Sat.Literal.pos 251) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation2 251 (assignment s)
    (Sat.Literal.pos 2781) (Sat.Literal.neg 256) (Sat.Literal.pos 251) (Sat.Literal.pos 247) (positive_of_descriptor s 2781 (.lex permutation2 251) (by rfl)) (lex_2_251_prefix s) (positive_select s 251) (lex_2_251_image s)

theorem lex_2_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 251), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation2 251 (hmax permutation2) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 251) (Sat.Literal.pos 247) (lex_2_251_prefix s) (positive_select s 251) (lex_2_251_image s)

theorem lex_2_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.neg 256)] :=
  (lex_2_251_gate s).prop _ (List.Mem.head _)

theorem lex_2_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.neg 251), (Sat.Literal.pos 247)] :=
  (lex_2_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.pos 251), (Sat.Literal.neg 247)] :=
  (lex_2_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 251), (Sat.Literal.neg 247), (Sat.Literal.pos 2781)] :=
  (lex_2_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 251), (Sat.Literal.pos 247), (Sat.Literal.pos 2781)] :=
  (lex_2_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2781) = lexBefore s permutation2 250 := by
  exact (positive_lex_of_descriptor s 2781 permutation2 251 (by rfl)).trans ((lex_skipped s permutation2 250 251 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation2 250) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation2 250 by rw [image2_eq]; rfl))

theorem lex_2_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2782) (Sat.Literal.pos 2781) (Sat.Literal.pos 250) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation2 250 (assignment s)
    (Sat.Literal.pos 2782) (Sat.Literal.pos 2781) (Sat.Literal.pos 250) (Sat.Literal.pos 246) (positive_of_descriptor s 2782 (.lex permutation2 250) (by rfl)) (lex_2_250_prefix s) (positive_select s 250) (lex_2_250_image s)

theorem lex_2_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.pos 250), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation2 250 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2781) (Sat.Literal.pos 250) (Sat.Literal.pos 246) (lex_2_250_prefix s) (positive_select s 250) (lex_2_250_image s)

theorem lex_2_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.pos 2781)] :=
  (lex_2_250_gate s).prop _ (List.Mem.head _)

theorem lex_2_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.neg 250), (Sat.Literal.pos 246)] :=
  (lex_2_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.pos 250), (Sat.Literal.neg 246)] :=
  (lex_2_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.neg 250), (Sat.Literal.neg 246), (Sat.Literal.pos 2782)] :=
  (lex_2_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2781), (Sat.Literal.pos 250), (Sat.Literal.pos 246), (Sat.Literal.pos 2782)] :=
  (lex_2_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2782) = lexBefore s permutation2 249 := by
  exact (positive_lex_of_descriptor s 2782 permutation2 250 (by rfl)).trans ((lex_skipped s permutation2 249 250 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation2 249) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation2 249 by rw [image2_eq]; rfl))

theorem lex_2_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2783) (Sat.Literal.pos 2782) (Sat.Literal.pos 249) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation2 249 (assignment s)
    (Sat.Literal.pos 2783) (Sat.Literal.pos 2782) (Sat.Literal.pos 249) (Sat.Literal.pos 245) (positive_of_descriptor s 2783 (.lex permutation2 249) (by rfl)) (lex_2_249_prefix s) (positive_select s 249) (lex_2_249_image s)

theorem lex_2_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.pos 249), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation2 249 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2782) (Sat.Literal.pos 249) (Sat.Literal.pos 245) (lex_2_249_prefix s) (positive_select s 249) (lex_2_249_image s)

theorem lex_2_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.pos 2782)] :=
  (lex_2_249_gate s).prop _ (List.Mem.head _)

theorem lex_2_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.neg 249), (Sat.Literal.pos 245)] :=
  (lex_2_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.pos 249), (Sat.Literal.neg 245)] :=
  (lex_2_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.neg 249), (Sat.Literal.neg 245), (Sat.Literal.pos 2783)] :=
  (lex_2_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2782), (Sat.Literal.pos 249), (Sat.Literal.pos 245), (Sat.Literal.pos 2783)] :=
  (lex_2_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2783) = lexBefore s permutation2 248 := by
  exact (positive_lex_of_descriptor s 2783 permutation2 249 (by rfl)).trans ((lex_skipped s permutation2 248 249 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation2 248) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation2 248 by rw [image2_eq]; rfl))

theorem lex_2_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2784) (Sat.Literal.pos 2783) (Sat.Literal.pos 248) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation2 248 (assignment s)
    (Sat.Literal.pos 2784) (Sat.Literal.pos 2783) (Sat.Literal.pos 248) (Sat.Literal.pos 244) (positive_of_descriptor s 2784 (.lex permutation2 248) (by rfl)) (lex_2_248_prefix s) (positive_select s 248) (lex_2_248_image s)

theorem lex_2_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.pos 248), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation2 248 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2783) (Sat.Literal.pos 248) (Sat.Literal.pos 244) (lex_2_248_prefix s) (positive_select s 248) (lex_2_248_image s)

theorem lex_2_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.pos 2783)] :=
  (lex_2_248_gate s).prop _ (List.Mem.head _)

theorem lex_2_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.neg 248), (Sat.Literal.pos 244)] :=
  (lex_2_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.pos 248), (Sat.Literal.neg 244)] :=
  (lex_2_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.neg 248), (Sat.Literal.neg 244), (Sat.Literal.pos 2784)] :=
  (lex_2_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2783), (Sat.Literal.pos 248), (Sat.Literal.pos 244), (Sat.Literal.pos 2784)] :=
  (lex_2_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2784) = lexBefore s permutation2 247 := by
  exact (positive_lex_of_descriptor s 2784 permutation2 248 (by rfl)).trans ((lex_skipped s permutation2 247 248 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation2 247) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation2 247 by rw [image2_eq]; rfl))

theorem lex_2_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2785) (Sat.Literal.pos 2784) (Sat.Literal.pos 247) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation2 247 (assignment s)
    (Sat.Literal.pos 2785) (Sat.Literal.pos 2784) (Sat.Literal.pos 247) (Sat.Literal.pos 251) (positive_of_descriptor s 2785 (.lex permutation2 247) (by rfl)) (lex_2_247_prefix s) (positive_select s 247) (lex_2_247_image s)

theorem lex_2_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.pos 247), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation2 247 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2784) (Sat.Literal.pos 247) (Sat.Literal.pos 251) (lex_2_247_prefix s) (positive_select s 247) (lex_2_247_image s)

theorem lex_2_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.pos 2784)] :=
  (lex_2_247_gate s).prop _ (List.Mem.head _)

theorem lex_2_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.neg 247), (Sat.Literal.pos 251)] :=
  (lex_2_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.pos 247), (Sat.Literal.neg 251)] :=
  (lex_2_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.neg 247), (Sat.Literal.neg 251), (Sat.Literal.pos 2785)] :=
  (lex_2_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2784), (Sat.Literal.pos 247), (Sat.Literal.pos 251), (Sat.Literal.pos 2785)] :=
  (lex_2_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2785) = lexBefore s permutation2 246 := by
  exact (positive_lex_of_descriptor s 2785 permutation2 247 (by rfl)).trans ((lex_skipped s permutation2 246 247 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation2 246) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation2 246 by rw [image2_eq]; rfl))

theorem lex_2_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2786) (Sat.Literal.pos 2785) (Sat.Literal.pos 246) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation2 246 (assignment s)
    (Sat.Literal.pos 2786) (Sat.Literal.pos 2785) (Sat.Literal.pos 246) (Sat.Literal.pos 250) (positive_of_descriptor s 2786 (.lex permutation2 246) (by rfl)) (lex_2_246_prefix s) (positive_select s 246) (lex_2_246_image s)

theorem lex_2_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.pos 246), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation2 246 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2785) (Sat.Literal.pos 246) (Sat.Literal.pos 250) (lex_2_246_prefix s) (positive_select s 246) (lex_2_246_image s)

theorem lex_2_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.pos 2785)] :=
  (lex_2_246_gate s).prop _ (List.Mem.head _)

theorem lex_2_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.neg 246), (Sat.Literal.pos 250)] :=
  (lex_2_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.pos 246), (Sat.Literal.neg 250)] :=
  (lex_2_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.neg 246), (Sat.Literal.neg 250), (Sat.Literal.pos 2786)] :=
  (lex_2_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2785), (Sat.Literal.pos 246), (Sat.Literal.pos 250), (Sat.Literal.pos 2786)] :=
  (lex_2_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2786) = lexBefore s permutation2 245 := by
  exact (positive_lex_of_descriptor s 2786 permutation2 246 (by rfl)).trans ((lex_skipped s permutation2 245 246 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation2 245) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation2 245 by rw [image2_eq]; rfl))

theorem lex_2_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2787) (Sat.Literal.pos 2786) (Sat.Literal.pos 245) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation2 245 (assignment s)
    (Sat.Literal.pos 2787) (Sat.Literal.pos 2786) (Sat.Literal.pos 245) (Sat.Literal.pos 249) (positive_of_descriptor s 2787 (.lex permutation2 245) (by rfl)) (lex_2_245_prefix s) (positive_select s 245) (lex_2_245_image s)

theorem lex_2_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.pos 245), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation2 245 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2786) (Sat.Literal.pos 245) (Sat.Literal.pos 249) (lex_2_245_prefix s) (positive_select s 245) (lex_2_245_image s)

theorem lex_2_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.pos 2786)] :=
  (lex_2_245_gate s).prop _ (List.Mem.head _)

theorem lex_2_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.neg 245), (Sat.Literal.pos 249)] :=
  (lex_2_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.pos 245), (Sat.Literal.neg 249)] :=
  (lex_2_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.neg 245), (Sat.Literal.neg 249), (Sat.Literal.pos 2787)] :=
  (lex_2_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2786), (Sat.Literal.pos 245), (Sat.Literal.pos 249), (Sat.Literal.pos 2787)] :=
  (lex_2_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2787) = lexBefore s permutation2 244 := by
  exact (positive_lex_of_descriptor s 2787 permutation2 245 (by rfl)).trans ((lex_skipped s permutation2 244 245 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation2 244) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation2 244 by rw [image2_eq]; rfl))

theorem lex_2_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2788) (Sat.Literal.pos 2787) (Sat.Literal.pos 244) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation2 244 (assignment s)
    (Sat.Literal.pos 2788) (Sat.Literal.pos 2787) (Sat.Literal.pos 244) (Sat.Literal.pos 248) (positive_of_descriptor s 2788 (.lex permutation2 244) (by rfl)) (lex_2_244_prefix s) (positive_select s 244) (lex_2_244_image s)

theorem lex_2_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.pos 244), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation2 244 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2787) (Sat.Literal.pos 244) (Sat.Literal.pos 248) (lex_2_244_prefix s) (positive_select s 244) (lex_2_244_image s)

theorem lex_2_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.pos 2787)] :=
  (lex_2_244_gate s).prop _ (List.Mem.head _)

theorem lex_2_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.neg 244), (Sat.Literal.pos 248)] :=
  (lex_2_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.pos 244), (Sat.Literal.neg 248)] :=
  (lex_2_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.neg 244), (Sat.Literal.neg 248), (Sat.Literal.pos 2788)] :=
  (lex_2_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2787), (Sat.Literal.pos 244), (Sat.Literal.pos 248), (Sat.Literal.pos 2788)] :=
  (lex_2_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2788) = lexBefore s permutation2 235 := by
  exact (positive_lex_of_descriptor s 2788 permutation2 244 (by rfl)).trans ((lex_skipped s permutation2 235 244 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 236 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation2 235) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation2 235 by rw [image2_eq]; rfl))

theorem lex_2_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2789) (Sat.Literal.pos 2788) (Sat.Literal.pos 235) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation2 235 (assignment s)
    (Sat.Literal.pos 2789) (Sat.Literal.pos 2788) (Sat.Literal.pos 235) (Sat.Literal.pos 231) (positive_of_descriptor s 2789 (.lex permutation2 235) (by rfl)) (lex_2_235_prefix s) (positive_select s 235) (lex_2_235_image s)

theorem lex_2_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.pos 235), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation2 235 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2788) (Sat.Literal.pos 235) (Sat.Literal.pos 231) (lex_2_235_prefix s) (positive_select s 235) (lex_2_235_image s)

theorem lex_2_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.pos 2788)] :=
  (lex_2_235_gate s).prop _ (List.Mem.head _)

theorem lex_2_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.neg 235), (Sat.Literal.pos 231)] :=
  (lex_2_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.pos 235), (Sat.Literal.neg 231)] :=
  (lex_2_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.neg 235), (Sat.Literal.neg 231), (Sat.Literal.pos 2789)] :=
  (lex_2_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2788), (Sat.Literal.pos 235), (Sat.Literal.pos 231), (Sat.Literal.pos 2789)] :=
  (lex_2_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2789) = lexBefore s permutation2 234 := by
  exact (positive_lex_of_descriptor s 2789 permutation2 235 (by rfl)).trans ((lex_skipped s permutation2 234 235 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation2 234) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation2 234 by rw [image2_eq]; rfl))

theorem lex_2_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2790) (Sat.Literal.pos 2789) (Sat.Literal.pos 234) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation2 234 (assignment s)
    (Sat.Literal.pos 2790) (Sat.Literal.pos 2789) (Sat.Literal.pos 234) (Sat.Literal.pos 230) (positive_of_descriptor s 2790 (.lex permutation2 234) (by rfl)) (lex_2_234_prefix s) (positive_select s 234) (lex_2_234_image s)

theorem lex_2_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.pos 234), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation2 234 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2789) (Sat.Literal.pos 234) (Sat.Literal.pos 230) (lex_2_234_prefix s) (positive_select s 234) (lex_2_234_image s)

theorem lex_2_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.pos 2789)] :=
  (lex_2_234_gate s).prop _ (List.Mem.head _)

theorem lex_2_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.neg 234), (Sat.Literal.pos 230)] :=
  (lex_2_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.pos 234), (Sat.Literal.neg 230)] :=
  (lex_2_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.neg 234), (Sat.Literal.neg 230), (Sat.Literal.pos 2790)] :=
  (lex_2_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2789), (Sat.Literal.pos 234), (Sat.Literal.pos 230), (Sat.Literal.pos 2790)] :=
  (lex_2_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2790) = lexBefore s permutation2 233 := by
  exact (positive_lex_of_descriptor s 2790 permutation2 234 (by rfl)).trans ((lex_skipped s permutation2 233 234 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation2 233) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation2 233 by rw [image2_eq]; rfl))

theorem lex_2_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2791) (Sat.Literal.pos 2790) (Sat.Literal.pos 233) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation2 233 (assignment s)
    (Sat.Literal.pos 2791) (Sat.Literal.pos 2790) (Sat.Literal.pos 233) (Sat.Literal.pos 229) (positive_of_descriptor s 2791 (.lex permutation2 233) (by rfl)) (lex_2_233_prefix s) (positive_select s 233) (lex_2_233_image s)

theorem lex_2_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.pos 233), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation2 233 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2790) (Sat.Literal.pos 233) (Sat.Literal.pos 229) (lex_2_233_prefix s) (positive_select s 233) (lex_2_233_image s)

theorem lex_2_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.pos 2790)] :=
  (lex_2_233_gate s).prop _ (List.Mem.head _)

theorem lex_2_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.neg 233), (Sat.Literal.pos 229)] :=
  (lex_2_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.pos 233), (Sat.Literal.neg 229)] :=
  (lex_2_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.neg 233), (Sat.Literal.neg 229), (Sat.Literal.pos 2791)] :=
  (lex_2_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2790), (Sat.Literal.pos 233), (Sat.Literal.pos 229), (Sat.Literal.pos 2791)] :=
  (lex_2_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2791) = lexBefore s permutation2 232 := by
  exact (positive_lex_of_descriptor s 2791 permutation2 233 (by rfl)).trans ((lex_skipped s permutation2 232 233 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation2 232) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation2 232 by rw [image2_eq]; rfl))

theorem lex_2_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2792) (Sat.Literal.pos 2791) (Sat.Literal.pos 232) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation2 232 (assignment s)
    (Sat.Literal.pos 2792) (Sat.Literal.pos 2791) (Sat.Literal.pos 232) (Sat.Literal.pos 228) (positive_of_descriptor s 2792 (.lex permutation2 232) (by rfl)) (lex_2_232_prefix s) (positive_select s 232) (lex_2_232_image s)

theorem lex_2_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.pos 232), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation2 232 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2791) (Sat.Literal.pos 232) (Sat.Literal.pos 228) (lex_2_232_prefix s) (positive_select s 232) (lex_2_232_image s)

theorem lex_2_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.pos 2791)] :=
  (lex_2_232_gate s).prop _ (List.Mem.head _)

theorem lex_2_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.neg 232), (Sat.Literal.pos 228)] :=
  (lex_2_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.pos 232), (Sat.Literal.neg 228)] :=
  (lex_2_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.neg 232), (Sat.Literal.neg 228), (Sat.Literal.pos 2792)] :=
  (lex_2_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2791), (Sat.Literal.pos 232), (Sat.Literal.pos 228), (Sat.Literal.pos 2792)] :=
  (lex_2_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2792) = lexBefore s permutation2 231 := by
  exact (positive_lex_of_descriptor s 2792 permutation2 232 (by rfl)).trans ((lex_skipped s permutation2 231 232 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation2 231) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation2 231 by rw [image2_eq]; rfl))

theorem lex_2_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2793) (Sat.Literal.pos 2792) (Sat.Literal.pos 231) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation2 231 (assignment s)
    (Sat.Literal.pos 2793) (Sat.Literal.pos 2792) (Sat.Literal.pos 231) (Sat.Literal.pos 235) (positive_of_descriptor s 2793 (.lex permutation2 231) (by rfl)) (lex_2_231_prefix s) (positive_select s 231) (lex_2_231_image s)

theorem lex_2_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.pos 231), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation2 231 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2792) (Sat.Literal.pos 231) (Sat.Literal.pos 235) (lex_2_231_prefix s) (positive_select s 231) (lex_2_231_image s)

theorem lex_2_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.pos 2792)] :=
  (lex_2_231_gate s).prop _ (List.Mem.head _)

theorem lex_2_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.neg 231), (Sat.Literal.pos 235)] :=
  (lex_2_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.pos 231), (Sat.Literal.neg 235)] :=
  (lex_2_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.neg 231), (Sat.Literal.neg 235), (Sat.Literal.pos 2793)] :=
  (lex_2_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2792), (Sat.Literal.pos 231), (Sat.Literal.pos 235), (Sat.Literal.pos 2793)] :=
  (lex_2_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2793) = lexBefore s permutation2 230 := by
  exact (positive_lex_of_descriptor s 2793 permutation2 231 (by rfl)).trans ((lex_skipped s permutation2 230 231 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation2 230) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation2 230 by rw [image2_eq]; rfl))

theorem lex_2_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2794) (Sat.Literal.pos 2793) (Sat.Literal.pos 230) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation2 230 (assignment s)
    (Sat.Literal.pos 2794) (Sat.Literal.pos 2793) (Sat.Literal.pos 230) (Sat.Literal.pos 234) (positive_of_descriptor s 2794 (.lex permutation2 230) (by rfl)) (lex_2_230_prefix s) (positive_select s 230) (lex_2_230_image s)

theorem lex_2_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.pos 230), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation2 230 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2793) (Sat.Literal.pos 230) (Sat.Literal.pos 234) (lex_2_230_prefix s) (positive_select s 230) (lex_2_230_image s)

theorem lex_2_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.pos 2793)] :=
  (lex_2_230_gate s).prop _ (List.Mem.head _)

theorem lex_2_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.neg 230), (Sat.Literal.pos 234)] :=
  (lex_2_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.pos 230), (Sat.Literal.neg 234)] :=
  (lex_2_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.neg 230), (Sat.Literal.neg 234), (Sat.Literal.pos 2794)] :=
  (lex_2_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2793), (Sat.Literal.pos 230), (Sat.Literal.pos 234), (Sat.Literal.pos 2794)] :=
  (lex_2_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2794) = lexBefore s permutation2 229 := by
  exact (positive_lex_of_descriptor s 2794 permutation2 230 (by rfl)).trans ((lex_skipped s permutation2 229 230 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation2 229) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation2 229 by rw [image2_eq]; rfl))

theorem lex_2_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2795) (Sat.Literal.pos 2794) (Sat.Literal.pos 229) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation2 229 (assignment s)
    (Sat.Literal.pos 2795) (Sat.Literal.pos 2794) (Sat.Literal.pos 229) (Sat.Literal.pos 233) (positive_of_descriptor s 2795 (.lex permutation2 229) (by rfl)) (lex_2_229_prefix s) (positive_select s 229) (lex_2_229_image s)

theorem lex_2_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.pos 229), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation2 229 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2794) (Sat.Literal.pos 229) (Sat.Literal.pos 233) (lex_2_229_prefix s) (positive_select s 229) (lex_2_229_image s)

theorem lex_2_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.pos 2794)] :=
  (lex_2_229_gate s).prop _ (List.Mem.head _)

theorem lex_2_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.neg 229), (Sat.Literal.pos 233)] :=
  (lex_2_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.pos 229), (Sat.Literal.neg 233)] :=
  (lex_2_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.neg 229), (Sat.Literal.neg 233), (Sat.Literal.pos 2795)] :=
  (lex_2_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2794), (Sat.Literal.pos 229), (Sat.Literal.pos 233), (Sat.Literal.pos 2795)] :=
  (lex_2_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2795) = lexBefore s permutation2 228 := by
  exact (positive_lex_of_descriptor s 2795 permutation2 229 (by rfl)).trans ((lex_skipped s permutation2 228 229 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation2 228) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation2 228 by rw [image2_eq]; rfl))

theorem lex_2_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2796) (Sat.Literal.pos 2795) (Sat.Literal.pos 228) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation2 228 (assignment s)
    (Sat.Literal.pos 2796) (Sat.Literal.pos 2795) (Sat.Literal.pos 228) (Sat.Literal.pos 232) (positive_of_descriptor s 2796 (.lex permutation2 228) (by rfl)) (lex_2_228_prefix s) (positive_select s 228) (lex_2_228_image s)

theorem lex_2_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.pos 228), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation2 228 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2795) (Sat.Literal.pos 228) (Sat.Literal.pos 232) (lex_2_228_prefix s) (positive_select s 228) (lex_2_228_image s)

theorem lex_2_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.pos 2795)] :=
  (lex_2_228_gate s).prop _ (List.Mem.head _)

theorem lex_2_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.neg 228), (Sat.Literal.pos 232)] :=
  (lex_2_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.pos 228), (Sat.Literal.neg 232)] :=
  (lex_2_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.neg 228), (Sat.Literal.neg 232), (Sat.Literal.pos 2796)] :=
  (lex_2_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2795), (Sat.Literal.pos 228), (Sat.Literal.pos 232), (Sat.Literal.pos 2796)] :=
  (lex_2_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2796) = lexBefore s permutation2 219 := by
  exact (positive_lex_of_descriptor s 2796 permutation2 228 (by rfl)).trans ((lex_skipped s permutation2 219 228 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 220 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation2 219) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation2 219 by rw [image2_eq]; rfl))

theorem lex_2_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2797) (Sat.Literal.pos 2796) (Sat.Literal.pos 219) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation2 219 (assignment s)
    (Sat.Literal.pos 2797) (Sat.Literal.pos 2796) (Sat.Literal.pos 219) (Sat.Literal.pos 215) (positive_of_descriptor s 2797 (.lex permutation2 219) (by rfl)) (lex_2_219_prefix s) (positive_select s 219) (lex_2_219_image s)

theorem lex_2_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.pos 219), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation2 219 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2796) (Sat.Literal.pos 219) (Sat.Literal.pos 215) (lex_2_219_prefix s) (positive_select s 219) (lex_2_219_image s)

theorem lex_2_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.pos 2796)] :=
  (lex_2_219_gate s).prop _ (List.Mem.head _)

theorem lex_2_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.neg 219), (Sat.Literal.pos 215)] :=
  (lex_2_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.pos 219), (Sat.Literal.neg 215)] :=
  (lex_2_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.neg 219), (Sat.Literal.neg 215), (Sat.Literal.pos 2797)] :=
  (lex_2_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2796), (Sat.Literal.pos 219), (Sat.Literal.pos 215), (Sat.Literal.pos 2797)] :=
  (lex_2_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2797) = lexBefore s permutation2 218 := by
  exact (positive_lex_of_descriptor s 2797 permutation2 219 (by rfl)).trans ((lex_skipped s permutation2 218 219 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation2 218) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation2 218 by rw [image2_eq]; rfl))

theorem lex_2_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2798) (Sat.Literal.pos 2797) (Sat.Literal.pos 218) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation2 218 (assignment s)
    (Sat.Literal.pos 2798) (Sat.Literal.pos 2797) (Sat.Literal.pos 218) (Sat.Literal.pos 214) (positive_of_descriptor s 2798 (.lex permutation2 218) (by rfl)) (lex_2_218_prefix s) (positive_select s 218) (lex_2_218_image s)

theorem lex_2_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.pos 218), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation2 218 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2797) (Sat.Literal.pos 218) (Sat.Literal.pos 214) (lex_2_218_prefix s) (positive_select s 218) (lex_2_218_image s)

theorem lex_2_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.pos 2797)] :=
  (lex_2_218_gate s).prop _ (List.Mem.head _)

theorem lex_2_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.neg 218), (Sat.Literal.pos 214)] :=
  (lex_2_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.pos 218), (Sat.Literal.neg 214)] :=
  (lex_2_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.neg 218), (Sat.Literal.neg 214), (Sat.Literal.pos 2798)] :=
  (lex_2_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2797), (Sat.Literal.pos 218), (Sat.Literal.pos 214), (Sat.Literal.pos 2798)] :=
  (lex_2_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2798) = lexBefore s permutation2 217 := by
  exact (positive_lex_of_descriptor s 2798 permutation2 218 (by rfl)).trans ((lex_skipped s permutation2 217 218 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation2 217) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation2 217 by rw [image2_eq]; rfl))

theorem lex_2_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2799) (Sat.Literal.pos 2798) (Sat.Literal.pos 217) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation2 217 (assignment s)
    (Sat.Literal.pos 2799) (Sat.Literal.pos 2798) (Sat.Literal.pos 217) (Sat.Literal.pos 213) (positive_of_descriptor s 2799 (.lex permutation2 217) (by rfl)) (lex_2_217_prefix s) (positive_select s 217) (lex_2_217_image s)

theorem lex_2_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.pos 217), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation2 217 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2798) (Sat.Literal.pos 217) (Sat.Literal.pos 213) (lex_2_217_prefix s) (positive_select s 217) (lex_2_217_image s)

theorem lex_2_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.pos 2798)] :=
  (lex_2_217_gate s).prop _ (List.Mem.head _)

theorem lex_2_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.neg 217), (Sat.Literal.pos 213)] :=
  (lex_2_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.pos 217), (Sat.Literal.neg 213)] :=
  (lex_2_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.neg 217), (Sat.Literal.neg 213), (Sat.Literal.pos 2799)] :=
  (lex_2_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2798), (Sat.Literal.pos 217), (Sat.Literal.pos 213), (Sat.Literal.pos 2799)] :=
  (lex_2_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2799) = lexBefore s permutation2 216 := by
  exact (positive_lex_of_descriptor s 2799 permutation2 217 (by rfl)).trans ((lex_skipped s permutation2 216 217 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation2 216) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation2 216 by rw [image2_eq]; rfl))

theorem lex_2_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2800) (Sat.Literal.pos 2799) (Sat.Literal.pos 216) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation2 216 (assignment s)
    (Sat.Literal.pos 2800) (Sat.Literal.pos 2799) (Sat.Literal.pos 216) (Sat.Literal.pos 212) (positive_of_descriptor s 2800 (.lex permutation2 216) (by rfl)) (lex_2_216_prefix s) (positive_select s 216) (lex_2_216_image s)

theorem lex_2_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.pos 216), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation2 216 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2799) (Sat.Literal.pos 216) (Sat.Literal.pos 212) (lex_2_216_prefix s) (positive_select s 216) (lex_2_216_image s)

theorem lex_2_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.pos 2799)] :=
  (lex_2_216_gate s).prop _ (List.Mem.head _)

theorem lex_2_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.neg 216), (Sat.Literal.pos 212)] :=
  (lex_2_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.pos 216), (Sat.Literal.neg 212)] :=
  (lex_2_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.neg 216), (Sat.Literal.neg 212), (Sat.Literal.pos 2800)] :=
  (lex_2_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2799), (Sat.Literal.pos 216), (Sat.Literal.pos 212), (Sat.Literal.pos 2800)] :=
  (lex_2_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2800) = lexBefore s permutation2 215 := by
  exact (positive_lex_of_descriptor s 2800 permutation2 216 (by rfl)).trans ((lex_skipped s permutation2 215 216 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation2 215) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation2 215 by rw [image2_eq]; rfl))

theorem lex_2_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2801) (Sat.Literal.pos 2800) (Sat.Literal.pos 215) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation2 215 (assignment s)
    (Sat.Literal.pos 2801) (Sat.Literal.pos 2800) (Sat.Literal.pos 215) (Sat.Literal.pos 219) (positive_of_descriptor s 2801 (.lex permutation2 215) (by rfl)) (lex_2_215_prefix s) (positive_select s 215) (lex_2_215_image s)

theorem lex_2_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.pos 215), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation2 215 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2800) (Sat.Literal.pos 215) (Sat.Literal.pos 219) (lex_2_215_prefix s) (positive_select s 215) (lex_2_215_image s)

theorem lex_2_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.pos 2800)] :=
  (lex_2_215_gate s).prop _ (List.Mem.head _)

theorem lex_2_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.neg 215), (Sat.Literal.pos 219)] :=
  (lex_2_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.pos 215), (Sat.Literal.neg 219)] :=
  (lex_2_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.neg 215), (Sat.Literal.neg 219), (Sat.Literal.pos 2801)] :=
  (lex_2_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2800), (Sat.Literal.pos 215), (Sat.Literal.pos 219), (Sat.Literal.pos 2801)] :=
  (lex_2_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2801) = lexBefore s permutation2 214 := by
  exact (positive_lex_of_descriptor s 2801 permutation2 215 (by rfl)).trans ((lex_skipped s permutation2 214 215 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation2 214) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation2 214 by rw [image2_eq]; rfl))

theorem lex_2_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2802) (Sat.Literal.pos 2801) (Sat.Literal.pos 214) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation2 214 (assignment s)
    (Sat.Literal.pos 2802) (Sat.Literal.pos 2801) (Sat.Literal.pos 214) (Sat.Literal.pos 218) (positive_of_descriptor s 2802 (.lex permutation2 214) (by rfl)) (lex_2_214_prefix s) (positive_select s 214) (lex_2_214_image s)

theorem lex_2_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.pos 214), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation2 214 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2801) (Sat.Literal.pos 214) (Sat.Literal.pos 218) (lex_2_214_prefix s) (positive_select s 214) (lex_2_214_image s)

theorem lex_2_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.pos 2801)] :=
  (lex_2_214_gate s).prop _ (List.Mem.head _)

theorem lex_2_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.neg 214), (Sat.Literal.pos 218)] :=
  (lex_2_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.pos 214), (Sat.Literal.neg 218)] :=
  (lex_2_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.neg 214), (Sat.Literal.neg 218), (Sat.Literal.pos 2802)] :=
  (lex_2_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2801), (Sat.Literal.pos 214), (Sat.Literal.pos 218), (Sat.Literal.pos 2802)] :=
  (lex_2_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2802) = lexBefore s permutation2 213 := by
  exact (positive_lex_of_descriptor s 2802 permutation2 214 (by rfl)).trans ((lex_skipped s permutation2 213 214 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation2 213) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation2 213 by rw [image2_eq]; rfl))

theorem lex_2_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2803) (Sat.Literal.pos 2802) (Sat.Literal.pos 213) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation2 213 (assignment s)
    (Sat.Literal.pos 2803) (Sat.Literal.pos 2802) (Sat.Literal.pos 213) (Sat.Literal.pos 217) (positive_of_descriptor s 2803 (.lex permutation2 213) (by rfl)) (lex_2_213_prefix s) (positive_select s 213) (lex_2_213_image s)

theorem lex_2_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.pos 213), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation2 213 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2802) (Sat.Literal.pos 213) (Sat.Literal.pos 217) (lex_2_213_prefix s) (positive_select s 213) (lex_2_213_image s)

theorem lex_2_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.pos 2802)] :=
  (lex_2_213_gate s).prop _ (List.Mem.head _)

theorem lex_2_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.neg 213), (Sat.Literal.pos 217)] :=
  (lex_2_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.pos 213), (Sat.Literal.neg 217)] :=
  (lex_2_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.neg 213), (Sat.Literal.neg 217), (Sat.Literal.pos 2803)] :=
  (lex_2_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2802), (Sat.Literal.pos 213), (Sat.Literal.pos 217), (Sat.Literal.pos 2803)] :=
  (lex_2_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2803) = lexBefore s permutation2 212 := by
  exact (positive_lex_of_descriptor s 2803 permutation2 213 (by rfl)).trans ((lex_skipped s permutation2 212 213 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation2 212) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation2 212 by rw [image2_eq]; rfl))

theorem lex_2_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2804) (Sat.Literal.pos 2803) (Sat.Literal.pos 212) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation2 212 (assignment s)
    (Sat.Literal.pos 2804) (Sat.Literal.pos 2803) (Sat.Literal.pos 212) (Sat.Literal.pos 216) (positive_of_descriptor s 2804 (.lex permutation2 212) (by rfl)) (lex_2_212_prefix s) (positive_select s 212) (lex_2_212_image s)

theorem lex_2_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.pos 212), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation2 212 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2803) (Sat.Literal.pos 212) (Sat.Literal.pos 216) (lex_2_212_prefix s) (positive_select s 212) (lex_2_212_image s)

theorem lex_2_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.pos 2803)] :=
  (lex_2_212_gate s).prop _ (List.Mem.head _)

theorem lex_2_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.neg 212), (Sat.Literal.pos 216)] :=
  (lex_2_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.pos 212), (Sat.Literal.neg 216)] :=
  (lex_2_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.neg 212), (Sat.Literal.neg 216), (Sat.Literal.pos 2804)] :=
  (lex_2_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2803), (Sat.Literal.pos 212), (Sat.Literal.pos 216), (Sat.Literal.pos 2804)] :=
  (lex_2_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2804) = lexBefore s permutation2 203 := by
  exact (positive_lex_of_descriptor s 2804 permutation2 212 (by rfl)).trans ((lex_skipped s permutation2 203 212 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 204 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation2 203) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation2 203 by rw [image2_eq]; rfl))

theorem lex_2_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2805) (Sat.Literal.pos 2804) (Sat.Literal.pos 203) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation2 203 (assignment s)
    (Sat.Literal.pos 2805) (Sat.Literal.pos 2804) (Sat.Literal.pos 203) (Sat.Literal.pos 199) (positive_of_descriptor s 2805 (.lex permutation2 203) (by rfl)) (lex_2_203_prefix s) (positive_select s 203) (lex_2_203_image s)

theorem lex_2_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.pos 203), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation2 203 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2804) (Sat.Literal.pos 203) (Sat.Literal.pos 199) (lex_2_203_prefix s) (positive_select s 203) (lex_2_203_image s)

theorem lex_2_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.pos 2804)] :=
  (lex_2_203_gate s).prop _ (List.Mem.head _)

theorem lex_2_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.neg 203), (Sat.Literal.pos 199)] :=
  (lex_2_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.pos 203), (Sat.Literal.neg 199)] :=
  (lex_2_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.neg 203), (Sat.Literal.neg 199), (Sat.Literal.pos 2805)] :=
  (lex_2_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2804), (Sat.Literal.pos 203), (Sat.Literal.pos 199), (Sat.Literal.pos 2805)] :=
  (lex_2_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2805) = lexBefore s permutation2 202 := by
  exact (positive_lex_of_descriptor s 2805 permutation2 203 (by rfl)).trans ((lex_skipped s permutation2 202 203 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation2 202) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation2 202 by rw [image2_eq]; rfl))

theorem lex_2_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2806) (Sat.Literal.pos 2805) (Sat.Literal.pos 202) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation2 202 (assignment s)
    (Sat.Literal.pos 2806) (Sat.Literal.pos 2805) (Sat.Literal.pos 202) (Sat.Literal.pos 198) (positive_of_descriptor s 2806 (.lex permutation2 202) (by rfl)) (lex_2_202_prefix s) (positive_select s 202) (lex_2_202_image s)

theorem lex_2_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.pos 202), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation2 202 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2805) (Sat.Literal.pos 202) (Sat.Literal.pos 198) (lex_2_202_prefix s) (positive_select s 202) (lex_2_202_image s)

theorem lex_2_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.pos 2805)] :=
  (lex_2_202_gate s).prop _ (List.Mem.head _)

theorem lex_2_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.neg 202), (Sat.Literal.pos 198)] :=
  (lex_2_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.pos 202), (Sat.Literal.neg 198)] :=
  (lex_2_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.neg 202), (Sat.Literal.neg 198), (Sat.Literal.pos 2806)] :=
  (lex_2_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2805), (Sat.Literal.pos 202), (Sat.Literal.pos 198), (Sat.Literal.pos 2806)] :=
  (lex_2_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2806) = lexBefore s permutation2 201 := by
  exact (positive_lex_of_descriptor s 2806 permutation2 202 (by rfl)).trans ((lex_skipped s permutation2 201 202 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation2 201) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation2 201 by rw [image2_eq]; rfl))

theorem lex_2_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2807) (Sat.Literal.pos 2806) (Sat.Literal.pos 201) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation2 201 (assignment s)
    (Sat.Literal.pos 2807) (Sat.Literal.pos 2806) (Sat.Literal.pos 201) (Sat.Literal.pos 197) (positive_of_descriptor s 2807 (.lex permutation2 201) (by rfl)) (lex_2_201_prefix s) (positive_select s 201) (lex_2_201_image s)

theorem lex_2_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.pos 201), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation2 201 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2806) (Sat.Literal.pos 201) (Sat.Literal.pos 197) (lex_2_201_prefix s) (positive_select s 201) (lex_2_201_image s)

theorem lex_2_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.pos 2806)] :=
  (lex_2_201_gate s).prop _ (List.Mem.head _)

theorem lex_2_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.neg 201), (Sat.Literal.pos 197)] :=
  (lex_2_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.pos 201), (Sat.Literal.neg 197)] :=
  (lex_2_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.neg 201), (Sat.Literal.neg 197), (Sat.Literal.pos 2807)] :=
  (lex_2_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2806), (Sat.Literal.pos 201), (Sat.Literal.pos 197), (Sat.Literal.pos 2807)] :=
  (lex_2_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2807) = lexBefore s permutation2 200 := by
  exact (positive_lex_of_descriptor s 2807 permutation2 201 (by rfl)).trans ((lex_skipped s permutation2 200 201 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation2 200) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation2 200 by rw [image2_eq]; rfl))

theorem lex_2_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2808) (Sat.Literal.pos 2807) (Sat.Literal.pos 200) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation2 200 (assignment s)
    (Sat.Literal.pos 2808) (Sat.Literal.pos 2807) (Sat.Literal.pos 200) (Sat.Literal.pos 196) (positive_of_descriptor s 2808 (.lex permutation2 200) (by rfl)) (lex_2_200_prefix s) (positive_select s 200) (lex_2_200_image s)

theorem lex_2_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.pos 200), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation2 200 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2807) (Sat.Literal.pos 200) (Sat.Literal.pos 196) (lex_2_200_prefix s) (positive_select s 200) (lex_2_200_image s)

theorem lex_2_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.pos 2807)] :=
  (lex_2_200_gate s).prop _ (List.Mem.head _)

theorem lex_2_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.neg 200), (Sat.Literal.pos 196)] :=
  (lex_2_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.pos 200), (Sat.Literal.neg 196)] :=
  (lex_2_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.neg 200), (Sat.Literal.neg 196), (Sat.Literal.pos 2808)] :=
  (lex_2_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2807), (Sat.Literal.pos 200), (Sat.Literal.pos 196), (Sat.Literal.pos 2808)] :=
  (lex_2_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2808) = lexBefore s permutation2 199 := by
  exact (positive_lex_of_descriptor s 2808 permutation2 200 (by rfl)).trans ((lex_skipped s permutation2 199 200 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation2 199) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation2 199 by rw [image2_eq]; rfl))

theorem lex_2_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2809) (Sat.Literal.pos 2808) (Sat.Literal.pos 199) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation2 199 (assignment s)
    (Sat.Literal.pos 2809) (Sat.Literal.pos 2808) (Sat.Literal.pos 199) (Sat.Literal.pos 203) (positive_of_descriptor s 2809 (.lex permutation2 199) (by rfl)) (lex_2_199_prefix s) (positive_select s 199) (lex_2_199_image s)

theorem lex_2_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.pos 199), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation2 199 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2808) (Sat.Literal.pos 199) (Sat.Literal.pos 203) (lex_2_199_prefix s) (positive_select s 199) (lex_2_199_image s)

theorem lex_2_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.pos 2808)] :=
  (lex_2_199_gate s).prop _ (List.Mem.head _)

theorem lex_2_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.neg 199), (Sat.Literal.pos 203)] :=
  (lex_2_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.pos 199), (Sat.Literal.neg 203)] :=
  (lex_2_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.neg 199), (Sat.Literal.neg 203), (Sat.Literal.pos 2809)] :=
  (lex_2_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2808), (Sat.Literal.pos 199), (Sat.Literal.pos 203), (Sat.Literal.pos 2809)] :=
  (lex_2_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2809) = lexBefore s permutation2 198 := by
  exact (positive_lex_of_descriptor s 2809 permutation2 199 (by rfl)).trans ((lex_skipped s permutation2 198 199 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation2 198) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation2 198 by rw [image2_eq]; rfl))

theorem lex_2_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2810) (Sat.Literal.pos 2809) (Sat.Literal.pos 198) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation2 198 (assignment s)
    (Sat.Literal.pos 2810) (Sat.Literal.pos 2809) (Sat.Literal.pos 198) (Sat.Literal.pos 202) (positive_of_descriptor s 2810 (.lex permutation2 198) (by rfl)) (lex_2_198_prefix s) (positive_select s 198) (lex_2_198_image s)

theorem lex_2_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.pos 198), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation2 198 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2809) (Sat.Literal.pos 198) (Sat.Literal.pos 202) (lex_2_198_prefix s) (positive_select s 198) (lex_2_198_image s)

theorem lex_2_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.pos 2809)] :=
  (lex_2_198_gate s).prop _ (List.Mem.head _)

theorem lex_2_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.neg 198), (Sat.Literal.pos 202)] :=
  (lex_2_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.pos 198), (Sat.Literal.neg 202)] :=
  (lex_2_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.neg 198), (Sat.Literal.neg 202), (Sat.Literal.pos 2810)] :=
  (lex_2_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2809), (Sat.Literal.pos 198), (Sat.Literal.pos 202), (Sat.Literal.pos 2810)] :=
  (lex_2_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2810) = lexBefore s permutation2 197 := by
  exact (positive_lex_of_descriptor s 2810 permutation2 198 (by rfl)).trans ((lex_skipped s permutation2 197 198 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation2 197) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation2 197 by rw [image2_eq]; rfl))

theorem lex_2_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2811) (Sat.Literal.pos 2810) (Sat.Literal.pos 197) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation2 197 (assignment s)
    (Sat.Literal.pos 2811) (Sat.Literal.pos 2810) (Sat.Literal.pos 197) (Sat.Literal.pos 201) (positive_of_descriptor s 2811 (.lex permutation2 197) (by rfl)) (lex_2_197_prefix s) (positive_select s 197) (lex_2_197_image s)

theorem lex_2_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.pos 197), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation2 197 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2810) (Sat.Literal.pos 197) (Sat.Literal.pos 201) (lex_2_197_prefix s) (positive_select s 197) (lex_2_197_image s)

theorem lex_2_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.pos 2810)] :=
  (lex_2_197_gate s).prop _ (List.Mem.head _)

theorem lex_2_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.neg 197), (Sat.Literal.pos 201)] :=
  (lex_2_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.pos 197), (Sat.Literal.neg 201)] :=
  (lex_2_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.neg 197), (Sat.Literal.neg 201), (Sat.Literal.pos 2811)] :=
  (lex_2_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2810), (Sat.Literal.pos 197), (Sat.Literal.pos 201), (Sat.Literal.pos 2811)] :=
  (lex_2_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2811) = lexBefore s permutation2 196 := by
  exact (positive_lex_of_descriptor s 2811 permutation2 197 (by rfl)).trans ((lex_skipped s permutation2 196 197 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation2 196) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation2 196 by rw [image2_eq]; rfl))

theorem lex_2_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2812) (Sat.Literal.pos 2811) (Sat.Literal.pos 196) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation2 196 (assignment s)
    (Sat.Literal.pos 2812) (Sat.Literal.pos 2811) (Sat.Literal.pos 196) (Sat.Literal.pos 200) (positive_of_descriptor s 2812 (.lex permutation2 196) (by rfl)) (lex_2_196_prefix s) (positive_select s 196) (lex_2_196_image s)

theorem lex_2_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.pos 196), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation2 196 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2811) (Sat.Literal.pos 196) (Sat.Literal.pos 200) (lex_2_196_prefix s) (positive_select s 196) (lex_2_196_image s)

theorem lex_2_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.pos 2811)] :=
  (lex_2_196_gate s).prop _ (List.Mem.head _)

theorem lex_2_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.neg 196), (Sat.Literal.pos 200)] :=
  (lex_2_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.pos 196), (Sat.Literal.neg 200)] :=
  (lex_2_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.neg 196), (Sat.Literal.neg 200), (Sat.Literal.pos 2812)] :=
  (lex_2_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2811), (Sat.Literal.pos 196), (Sat.Literal.pos 200), (Sat.Literal.pos 2812)] :=
  (lex_2_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2812) = lexBefore s permutation2 187 := by
  exact (positive_lex_of_descriptor s 2812 permutation2 196 (by rfl)).trans ((lex_skipped s permutation2 187 196 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 188 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation2 187) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation2 187 by rw [image2_eq]; rfl))

theorem lex_2_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2813) (Sat.Literal.pos 2812) (Sat.Literal.pos 187) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation2 187 (assignment s)
    (Sat.Literal.pos 2813) (Sat.Literal.pos 2812) (Sat.Literal.pos 187) (Sat.Literal.pos 183) (positive_of_descriptor s 2813 (.lex permutation2 187) (by rfl)) (lex_2_187_prefix s) (positive_select s 187) (lex_2_187_image s)

theorem lex_2_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.pos 187), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation2 187 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2812) (Sat.Literal.pos 187) (Sat.Literal.pos 183) (lex_2_187_prefix s) (positive_select s 187) (lex_2_187_image s)

theorem lex_2_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.pos 2812)] :=
  (lex_2_187_gate s).prop _ (List.Mem.head _)

theorem lex_2_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.neg 187), (Sat.Literal.pos 183)] :=
  (lex_2_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.pos 187), (Sat.Literal.neg 183)] :=
  (lex_2_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.neg 187), (Sat.Literal.neg 183), (Sat.Literal.pos 2813)] :=
  (lex_2_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2812), (Sat.Literal.pos 187), (Sat.Literal.pos 183), (Sat.Literal.pos 2813)] :=
  (lex_2_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2813) = lexBefore s permutation2 186 := by
  exact (positive_lex_of_descriptor s 2813 permutation2 187 (by rfl)).trans ((lex_skipped s permutation2 186 187 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation2 186) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation2 186 by rw [image2_eq]; rfl))

theorem lex_2_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2814) (Sat.Literal.pos 2813) (Sat.Literal.pos 186) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation2 186 (assignment s)
    (Sat.Literal.pos 2814) (Sat.Literal.pos 2813) (Sat.Literal.pos 186) (Sat.Literal.pos 182) (positive_of_descriptor s 2814 (.lex permutation2 186) (by rfl)) (lex_2_186_prefix s) (positive_select s 186) (lex_2_186_image s)

theorem lex_2_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.pos 186), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation2 186 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2813) (Sat.Literal.pos 186) (Sat.Literal.pos 182) (lex_2_186_prefix s) (positive_select s 186) (lex_2_186_image s)

theorem lex_2_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.pos 2813)] :=
  (lex_2_186_gate s).prop _ (List.Mem.head _)

theorem lex_2_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.neg 186), (Sat.Literal.pos 182)] :=
  (lex_2_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.pos 186), (Sat.Literal.neg 182)] :=
  (lex_2_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.neg 186), (Sat.Literal.neg 182), (Sat.Literal.pos 2814)] :=
  (lex_2_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2813), (Sat.Literal.pos 186), (Sat.Literal.pos 182), (Sat.Literal.pos 2814)] :=
  (lex_2_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2814) = lexBefore s permutation2 185 := by
  exact (positive_lex_of_descriptor s 2814 permutation2 186 (by rfl)).trans ((lex_skipped s permutation2 185 186 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation2 185) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation2 185 by rw [image2_eq]; rfl))

theorem lex_2_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2815) (Sat.Literal.pos 2814) (Sat.Literal.pos 185) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation2 185 (assignment s)
    (Sat.Literal.pos 2815) (Sat.Literal.pos 2814) (Sat.Literal.pos 185) (Sat.Literal.pos 181) (positive_of_descriptor s 2815 (.lex permutation2 185) (by rfl)) (lex_2_185_prefix s) (positive_select s 185) (lex_2_185_image s)

theorem lex_2_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.pos 185), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation2 185 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2814) (Sat.Literal.pos 185) (Sat.Literal.pos 181) (lex_2_185_prefix s) (positive_select s 185) (lex_2_185_image s)

theorem lex_2_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.pos 2814)] :=
  (lex_2_185_gate s).prop _ (List.Mem.head _)

theorem lex_2_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.neg 185), (Sat.Literal.pos 181)] :=
  (lex_2_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.pos 185), (Sat.Literal.neg 181)] :=
  (lex_2_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.neg 185), (Sat.Literal.neg 181), (Sat.Literal.pos 2815)] :=
  (lex_2_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2814), (Sat.Literal.pos 185), (Sat.Literal.pos 181), (Sat.Literal.pos 2815)] :=
  (lex_2_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2815) = lexBefore s permutation2 184 := by
  exact (positive_lex_of_descriptor s 2815 permutation2 185 (by rfl)).trans ((lex_skipped s permutation2 184 185 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation2 184) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation2 184 by rw [image2_eq]; rfl))

theorem lex_2_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2816) (Sat.Literal.pos 2815) (Sat.Literal.pos 184) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation2 184 (assignment s)
    (Sat.Literal.pos 2816) (Sat.Literal.pos 2815) (Sat.Literal.pos 184) (Sat.Literal.pos 180) (positive_of_descriptor s 2816 (.lex permutation2 184) (by rfl)) (lex_2_184_prefix s) (positive_select s 184) (lex_2_184_image s)

theorem lex_2_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.pos 184), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation2 184 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2815) (Sat.Literal.pos 184) (Sat.Literal.pos 180) (lex_2_184_prefix s) (positive_select s 184) (lex_2_184_image s)

theorem lex_2_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.pos 2815)] :=
  (lex_2_184_gate s).prop _ (List.Mem.head _)

theorem lex_2_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.neg 184), (Sat.Literal.pos 180)] :=
  (lex_2_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.pos 184), (Sat.Literal.neg 180)] :=
  (lex_2_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.neg 184), (Sat.Literal.neg 180), (Sat.Literal.pos 2816)] :=
  (lex_2_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2815), (Sat.Literal.pos 184), (Sat.Literal.pos 180), (Sat.Literal.pos 2816)] :=
  (lex_2_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2816) = lexBefore s permutation2 183 := by
  exact (positive_lex_of_descriptor s 2816 permutation2 184 (by rfl)).trans ((lex_skipped s permutation2 183 184 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation2 183) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation2 183 by rw [image2_eq]; rfl))

theorem lex_2_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2817) (Sat.Literal.pos 2816) (Sat.Literal.pos 183) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation2 183 (assignment s)
    (Sat.Literal.pos 2817) (Sat.Literal.pos 2816) (Sat.Literal.pos 183) (Sat.Literal.pos 187) (positive_of_descriptor s 2817 (.lex permutation2 183) (by rfl)) (lex_2_183_prefix s) (positive_select s 183) (lex_2_183_image s)

theorem lex_2_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.pos 183), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation2 183 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2816) (Sat.Literal.pos 183) (Sat.Literal.pos 187) (lex_2_183_prefix s) (positive_select s 183) (lex_2_183_image s)

theorem lex_2_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.pos 2816)] :=
  (lex_2_183_gate s).prop _ (List.Mem.head _)

theorem lex_2_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.neg 183), (Sat.Literal.pos 187)] :=
  (lex_2_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.pos 183), (Sat.Literal.neg 187)] :=
  (lex_2_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.neg 183), (Sat.Literal.neg 187), (Sat.Literal.pos 2817)] :=
  (lex_2_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2816), (Sat.Literal.pos 183), (Sat.Literal.pos 187), (Sat.Literal.pos 2817)] :=
  (lex_2_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2817) = lexBefore s permutation2 182 := by
  exact (positive_lex_of_descriptor s 2817 permutation2 183 (by rfl)).trans ((lex_skipped s permutation2 182 183 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation2 182) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation2 182 by rw [image2_eq]; rfl))

theorem lex_2_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2818) (Sat.Literal.pos 2817) (Sat.Literal.pos 182) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation2 182 (assignment s)
    (Sat.Literal.pos 2818) (Sat.Literal.pos 2817) (Sat.Literal.pos 182) (Sat.Literal.pos 186) (positive_of_descriptor s 2818 (.lex permutation2 182) (by rfl)) (lex_2_182_prefix s) (positive_select s 182) (lex_2_182_image s)

theorem lex_2_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.pos 182), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation2 182 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2817) (Sat.Literal.pos 182) (Sat.Literal.pos 186) (lex_2_182_prefix s) (positive_select s 182) (lex_2_182_image s)

theorem lex_2_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.pos 2817)] :=
  (lex_2_182_gate s).prop _ (List.Mem.head _)

theorem lex_2_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.neg 182), (Sat.Literal.pos 186)] :=
  (lex_2_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.pos 182), (Sat.Literal.neg 186)] :=
  (lex_2_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.neg 182), (Sat.Literal.neg 186), (Sat.Literal.pos 2818)] :=
  (lex_2_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2817), (Sat.Literal.pos 182), (Sat.Literal.pos 186), (Sat.Literal.pos 2818)] :=
  (lex_2_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2818) = lexBefore s permutation2 181 := by
  exact (positive_lex_of_descriptor s 2818 permutation2 182 (by rfl)).trans ((lex_skipped s permutation2 181 182 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation2 181) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation2 181 by rw [image2_eq]; rfl))

theorem lex_2_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2819) (Sat.Literal.pos 2818) (Sat.Literal.pos 181) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation2 181 (assignment s)
    (Sat.Literal.pos 2819) (Sat.Literal.pos 2818) (Sat.Literal.pos 181) (Sat.Literal.pos 185) (positive_of_descriptor s 2819 (.lex permutation2 181) (by rfl)) (lex_2_181_prefix s) (positive_select s 181) (lex_2_181_image s)

theorem lex_2_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.pos 181), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation2 181 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2818) (Sat.Literal.pos 181) (Sat.Literal.pos 185) (lex_2_181_prefix s) (positive_select s 181) (lex_2_181_image s)

theorem lex_2_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.pos 2818)] :=
  (lex_2_181_gate s).prop _ (List.Mem.head _)

theorem lex_2_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.neg 181), (Sat.Literal.pos 185)] :=
  (lex_2_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.pos 181), (Sat.Literal.neg 185)] :=
  (lex_2_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.neg 181), (Sat.Literal.neg 185), (Sat.Literal.pos 2819)] :=
  (lex_2_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2818), (Sat.Literal.pos 181), (Sat.Literal.pos 185), (Sat.Literal.pos 2819)] :=
  (lex_2_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2819) = lexBefore s permutation2 180 := by
  exact (positive_lex_of_descriptor s 2819 permutation2 181 (by rfl)).trans ((lex_skipped s permutation2 180 181 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation2 180) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation2 180 by rw [image2_eq]; rfl))

theorem lex_2_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2820) (Sat.Literal.pos 2819) (Sat.Literal.pos 180) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation2 180 (assignment s)
    (Sat.Literal.pos 2820) (Sat.Literal.pos 2819) (Sat.Literal.pos 180) (Sat.Literal.pos 184) (positive_of_descriptor s 2820 (.lex permutation2 180) (by rfl)) (lex_2_180_prefix s) (positive_select s 180) (lex_2_180_image s)

theorem lex_2_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.pos 180), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation2 180 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2819) (Sat.Literal.pos 180) (Sat.Literal.pos 184) (lex_2_180_prefix s) (positive_select s 180) (lex_2_180_image s)

theorem lex_2_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.pos 2819)] :=
  (lex_2_180_gate s).prop _ (List.Mem.head _)

theorem lex_2_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.neg 180), (Sat.Literal.pos 184)] :=
  (lex_2_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.pos 180), (Sat.Literal.neg 184)] :=
  (lex_2_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.neg 180), (Sat.Literal.neg 184), (Sat.Literal.pos 2820)] :=
  (lex_2_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2819), (Sat.Literal.pos 180), (Sat.Literal.pos 184), (Sat.Literal.pos 2820)] :=
  (lex_2_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2820) = lexBefore s permutation2 171 := by
  exact (positive_lex_of_descriptor s 2820 permutation2 180 (by rfl)).trans ((lex_skipped s permutation2 171 180 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 172 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation2 171) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation2 171 by rw [image2_eq]; rfl))

theorem lex_2_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2821) (Sat.Literal.pos 2820) (Sat.Literal.pos 171) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation2 171 (assignment s)
    (Sat.Literal.pos 2821) (Sat.Literal.pos 2820) (Sat.Literal.pos 171) (Sat.Literal.pos 167) (positive_of_descriptor s 2821 (.lex permutation2 171) (by rfl)) (lex_2_171_prefix s) (positive_select s 171) (lex_2_171_image s)

theorem lex_2_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.pos 171), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation2 171 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2820) (Sat.Literal.pos 171) (Sat.Literal.pos 167) (lex_2_171_prefix s) (positive_select s 171) (lex_2_171_image s)

theorem lex_2_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.pos 2820)] :=
  (lex_2_171_gate s).prop _ (List.Mem.head _)

theorem lex_2_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.neg 171), (Sat.Literal.pos 167)] :=
  (lex_2_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.pos 171), (Sat.Literal.neg 167)] :=
  (lex_2_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.neg 171), (Sat.Literal.neg 167), (Sat.Literal.pos 2821)] :=
  (lex_2_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2820), (Sat.Literal.pos 171), (Sat.Literal.pos 167), (Sat.Literal.pos 2821)] :=
  (lex_2_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2821) = lexBefore s permutation2 170 := by
  exact (positive_lex_of_descriptor s 2821 permutation2 171 (by rfl)).trans ((lex_skipped s permutation2 170 171 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation2 170) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation2 170 by rw [image2_eq]; rfl))

theorem lex_2_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2822) (Sat.Literal.pos 2821) (Sat.Literal.pos 170) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation2 170 (assignment s)
    (Sat.Literal.pos 2822) (Sat.Literal.pos 2821) (Sat.Literal.pos 170) (Sat.Literal.pos 166) (positive_of_descriptor s 2822 (.lex permutation2 170) (by rfl)) (lex_2_170_prefix s) (positive_select s 170) (lex_2_170_image s)

theorem lex_2_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.pos 170), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation2 170 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2821) (Sat.Literal.pos 170) (Sat.Literal.pos 166) (lex_2_170_prefix s) (positive_select s 170) (lex_2_170_image s)

theorem lex_2_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.pos 2821)] :=
  (lex_2_170_gate s).prop _ (List.Mem.head _)

theorem lex_2_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.neg 170), (Sat.Literal.pos 166)] :=
  (lex_2_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.pos 170), (Sat.Literal.neg 166)] :=
  (lex_2_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.neg 170), (Sat.Literal.neg 166), (Sat.Literal.pos 2822)] :=
  (lex_2_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2821), (Sat.Literal.pos 170), (Sat.Literal.pos 166), (Sat.Literal.pos 2822)] :=
  (lex_2_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2822) = lexBefore s permutation2 169 := by
  exact (positive_lex_of_descriptor s 2822 permutation2 170 (by rfl)).trans ((lex_skipped s permutation2 169 170 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation2 169) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation2 169 by rw [image2_eq]; rfl))

theorem lex_2_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2823) (Sat.Literal.pos 2822) (Sat.Literal.pos 169) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation2 169 (assignment s)
    (Sat.Literal.pos 2823) (Sat.Literal.pos 2822) (Sat.Literal.pos 169) (Sat.Literal.pos 165) (positive_of_descriptor s 2823 (.lex permutation2 169) (by rfl)) (lex_2_169_prefix s) (positive_select s 169) (lex_2_169_image s)

theorem lex_2_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.pos 169), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation2 169 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2822) (Sat.Literal.pos 169) (Sat.Literal.pos 165) (lex_2_169_prefix s) (positive_select s 169) (lex_2_169_image s)

theorem lex_2_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.pos 2822)] :=
  (lex_2_169_gate s).prop _ (List.Mem.head _)

theorem lex_2_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.neg 169), (Sat.Literal.pos 165)] :=
  (lex_2_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.pos 169), (Sat.Literal.neg 165)] :=
  (lex_2_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.neg 169), (Sat.Literal.neg 165), (Sat.Literal.pos 2823)] :=
  (lex_2_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2822), (Sat.Literal.pos 169), (Sat.Literal.pos 165), (Sat.Literal.pos 2823)] :=
  (lex_2_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2823) = lexBefore s permutation2 168 := by
  exact (positive_lex_of_descriptor s 2823 permutation2 169 (by rfl)).trans ((lex_skipped s permutation2 168 169 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation2 168) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation2 168 by rw [image2_eq]; rfl))

theorem lex_2_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2824) (Sat.Literal.pos 2823) (Sat.Literal.pos 168) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation2 168 (assignment s)
    (Sat.Literal.pos 2824) (Sat.Literal.pos 2823) (Sat.Literal.pos 168) (Sat.Literal.pos 164) (positive_of_descriptor s 2824 (.lex permutation2 168) (by rfl)) (lex_2_168_prefix s) (positive_select s 168) (lex_2_168_image s)

theorem lex_2_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.pos 168), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation2 168 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2823) (Sat.Literal.pos 168) (Sat.Literal.pos 164) (lex_2_168_prefix s) (positive_select s 168) (lex_2_168_image s)

theorem lex_2_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.pos 2823)] :=
  (lex_2_168_gate s).prop _ (List.Mem.head _)

theorem lex_2_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.neg 168), (Sat.Literal.pos 164)] :=
  (lex_2_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.pos 168), (Sat.Literal.neg 164)] :=
  (lex_2_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.neg 168), (Sat.Literal.neg 164), (Sat.Literal.pos 2824)] :=
  (lex_2_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2823), (Sat.Literal.pos 168), (Sat.Literal.pos 164), (Sat.Literal.pos 2824)] :=
  (lex_2_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_1_109_gate

end Crown.CertificateData
