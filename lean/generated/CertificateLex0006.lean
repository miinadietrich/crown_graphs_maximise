import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_4_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3124) = lexBefore s permutation4 87 := by
  exact (positive_lex_of_descriptor s 3124 permutation4 88 (by rfl)).trans ((lex_skipped s permutation4 87 88 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation4 87) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation4 87 by rw [image4_eq]; rfl))

theorem lex_4_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3125) (Sat.Literal.pos 3124) (Sat.Literal.pos 87) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation4 87 (assignment s)
    (Sat.Literal.pos 3125) (Sat.Literal.pos 3124) (Sat.Literal.pos 87) (Sat.Literal.pos 103) (positive_of_descriptor s 3125 (.lex permutation4 87) (by rfl)) (lex_4_87_prefix s) (positive_select s 87) (lex_4_87_image s)

theorem lex_4_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.pos 87), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation4 87 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3124) (Sat.Literal.pos 87) (Sat.Literal.pos 103) (lex_4_87_prefix s) (positive_select s 87) (lex_4_87_image s)

theorem lex_4_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.pos 3124)] :=
  (lex_4_87_gate s).prop _ (List.Mem.head _)

theorem lex_4_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.neg 87), (Sat.Literal.pos 103)] :=
  (lex_4_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.pos 87), (Sat.Literal.neg 103)] :=
  (lex_4_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.neg 87), (Sat.Literal.neg 103), (Sat.Literal.pos 3125)] :=
  (lex_4_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3124), (Sat.Literal.pos 87), (Sat.Literal.pos 103), (Sat.Literal.pos 3125)] :=
  (lex_4_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3125) = lexBefore s permutation4 86 := by
  exact (positive_lex_of_descriptor s 3125 permutation4 87 (by rfl)).trans ((lex_skipped s permutation4 86 87 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation4 86) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation4 86 by rw [image4_eq]; rfl))

theorem lex_4_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3126) (Sat.Literal.pos 3125) (Sat.Literal.pos 86) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation4 86 (assignment s)
    (Sat.Literal.pos 3126) (Sat.Literal.pos 3125) (Sat.Literal.pos 86) (Sat.Literal.pos 102) (positive_of_descriptor s 3126 (.lex permutation4 86) (by rfl)) (lex_4_86_prefix s) (positive_select s 86) (lex_4_86_image s)

theorem lex_4_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.pos 86), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation4 86 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3125) (Sat.Literal.pos 86) (Sat.Literal.pos 102) (lex_4_86_prefix s) (positive_select s 86) (lex_4_86_image s)

theorem lex_4_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.pos 3125)] :=
  (lex_4_86_gate s).prop _ (List.Mem.head _)

theorem lex_4_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.neg 86), (Sat.Literal.pos 102)] :=
  (lex_4_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.pos 86), (Sat.Literal.neg 102)] :=
  (lex_4_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.neg 86), (Sat.Literal.neg 102), (Sat.Literal.pos 3126)] :=
  (lex_4_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3125), (Sat.Literal.pos 86), (Sat.Literal.pos 102), (Sat.Literal.pos 3126)] :=
  (lex_4_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3126) = lexBefore s permutation4 85 := by
  exact (positive_lex_of_descriptor s 3126 permutation4 86 (by rfl)).trans ((lex_skipped s permutation4 85 86 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation4 85) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation4 85 by rw [image4_eq]; rfl))

theorem lex_4_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3127) (Sat.Literal.pos 3126) (Sat.Literal.pos 85) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation4 85 (assignment s)
    (Sat.Literal.pos 3127) (Sat.Literal.pos 3126) (Sat.Literal.pos 85) (Sat.Literal.pos 101) (positive_of_descriptor s 3127 (.lex permutation4 85) (by rfl)) (lex_4_85_prefix s) (positive_select s 85) (lex_4_85_image s)

theorem lex_4_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.pos 85), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation4 85 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3126) (Sat.Literal.pos 85) (Sat.Literal.pos 101) (lex_4_85_prefix s) (positive_select s 85) (lex_4_85_image s)

theorem lex_4_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.pos 3126)] :=
  (lex_4_85_gate s).prop _ (List.Mem.head _)

theorem lex_4_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.neg 85), (Sat.Literal.pos 101)] :=
  (lex_4_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.pos 85), (Sat.Literal.neg 101)] :=
  (lex_4_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.neg 85), (Sat.Literal.neg 101), (Sat.Literal.pos 3127)] :=
  (lex_4_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3126), (Sat.Literal.pos 85), (Sat.Literal.pos 101), (Sat.Literal.pos 3127)] :=
  (lex_4_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3127) = lexBefore s permutation4 84 := by
  exact (positive_lex_of_descriptor s 3127 permutation4 85 (by rfl)).trans ((lex_skipped s permutation4 84 85 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation4 84) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation4 84 by rw [image4_eq]; rfl))

theorem lex_4_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3128) (Sat.Literal.pos 3127) (Sat.Literal.pos 84) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation4 84 (assignment s)
    (Sat.Literal.pos 3128) (Sat.Literal.pos 3127) (Sat.Literal.pos 84) (Sat.Literal.pos 100) (positive_of_descriptor s 3128 (.lex permutation4 84) (by rfl)) (lex_4_84_prefix s) (positive_select s 84) (lex_4_84_image s)

theorem lex_4_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.pos 84), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation4 84 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3127) (Sat.Literal.pos 84) (Sat.Literal.pos 100) (lex_4_84_prefix s) (positive_select s 84) (lex_4_84_image s)

theorem lex_4_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.pos 3127)] :=
  (lex_4_84_gate s).prop _ (List.Mem.head _)

theorem lex_4_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.neg 84), (Sat.Literal.pos 100)] :=
  (lex_4_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.pos 84), (Sat.Literal.neg 100)] :=
  (lex_4_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.neg 84), (Sat.Literal.neg 100), (Sat.Literal.pos 3128)] :=
  (lex_4_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3127), (Sat.Literal.pos 84), (Sat.Literal.pos 100), (Sat.Literal.pos 3128)] :=
  (lex_4_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3128) = lexBefore s permutation4 83 := by
  exact (positive_lex_of_descriptor s 3128 permutation4 84 (by rfl)).trans ((lex_skipped s permutation4 83 84 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation4 83) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation4 83 by rw [image4_eq]; rfl))

theorem lex_4_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3129) (Sat.Literal.pos 3128) (Sat.Literal.pos 83) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation4 83 (assignment s)
    (Sat.Literal.pos 3129) (Sat.Literal.pos 3128) (Sat.Literal.pos 83) (Sat.Literal.pos 99) (positive_of_descriptor s 3129 (.lex permutation4 83) (by rfl)) (lex_4_83_prefix s) (positive_select s 83) (lex_4_83_image s)

theorem lex_4_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.pos 83), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation4 83 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3128) (Sat.Literal.pos 83) (Sat.Literal.pos 99) (lex_4_83_prefix s) (positive_select s 83) (lex_4_83_image s)

theorem lex_4_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.pos 3128)] :=
  (lex_4_83_gate s).prop _ (List.Mem.head _)

theorem lex_4_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.neg 83), (Sat.Literal.pos 99)] :=
  (lex_4_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.pos 83), (Sat.Literal.neg 99)] :=
  (lex_4_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.neg 83), (Sat.Literal.neg 99), (Sat.Literal.pos 3129)] :=
  (lex_4_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3128), (Sat.Literal.pos 83), (Sat.Literal.pos 99), (Sat.Literal.pos 3129)] :=
  (lex_4_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3129) = lexBefore s permutation4 82 := by
  exact (positive_lex_of_descriptor s 3129 permutation4 83 (by rfl)).trans ((lex_skipped s permutation4 82 83 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation4 82) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation4 82 by rw [image4_eq]; rfl))

theorem lex_4_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3130) (Sat.Literal.pos 3129) (Sat.Literal.pos 82) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation4 82 (assignment s)
    (Sat.Literal.pos 3130) (Sat.Literal.pos 3129) (Sat.Literal.pos 82) (Sat.Literal.pos 98) (positive_of_descriptor s 3130 (.lex permutation4 82) (by rfl)) (lex_4_82_prefix s) (positive_select s 82) (lex_4_82_image s)

theorem lex_4_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.pos 82), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation4 82 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3129) (Sat.Literal.pos 82) (Sat.Literal.pos 98) (lex_4_82_prefix s) (positive_select s 82) (lex_4_82_image s)

theorem lex_4_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.pos 3129)] :=
  (lex_4_82_gate s).prop _ (List.Mem.head _)

theorem lex_4_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.neg 82), (Sat.Literal.pos 98)] :=
  (lex_4_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.pos 82), (Sat.Literal.neg 98)] :=
  (lex_4_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.neg 82), (Sat.Literal.neg 98), (Sat.Literal.pos 3130)] :=
  (lex_4_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3129), (Sat.Literal.pos 82), (Sat.Literal.pos 98), (Sat.Literal.pos 3130)] :=
  (lex_4_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3130) = lexBefore s permutation4 81 := by
  exact (positive_lex_of_descriptor s 3130 permutation4 82 (by rfl)).trans ((lex_skipped s permutation4 81 82 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation4 81) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation4 81 by rw [image4_eq]; rfl))

theorem lex_4_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3131) (Sat.Literal.pos 3130) (Sat.Literal.pos 81) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation4 81 (assignment s)
    (Sat.Literal.pos 3131) (Sat.Literal.pos 3130) (Sat.Literal.pos 81) (Sat.Literal.pos 97) (positive_of_descriptor s 3131 (.lex permutation4 81) (by rfl)) (lex_4_81_prefix s) (positive_select s 81) (lex_4_81_image s)

theorem lex_4_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.pos 81), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation4 81 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3130) (Sat.Literal.pos 81) (Sat.Literal.pos 97) (lex_4_81_prefix s) (positive_select s 81) (lex_4_81_image s)

theorem lex_4_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.pos 3130)] :=
  (lex_4_81_gate s).prop _ (List.Mem.head _)

theorem lex_4_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.neg 81), (Sat.Literal.pos 97)] :=
  (lex_4_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.pos 81), (Sat.Literal.neg 97)] :=
  (lex_4_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.neg 81), (Sat.Literal.neg 97), (Sat.Literal.pos 3131)] :=
  (lex_4_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3130), (Sat.Literal.pos 81), (Sat.Literal.pos 97), (Sat.Literal.pos 3131)] :=
  (lex_4_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3131) = lexBefore s permutation4 80 := by
  exact (positive_lex_of_descriptor s 3131 permutation4 81 (by rfl)).trans ((lex_skipped s permutation4 80 81 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation4 80) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation4 80 by rw [image4_eq]; rfl))

theorem lex_4_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3132) (Sat.Literal.pos 3131) (Sat.Literal.pos 80) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation4 80 (assignment s)
    (Sat.Literal.pos 3132) (Sat.Literal.pos 3131) (Sat.Literal.pos 80) (Sat.Literal.pos 96) (positive_of_descriptor s 3132 (.lex permutation4 80) (by rfl)) (lex_4_80_prefix s) (positive_select s 80) (lex_4_80_image s)

theorem lex_4_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.pos 80), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation4 80 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3131) (Sat.Literal.pos 80) (Sat.Literal.pos 96) (lex_4_80_prefix s) (positive_select s 80) (lex_4_80_image s)

theorem lex_4_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.pos 3131)] :=
  (lex_4_80_gate s).prop _ (List.Mem.head _)

theorem lex_4_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.neg 80), (Sat.Literal.pos 96)] :=
  (lex_4_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.pos 80), (Sat.Literal.neg 96)] :=
  (lex_4_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.neg 80), (Sat.Literal.neg 96), (Sat.Literal.pos 3132)] :=
  (lex_4_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3131), (Sat.Literal.pos 80), (Sat.Literal.pos 96), (Sat.Literal.pos 3132)] :=
  (lex_4_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3132) = lexBefore s permutation4 47 := by
  exact (positive_lex_of_descriptor s 3132 permutation4 80 (by rfl)).trans ((lex_skipped s permutation4 47 80 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 48 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation4 47) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation4 47 by rw [image4_eq]; rfl))

theorem lex_4_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3133) (Sat.Literal.pos 3132) (Sat.Literal.pos 47) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation4 47 (assignment s)
    (Sat.Literal.pos 3133) (Sat.Literal.pos 3132) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (positive_of_descriptor s 3133 (.lex permutation4 47) (by rfl)) (lex_4_47_prefix s) (positive_select s 47) (lex_4_47_image s)

theorem lex_4_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation4 47 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3132) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (lex_4_47_prefix s) (positive_select s 47) (lex_4_47_image s)

theorem lex_4_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.pos 3132)] :=
  (lex_4_47_gate s).prop _ (List.Mem.head _)

theorem lex_4_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.neg 47), (Sat.Literal.pos 31)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.neg 47), (Sat.Literal.neg 31), (Sat.Literal.pos 3133)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3132), (Sat.Literal.pos 47), (Sat.Literal.pos 31), (Sat.Literal.pos 3133)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3133) = lexBefore s permutation4 46 := by
  exact (positive_lex_of_descriptor s 3133 permutation4 47 (by rfl)).trans ((lex_skipped s permutation4 46 47 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation4 46) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation4 46 by rw [image4_eq]; rfl))

theorem lex_4_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3134) (Sat.Literal.pos 3133) (Sat.Literal.pos 46) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation4 46 (assignment s)
    (Sat.Literal.pos 3134) (Sat.Literal.pos 3133) (Sat.Literal.pos 46) (Sat.Literal.pos 30) (positive_of_descriptor s 3134 (.lex permutation4 46) (by rfl)) (lex_4_46_prefix s) (positive_select s 46) (lex_4_46_image s)

theorem lex_4_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.pos 46), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation4 46 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3133) (Sat.Literal.pos 46) (Sat.Literal.pos 30) (lex_4_46_prefix s) (positive_select s 46) (lex_4_46_image s)

theorem lex_4_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.pos 3133)] :=
  (lex_4_46_gate s).prop _ (List.Mem.head _)

theorem lex_4_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.neg 46), (Sat.Literal.pos 30)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.pos 46), (Sat.Literal.neg 30)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.neg 46), (Sat.Literal.neg 30), (Sat.Literal.pos 3134)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3133), (Sat.Literal.pos 46), (Sat.Literal.pos 30), (Sat.Literal.pos 3134)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3134) = lexBefore s permutation4 45 := by
  exact (positive_lex_of_descriptor s 3134 permutation4 46 (by rfl)).trans ((lex_skipped s permutation4 45 46 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation4 45) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation4 45 by rw [image4_eq]; rfl))

theorem lex_4_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3135) (Sat.Literal.pos 3134) (Sat.Literal.pos 45) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation4 45 (assignment s)
    (Sat.Literal.pos 3135) (Sat.Literal.pos 3134) (Sat.Literal.pos 45) (Sat.Literal.pos 29) (positive_of_descriptor s 3135 (.lex permutation4 45) (by rfl)) (lex_4_45_prefix s) (positive_select s 45) (lex_4_45_image s)

theorem lex_4_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.pos 45), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation4 45 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3134) (Sat.Literal.pos 45) (Sat.Literal.pos 29) (lex_4_45_prefix s) (positive_select s 45) (lex_4_45_image s)

theorem lex_4_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.pos 3134)] :=
  (lex_4_45_gate s).prop _ (List.Mem.head _)

theorem lex_4_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.neg 45), (Sat.Literal.pos 29)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.pos 45), (Sat.Literal.neg 29)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.neg 45), (Sat.Literal.neg 29), (Sat.Literal.pos 3135)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3134), (Sat.Literal.pos 45), (Sat.Literal.pos 29), (Sat.Literal.pos 3135)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3135) = lexBefore s permutation4 44 := by
  exact (positive_lex_of_descriptor s 3135 permutation4 45 (by rfl)).trans ((lex_skipped s permutation4 44 45 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation4 44) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation4 44 by rw [image4_eq]; rfl))

theorem lex_4_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3136) (Sat.Literal.pos 3135) (Sat.Literal.pos 44) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation4 44 (assignment s)
    (Sat.Literal.pos 3136) (Sat.Literal.pos 3135) (Sat.Literal.pos 44) (Sat.Literal.pos 28) (positive_of_descriptor s 3136 (.lex permutation4 44) (by rfl)) (lex_4_44_prefix s) (positive_select s 44) (lex_4_44_image s)

theorem lex_4_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.pos 44), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation4 44 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3135) (Sat.Literal.pos 44) (Sat.Literal.pos 28) (lex_4_44_prefix s) (positive_select s 44) (lex_4_44_image s)

theorem lex_4_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.pos 3135)] :=
  (lex_4_44_gate s).prop _ (List.Mem.head _)

theorem lex_4_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.neg 44), (Sat.Literal.pos 28)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.pos 44), (Sat.Literal.neg 28)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.neg 44), (Sat.Literal.neg 28), (Sat.Literal.pos 3136)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3135), (Sat.Literal.pos 44), (Sat.Literal.pos 28), (Sat.Literal.pos 3136)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3136) = lexBefore s permutation4 43 := by
  exact (positive_lex_of_descriptor s 3136 permutation4 44 (by rfl)).trans ((lex_skipped s permutation4 43 44 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation4 43) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation4 43 by rw [image4_eq]; rfl))

theorem lex_4_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3137) (Sat.Literal.pos 3136) (Sat.Literal.pos 43) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation4 43 (assignment s)
    (Sat.Literal.pos 3137) (Sat.Literal.pos 3136) (Sat.Literal.pos 43) (Sat.Literal.pos 27) (positive_of_descriptor s 3137 (.lex permutation4 43) (by rfl)) (lex_4_43_prefix s) (positive_select s 43) (lex_4_43_image s)

theorem lex_4_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.pos 43), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation4 43 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3136) (Sat.Literal.pos 43) (Sat.Literal.pos 27) (lex_4_43_prefix s) (positive_select s 43) (lex_4_43_image s)

theorem lex_4_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.pos 3136)] :=
  (lex_4_43_gate s).prop _ (List.Mem.head _)

theorem lex_4_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.neg 43), (Sat.Literal.pos 27)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.pos 43), (Sat.Literal.neg 27)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.neg 43), (Sat.Literal.neg 27), (Sat.Literal.pos 3137)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3136), (Sat.Literal.pos 43), (Sat.Literal.pos 27), (Sat.Literal.pos 3137)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3137) = lexBefore s permutation4 42 := by
  exact (positive_lex_of_descriptor s 3137 permutation4 43 (by rfl)).trans ((lex_skipped s permutation4 42 43 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation4 42) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation4 42 by rw [image4_eq]; rfl))

theorem lex_4_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3138) (Sat.Literal.pos 3137) (Sat.Literal.pos 42) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation4 42 (assignment s)
    (Sat.Literal.pos 3138) (Sat.Literal.pos 3137) (Sat.Literal.pos 42) (Sat.Literal.pos 26) (positive_of_descriptor s 3138 (.lex permutation4 42) (by rfl)) (lex_4_42_prefix s) (positive_select s 42) (lex_4_42_image s)

theorem lex_4_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.pos 42), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation4 42 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3137) (Sat.Literal.pos 42) (Sat.Literal.pos 26) (lex_4_42_prefix s) (positive_select s 42) (lex_4_42_image s)

theorem lex_4_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.pos 3137)] :=
  (lex_4_42_gate s).prop _ (List.Mem.head _)

theorem lex_4_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.neg 42), (Sat.Literal.pos 26)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.pos 42), (Sat.Literal.neg 26)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.neg 42), (Sat.Literal.neg 26), (Sat.Literal.pos 3138)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3137), (Sat.Literal.pos 42), (Sat.Literal.pos 26), (Sat.Literal.pos 3138)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3138) = lexBefore s permutation4 41 := by
  exact (positive_lex_of_descriptor s 3138 permutation4 42 (by rfl)).trans ((lex_skipped s permutation4 41 42 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation4 41) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation4 41 by rw [image4_eq]; rfl))

theorem lex_4_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3139) (Sat.Literal.pos 3138) (Sat.Literal.pos 41) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation4 41 (assignment s)
    (Sat.Literal.pos 3139) (Sat.Literal.pos 3138) (Sat.Literal.pos 41) (Sat.Literal.pos 25) (positive_of_descriptor s 3139 (.lex permutation4 41) (by rfl)) (lex_4_41_prefix s) (positive_select s 41) (lex_4_41_image s)

theorem lex_4_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.pos 41), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation4 41 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3138) (Sat.Literal.pos 41) (Sat.Literal.pos 25) (lex_4_41_prefix s) (positive_select s 41) (lex_4_41_image s)

theorem lex_4_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.pos 3138)] :=
  (lex_4_41_gate s).prop _ (List.Mem.head _)

theorem lex_4_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.neg 41), (Sat.Literal.pos 25)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.pos 41), (Sat.Literal.neg 25)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.neg 41), (Sat.Literal.neg 25), (Sat.Literal.pos 3139)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3138), (Sat.Literal.pos 41), (Sat.Literal.pos 25), (Sat.Literal.pos 3139)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3139) = lexBefore s permutation4 40 := by
  exact (positive_lex_of_descriptor s 3139 permutation4 41 (by rfl)).trans ((lex_skipped s permutation4 40 41 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation4 40) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation4 40 by rw [image4_eq]; rfl))

theorem lex_4_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3140) (Sat.Literal.pos 3139) (Sat.Literal.pos 40) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation4 40 (assignment s)
    (Sat.Literal.pos 3140) (Sat.Literal.pos 3139) (Sat.Literal.pos 40) (Sat.Literal.pos 24) (positive_of_descriptor s 3140 (.lex permutation4 40) (by rfl)) (lex_4_40_prefix s) (positive_select s 40) (lex_4_40_image s)

theorem lex_4_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.pos 40), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation4 40 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3139) (Sat.Literal.pos 40) (Sat.Literal.pos 24) (lex_4_40_prefix s) (positive_select s 40) (lex_4_40_image s)

theorem lex_4_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.pos 3139)] :=
  (lex_4_40_gate s).prop _ (List.Mem.head _)

theorem lex_4_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.neg 40), (Sat.Literal.pos 24)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.pos 40), (Sat.Literal.neg 24)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.neg 40), (Sat.Literal.neg 24), (Sat.Literal.pos 3140)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3139), (Sat.Literal.pos 40), (Sat.Literal.pos 24), (Sat.Literal.pos 3140)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3140) = lexBefore s permutation4 39 := by
  exact (positive_lex_of_descriptor s 3140 permutation4 40 (by rfl)).trans ((lex_skipped s permutation4 39 40 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation4 39) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation4 39 by rw [image4_eq]; rfl))

theorem lex_4_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3141) (Sat.Literal.pos 3140) (Sat.Literal.pos 39) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation4 39 (assignment s)
    (Sat.Literal.pos 3141) (Sat.Literal.pos 3140) (Sat.Literal.pos 39) (Sat.Literal.pos 23) (positive_of_descriptor s 3141 (.lex permutation4 39) (by rfl)) (lex_4_39_prefix s) (positive_select s 39) (lex_4_39_image s)

theorem lex_4_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.pos 39), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation4 39 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3140) (Sat.Literal.pos 39) (Sat.Literal.pos 23) (lex_4_39_prefix s) (positive_select s 39) (lex_4_39_image s)

theorem lex_4_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.pos 3140)] :=
  (lex_4_39_gate s).prop _ (List.Mem.head _)

theorem lex_4_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.neg 39), (Sat.Literal.pos 23)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.pos 39), (Sat.Literal.neg 23)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.neg 39), (Sat.Literal.neg 23), (Sat.Literal.pos 3141)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3140), (Sat.Literal.pos 39), (Sat.Literal.pos 23), (Sat.Literal.pos 3141)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3141) = lexBefore s permutation4 38 := by
  exact (positive_lex_of_descriptor s 3141 permutation4 39 (by rfl)).trans ((lex_skipped s permutation4 38 39 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation4 38) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation4 38 by rw [image4_eq]; rfl))

theorem lex_4_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3142) (Sat.Literal.pos 3141) (Sat.Literal.pos 38) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation4 38 (assignment s)
    (Sat.Literal.pos 3142) (Sat.Literal.pos 3141) (Sat.Literal.pos 38) (Sat.Literal.pos 22) (positive_of_descriptor s 3142 (.lex permutation4 38) (by rfl)) (lex_4_38_prefix s) (positive_select s 38) (lex_4_38_image s)

theorem lex_4_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.pos 38), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation4 38 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3141) (Sat.Literal.pos 38) (Sat.Literal.pos 22) (lex_4_38_prefix s) (positive_select s 38) (lex_4_38_image s)

theorem lex_4_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.pos 3141)] :=
  (lex_4_38_gate s).prop _ (List.Mem.head _)

theorem lex_4_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.neg 38), (Sat.Literal.pos 22)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.pos 38), (Sat.Literal.neg 22)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.neg 38), (Sat.Literal.neg 22), (Sat.Literal.pos 3142)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3141), (Sat.Literal.pos 38), (Sat.Literal.pos 22), (Sat.Literal.pos 3142)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3142) = lexBefore s permutation4 37 := by
  exact (positive_lex_of_descriptor s 3142 permutation4 38 (by rfl)).trans ((lex_skipped s permutation4 37 38 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation4 37) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation4 37 by rw [image4_eq]; rfl))

theorem lex_4_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3143) (Sat.Literal.pos 3142) (Sat.Literal.pos 37) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation4 37 (assignment s)
    (Sat.Literal.pos 3143) (Sat.Literal.pos 3142) (Sat.Literal.pos 37) (Sat.Literal.pos 21) (positive_of_descriptor s 3143 (.lex permutation4 37) (by rfl)) (lex_4_37_prefix s) (positive_select s 37) (lex_4_37_image s)

theorem lex_4_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.pos 37), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation4 37 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3142) (Sat.Literal.pos 37) (Sat.Literal.pos 21) (lex_4_37_prefix s) (positive_select s 37) (lex_4_37_image s)

theorem lex_4_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.pos 3142)] :=
  (lex_4_37_gate s).prop _ (List.Mem.head _)

theorem lex_4_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.neg 37), (Sat.Literal.pos 21)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.pos 37), (Sat.Literal.neg 21)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.neg 37), (Sat.Literal.neg 21), (Sat.Literal.pos 3143)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3142), (Sat.Literal.pos 37), (Sat.Literal.pos 21), (Sat.Literal.pos 3143)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3143) = lexBefore s permutation4 36 := by
  exact (positive_lex_of_descriptor s 3143 permutation4 37 (by rfl)).trans ((lex_skipped s permutation4 36 37 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation4 36) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation4 36 by rw [image4_eq]; rfl))

theorem lex_4_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3144) (Sat.Literal.pos 3143) (Sat.Literal.pos 36) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation4 36 (assignment s)
    (Sat.Literal.pos 3144) (Sat.Literal.pos 3143) (Sat.Literal.pos 36) (Sat.Literal.pos 20) (positive_of_descriptor s 3144 (.lex permutation4 36) (by rfl)) (lex_4_36_prefix s) (positive_select s 36) (lex_4_36_image s)

theorem lex_4_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.pos 36), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation4 36 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3143) (Sat.Literal.pos 36) (Sat.Literal.pos 20) (lex_4_36_prefix s) (positive_select s 36) (lex_4_36_image s)

theorem lex_4_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.pos 3143)] :=
  (lex_4_36_gate s).prop _ (List.Mem.head _)

theorem lex_4_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.neg 36), (Sat.Literal.pos 20)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.pos 36), (Sat.Literal.neg 20)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.neg 36), (Sat.Literal.neg 20), (Sat.Literal.pos 3144)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3143), (Sat.Literal.pos 36), (Sat.Literal.pos 20), (Sat.Literal.pos 3144)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3144) = lexBefore s permutation4 35 := by
  exact (positive_lex_of_descriptor s 3144 permutation4 36 (by rfl)).trans ((lex_skipped s permutation4 35 36 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation4 35) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation4 35 by rw [image4_eq]; rfl))

theorem lex_4_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3145) (Sat.Literal.pos 3144) (Sat.Literal.pos 35) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation4 35 (assignment s)
    (Sat.Literal.pos 3145) (Sat.Literal.pos 3144) (Sat.Literal.pos 35) (Sat.Literal.pos 19) (positive_of_descriptor s 3145 (.lex permutation4 35) (by rfl)) (lex_4_35_prefix s) (positive_select s 35) (lex_4_35_image s)

theorem lex_4_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.pos 35), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation4 35 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3144) (Sat.Literal.pos 35) (Sat.Literal.pos 19) (lex_4_35_prefix s) (positive_select s 35) (lex_4_35_image s)

theorem lex_4_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.pos 3144)] :=
  (lex_4_35_gate s).prop _ (List.Mem.head _)

theorem lex_4_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.neg 35), (Sat.Literal.pos 19)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.pos 35), (Sat.Literal.neg 19)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.neg 35), (Sat.Literal.neg 19), (Sat.Literal.pos 3145)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3144), (Sat.Literal.pos 35), (Sat.Literal.pos 19), (Sat.Literal.pos 3145)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3145) = lexBefore s permutation4 34 := by
  exact (positive_lex_of_descriptor s 3145 permutation4 35 (by rfl)).trans ((lex_skipped s permutation4 34 35 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation4 34) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation4 34 by rw [image4_eq]; rfl))

theorem lex_4_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3146) (Sat.Literal.pos 3145) (Sat.Literal.pos 34) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation4 34 (assignment s)
    (Sat.Literal.pos 3146) (Sat.Literal.pos 3145) (Sat.Literal.pos 34) (Sat.Literal.pos 18) (positive_of_descriptor s 3146 (.lex permutation4 34) (by rfl)) (lex_4_34_prefix s) (positive_select s 34) (lex_4_34_image s)

theorem lex_4_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.pos 34), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation4 34 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3145) (Sat.Literal.pos 34) (Sat.Literal.pos 18) (lex_4_34_prefix s) (positive_select s 34) (lex_4_34_image s)

theorem lex_4_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.pos 3145)] :=
  (lex_4_34_gate s).prop _ (List.Mem.head _)

theorem lex_4_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.neg 34), (Sat.Literal.pos 18)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.pos 34), (Sat.Literal.neg 18)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.neg 34), (Sat.Literal.neg 18), (Sat.Literal.pos 3146)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3145), (Sat.Literal.pos 34), (Sat.Literal.pos 18), (Sat.Literal.pos 3146)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3146) = lexBefore s permutation4 33 := by
  exact (positive_lex_of_descriptor s 3146 permutation4 34 (by rfl)).trans ((lex_skipped s permutation4 33 34 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation4 33) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation4 33 by rw [image4_eq]; rfl))

theorem lex_4_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3147) (Sat.Literal.pos 3146) (Sat.Literal.pos 33) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation4 33 (assignment s)
    (Sat.Literal.pos 3147) (Sat.Literal.pos 3146) (Sat.Literal.pos 33) (Sat.Literal.pos 17) (positive_of_descriptor s 3147 (.lex permutation4 33) (by rfl)) (lex_4_33_prefix s) (positive_select s 33) (lex_4_33_image s)

theorem lex_4_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.pos 33), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation4 33 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3146) (Sat.Literal.pos 33) (Sat.Literal.pos 17) (lex_4_33_prefix s) (positive_select s 33) (lex_4_33_image s)

theorem lex_4_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.pos 3146)] :=
  (lex_4_33_gate s).prop _ (List.Mem.head _)

theorem lex_4_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.neg 33), (Sat.Literal.pos 17)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.pos 33), (Sat.Literal.neg 17)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.neg 33), (Sat.Literal.neg 17), (Sat.Literal.pos 3147)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3146), (Sat.Literal.pos 33), (Sat.Literal.pos 17), (Sat.Literal.pos 3147)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3147) = lexBefore s permutation4 32 := by
  exact (positive_lex_of_descriptor s 3147 permutation4 33 (by rfl)).trans ((lex_skipped s permutation4 32 33 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation4 32) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation4 32 by rw [image4_eq]; rfl))

theorem lex_4_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3148) (Sat.Literal.pos 3147) (Sat.Literal.pos 32) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation4 32 (assignment s)
    (Sat.Literal.pos 3148) (Sat.Literal.pos 3147) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (positive_of_descriptor s 3148 (.lex permutation4 32) (by rfl)) (lex_4_32_prefix s) (positive_select s 32) (lex_4_32_image s)

theorem lex_4_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation4 32 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3147) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (lex_4_32_prefix s) (positive_select s 32) (lex_4_32_image s)

theorem lex_4_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.pos 3147)] :=
  (lex_4_32_gate s).prop _ (List.Mem.head _)

theorem lex_4_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.neg 32), (Sat.Literal.pos 16)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.neg 32), (Sat.Literal.neg 16), (Sat.Literal.pos 3148)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3147), (Sat.Literal.pos 32), (Sat.Literal.pos 16), (Sat.Literal.pos 3148)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3148) = lexBefore s permutation4 31 := by
  exact (positive_lex_of_descriptor s 3148 permutation4 32 (by rfl)).trans ((lex_skipped s permutation4 31 32 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation4 31) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation4 31 by rw [image4_eq]; rfl))

theorem lex_4_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3149) (Sat.Literal.pos 3148) (Sat.Literal.pos 31) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation4 31 (assignment s)
    (Sat.Literal.pos 3149) (Sat.Literal.pos 3148) (Sat.Literal.pos 31) (Sat.Literal.pos 47) (positive_of_descriptor s 3149 (.lex permutation4 31) (by rfl)) (lex_4_31_prefix s) (positive_select s 31) (lex_4_31_image s)

theorem lex_4_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.pos 31), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation4 31 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3148) (Sat.Literal.pos 31) (Sat.Literal.pos 47) (lex_4_31_prefix s) (positive_select s 31) (lex_4_31_image s)

theorem lex_4_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.pos 3148)] :=
  (lex_4_31_gate s).prop _ (List.Mem.head _)

theorem lex_4_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.neg 31), (Sat.Literal.pos 47)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.pos 31), (Sat.Literal.neg 47)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.neg 31), (Sat.Literal.neg 47), (Sat.Literal.pos 3149)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3148), (Sat.Literal.pos 31), (Sat.Literal.pos 47), (Sat.Literal.pos 3149)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3149) = lexBefore s permutation4 30 := by
  exact (positive_lex_of_descriptor s 3149 permutation4 31 (by rfl)).trans ((lex_skipped s permutation4 30 31 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation4 30) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation4 30 by rw [image4_eq]; rfl))

theorem lex_4_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3150) (Sat.Literal.pos 3149) (Sat.Literal.pos 30) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation4 30 (assignment s)
    (Sat.Literal.pos 3150) (Sat.Literal.pos 3149) (Sat.Literal.pos 30) (Sat.Literal.pos 46) (positive_of_descriptor s 3150 (.lex permutation4 30) (by rfl)) (lex_4_30_prefix s) (positive_select s 30) (lex_4_30_image s)

theorem lex_4_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.pos 30), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation4 30 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3149) (Sat.Literal.pos 30) (Sat.Literal.pos 46) (lex_4_30_prefix s) (positive_select s 30) (lex_4_30_image s)

theorem lex_4_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.pos 3149)] :=
  (lex_4_30_gate s).prop _ (List.Mem.head _)

theorem lex_4_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.neg 30), (Sat.Literal.pos 46)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.pos 30), (Sat.Literal.neg 46)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.neg 30), (Sat.Literal.neg 46), (Sat.Literal.pos 3150)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3149), (Sat.Literal.pos 30), (Sat.Literal.pos 46), (Sat.Literal.pos 3150)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3150) = lexBefore s permutation4 29 := by
  exact (positive_lex_of_descriptor s 3150 permutation4 30 (by rfl)).trans ((lex_skipped s permutation4 29 30 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation4 29) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation4 29 by rw [image4_eq]; rfl))

theorem lex_4_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3151) (Sat.Literal.pos 3150) (Sat.Literal.pos 29) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation4 29 (assignment s)
    (Sat.Literal.pos 3151) (Sat.Literal.pos 3150) (Sat.Literal.pos 29) (Sat.Literal.pos 45) (positive_of_descriptor s 3151 (.lex permutation4 29) (by rfl)) (lex_4_29_prefix s) (positive_select s 29) (lex_4_29_image s)

theorem lex_4_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.pos 29), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation4 29 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3150) (Sat.Literal.pos 29) (Sat.Literal.pos 45) (lex_4_29_prefix s) (positive_select s 29) (lex_4_29_image s)

theorem lex_4_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.pos 3150)] :=
  (lex_4_29_gate s).prop _ (List.Mem.head _)

theorem lex_4_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.neg 29), (Sat.Literal.pos 45)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.pos 29), (Sat.Literal.neg 45)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.neg 29), (Sat.Literal.neg 45), (Sat.Literal.pos 3151)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3150), (Sat.Literal.pos 29), (Sat.Literal.pos 45), (Sat.Literal.pos 3151)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3151) = lexBefore s permutation4 28 := by
  exact (positive_lex_of_descriptor s 3151 permutation4 29 (by rfl)).trans ((lex_skipped s permutation4 28 29 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation4 28) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation4 28 by rw [image4_eq]; rfl))

theorem lex_4_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3152) (Sat.Literal.pos 3151) (Sat.Literal.pos 28) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation4 28 (assignment s)
    (Sat.Literal.pos 3152) (Sat.Literal.pos 3151) (Sat.Literal.pos 28) (Sat.Literal.pos 44) (positive_of_descriptor s 3152 (.lex permutation4 28) (by rfl)) (lex_4_28_prefix s) (positive_select s 28) (lex_4_28_image s)

theorem lex_4_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.pos 28), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation4 28 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3151) (Sat.Literal.pos 28) (Sat.Literal.pos 44) (lex_4_28_prefix s) (positive_select s 28) (lex_4_28_image s)

theorem lex_4_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.pos 3151)] :=
  (lex_4_28_gate s).prop _ (List.Mem.head _)

theorem lex_4_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.neg 28), (Sat.Literal.pos 44)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.pos 28), (Sat.Literal.neg 44)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.neg 28), (Sat.Literal.neg 44), (Sat.Literal.pos 3152)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3151), (Sat.Literal.pos 28), (Sat.Literal.pos 44), (Sat.Literal.pos 3152)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3152) = lexBefore s permutation4 27 := by
  exact (positive_lex_of_descriptor s 3152 permutation4 28 (by rfl)).trans ((lex_skipped s permutation4 27 28 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation4 27) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation4 27 by rw [image4_eq]; rfl))

theorem lex_4_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3153) (Sat.Literal.pos 3152) (Sat.Literal.pos 27) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation4 27 (assignment s)
    (Sat.Literal.pos 3153) (Sat.Literal.pos 3152) (Sat.Literal.pos 27) (Sat.Literal.pos 43) (positive_of_descriptor s 3153 (.lex permutation4 27) (by rfl)) (lex_4_27_prefix s) (positive_select s 27) (lex_4_27_image s)

theorem lex_4_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.pos 27), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation4 27 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3152) (Sat.Literal.pos 27) (Sat.Literal.pos 43) (lex_4_27_prefix s) (positive_select s 27) (lex_4_27_image s)

theorem lex_4_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.pos 3152)] :=
  (lex_4_27_gate s).prop _ (List.Mem.head _)

theorem lex_4_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.neg 27), (Sat.Literal.pos 43)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.pos 27), (Sat.Literal.neg 43)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.neg 27), (Sat.Literal.neg 43), (Sat.Literal.pos 3153)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3152), (Sat.Literal.pos 27), (Sat.Literal.pos 43), (Sat.Literal.pos 3153)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3153) = lexBefore s permutation4 26 := by
  exact (positive_lex_of_descriptor s 3153 permutation4 27 (by rfl)).trans ((lex_skipped s permutation4 26 27 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation4 26) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation4 26 by rw [image4_eq]; rfl))

theorem lex_4_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3154) (Sat.Literal.pos 3153) (Sat.Literal.pos 26) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation4 26 (assignment s)
    (Sat.Literal.pos 3154) (Sat.Literal.pos 3153) (Sat.Literal.pos 26) (Sat.Literal.pos 42) (positive_of_descriptor s 3154 (.lex permutation4 26) (by rfl)) (lex_4_26_prefix s) (positive_select s 26) (lex_4_26_image s)

theorem lex_4_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.pos 26), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation4 26 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3153) (Sat.Literal.pos 26) (Sat.Literal.pos 42) (lex_4_26_prefix s) (positive_select s 26) (lex_4_26_image s)

theorem lex_4_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.pos 3153)] :=
  (lex_4_26_gate s).prop _ (List.Mem.head _)

theorem lex_4_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.neg 26), (Sat.Literal.pos 42)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.pos 26), (Sat.Literal.neg 42)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.neg 26), (Sat.Literal.neg 42), (Sat.Literal.pos 3154)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3153), (Sat.Literal.pos 26), (Sat.Literal.pos 42), (Sat.Literal.pos 3154)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3154) = lexBefore s permutation4 25 := by
  exact (positive_lex_of_descriptor s 3154 permutation4 26 (by rfl)).trans ((lex_skipped s permutation4 25 26 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation4 25) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation4 25 by rw [image4_eq]; rfl))

theorem lex_4_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3155) (Sat.Literal.pos 3154) (Sat.Literal.pos 25) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation4 25 (assignment s)
    (Sat.Literal.pos 3155) (Sat.Literal.pos 3154) (Sat.Literal.pos 25) (Sat.Literal.pos 41) (positive_of_descriptor s 3155 (.lex permutation4 25) (by rfl)) (lex_4_25_prefix s) (positive_select s 25) (lex_4_25_image s)

theorem lex_4_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.pos 25), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation4 25 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3154) (Sat.Literal.pos 25) (Sat.Literal.pos 41) (lex_4_25_prefix s) (positive_select s 25) (lex_4_25_image s)

theorem lex_4_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.pos 3154)] :=
  (lex_4_25_gate s).prop _ (List.Mem.head _)

theorem lex_4_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.neg 25), (Sat.Literal.pos 41)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.pos 25), (Sat.Literal.neg 41)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.neg 25), (Sat.Literal.neg 41), (Sat.Literal.pos 3155)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3154), (Sat.Literal.pos 25), (Sat.Literal.pos 41), (Sat.Literal.pos 3155)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3155) = lexBefore s permutation4 24 := by
  exact (positive_lex_of_descriptor s 3155 permutation4 25 (by rfl)).trans ((lex_skipped s permutation4 24 25 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation4 24) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation4 24 by rw [image4_eq]; rfl))

theorem lex_4_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3156) (Sat.Literal.pos 3155) (Sat.Literal.pos 24) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation4 24 (assignment s)
    (Sat.Literal.pos 3156) (Sat.Literal.pos 3155) (Sat.Literal.pos 24) (Sat.Literal.pos 40) (positive_of_descriptor s 3156 (.lex permutation4 24) (by rfl)) (lex_4_24_prefix s) (positive_select s 24) (lex_4_24_image s)

theorem lex_4_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.pos 24), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation4 24 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3155) (Sat.Literal.pos 24) (Sat.Literal.pos 40) (lex_4_24_prefix s) (positive_select s 24) (lex_4_24_image s)

theorem lex_4_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.pos 3155)] :=
  (lex_4_24_gate s).prop _ (List.Mem.head _)

theorem lex_4_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.neg 24), (Sat.Literal.pos 40)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.pos 24), (Sat.Literal.neg 40)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.neg 24), (Sat.Literal.neg 40), (Sat.Literal.pos 3156)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3155), (Sat.Literal.pos 24), (Sat.Literal.pos 40), (Sat.Literal.pos 3156)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3156) = lexBefore s permutation4 23 := by
  exact (positive_lex_of_descriptor s 3156 permutation4 24 (by rfl)).trans ((lex_skipped s permutation4 23 24 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation4 23) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation4 23 by rw [image4_eq]; rfl))

theorem lex_4_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3157) (Sat.Literal.pos 3156) (Sat.Literal.pos 23) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation4 23 (assignment s)
    (Sat.Literal.pos 3157) (Sat.Literal.pos 3156) (Sat.Literal.pos 23) (Sat.Literal.pos 39) (positive_of_descriptor s 3157 (.lex permutation4 23) (by rfl)) (lex_4_23_prefix s) (positive_select s 23) (lex_4_23_image s)

theorem lex_4_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.pos 23), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation4 23 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3156) (Sat.Literal.pos 23) (Sat.Literal.pos 39) (lex_4_23_prefix s) (positive_select s 23) (lex_4_23_image s)

theorem lex_4_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.pos 3156)] :=
  (lex_4_23_gate s).prop _ (List.Mem.head _)

theorem lex_4_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.neg 23), (Sat.Literal.pos 39)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.pos 23), (Sat.Literal.neg 39)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.neg 23), (Sat.Literal.neg 39), (Sat.Literal.pos 3157)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3156), (Sat.Literal.pos 23), (Sat.Literal.pos 39), (Sat.Literal.pos 3157)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3157) = lexBefore s permutation4 22 := by
  exact (positive_lex_of_descriptor s 3157 permutation4 23 (by rfl)).trans ((lex_skipped s permutation4 22 23 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation4 22) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation4 22 by rw [image4_eq]; rfl))

theorem lex_4_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3158) (Sat.Literal.pos 3157) (Sat.Literal.pos 22) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation4 22 (assignment s)
    (Sat.Literal.pos 3158) (Sat.Literal.pos 3157) (Sat.Literal.pos 22) (Sat.Literal.pos 38) (positive_of_descriptor s 3158 (.lex permutation4 22) (by rfl)) (lex_4_22_prefix s) (positive_select s 22) (lex_4_22_image s)

theorem lex_4_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.pos 22), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation4 22 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3157) (Sat.Literal.pos 22) (Sat.Literal.pos 38) (lex_4_22_prefix s) (positive_select s 22) (lex_4_22_image s)

theorem lex_4_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.pos 3157)] :=
  (lex_4_22_gate s).prop _ (List.Mem.head _)

theorem lex_4_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.neg 22), (Sat.Literal.pos 38)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.pos 22), (Sat.Literal.neg 38)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.neg 22), (Sat.Literal.neg 38), (Sat.Literal.pos 3158)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3157), (Sat.Literal.pos 22), (Sat.Literal.pos 38), (Sat.Literal.pos 3158)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3158) = lexBefore s permutation4 21 := by
  exact (positive_lex_of_descriptor s 3158 permutation4 22 (by rfl)).trans ((lex_skipped s permutation4 21 22 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation4 21) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation4 21 by rw [image4_eq]; rfl))

theorem lex_4_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3159) (Sat.Literal.pos 3158) (Sat.Literal.pos 21) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation4 21 (assignment s)
    (Sat.Literal.pos 3159) (Sat.Literal.pos 3158) (Sat.Literal.pos 21) (Sat.Literal.pos 37) (positive_of_descriptor s 3159 (.lex permutation4 21) (by rfl)) (lex_4_21_prefix s) (positive_select s 21) (lex_4_21_image s)

theorem lex_4_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.pos 21), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation4 21 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3158) (Sat.Literal.pos 21) (Sat.Literal.pos 37) (lex_4_21_prefix s) (positive_select s 21) (lex_4_21_image s)

theorem lex_4_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.pos 3158)] :=
  (lex_4_21_gate s).prop _ (List.Mem.head _)

theorem lex_4_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.neg 21), (Sat.Literal.pos 37)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.pos 21), (Sat.Literal.neg 37)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.neg 21), (Sat.Literal.neg 37), (Sat.Literal.pos 3159)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3158), (Sat.Literal.pos 21), (Sat.Literal.pos 37), (Sat.Literal.pos 3159)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3159) = lexBefore s permutation4 20 := by
  exact (positive_lex_of_descriptor s 3159 permutation4 21 (by rfl)).trans ((lex_skipped s permutation4 20 21 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation4 20) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation4 20 by rw [image4_eq]; rfl))

theorem lex_4_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3160) (Sat.Literal.pos 3159) (Sat.Literal.pos 20) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation4 20 (assignment s)
    (Sat.Literal.pos 3160) (Sat.Literal.pos 3159) (Sat.Literal.pos 20) (Sat.Literal.pos 36) (positive_of_descriptor s 3160 (.lex permutation4 20) (by rfl)) (lex_4_20_prefix s) (positive_select s 20) (lex_4_20_image s)

theorem lex_4_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.pos 20), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation4 20 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3159) (Sat.Literal.pos 20) (Sat.Literal.pos 36) (lex_4_20_prefix s) (positive_select s 20) (lex_4_20_image s)

theorem lex_4_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.pos 3159)] :=
  (lex_4_20_gate s).prop _ (List.Mem.head _)

theorem lex_4_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.neg 20), (Sat.Literal.pos 36)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.pos 20), (Sat.Literal.neg 36)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.neg 20), (Sat.Literal.neg 36), (Sat.Literal.pos 3160)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3159), (Sat.Literal.pos 20), (Sat.Literal.pos 36), (Sat.Literal.pos 3160)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3160) = lexBefore s permutation4 19 := by
  exact (positive_lex_of_descriptor s 3160 permutation4 20 (by rfl)).trans ((lex_skipped s permutation4 19 20 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation4 19) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation4 19 by rw [image4_eq]; rfl))

theorem lex_4_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3161) (Sat.Literal.pos 3160) (Sat.Literal.pos 19) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation4 19 (assignment s)
    (Sat.Literal.pos 3161) (Sat.Literal.pos 3160) (Sat.Literal.pos 19) (Sat.Literal.pos 35) (positive_of_descriptor s 3161 (.lex permutation4 19) (by rfl)) (lex_4_19_prefix s) (positive_select s 19) (lex_4_19_image s)

theorem lex_4_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.pos 19), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation4 19 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3160) (Sat.Literal.pos 19) (Sat.Literal.pos 35) (lex_4_19_prefix s) (positive_select s 19) (lex_4_19_image s)

theorem lex_4_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.pos 3160)] :=
  (lex_4_19_gate s).prop _ (List.Mem.head _)

theorem lex_4_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.neg 19), (Sat.Literal.pos 35)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.pos 19), (Sat.Literal.neg 35)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.neg 19), (Sat.Literal.neg 35), (Sat.Literal.pos 3161)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3160), (Sat.Literal.pos 19), (Sat.Literal.pos 35), (Sat.Literal.pos 3161)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3161) = lexBefore s permutation4 18 := by
  exact (positive_lex_of_descriptor s 3161 permutation4 19 (by rfl)).trans ((lex_skipped s permutation4 18 19 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation4 18) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation4 18 by rw [image4_eq]; rfl))

theorem lex_4_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3162) (Sat.Literal.pos 3161) (Sat.Literal.pos 18) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation4 18 (assignment s)
    (Sat.Literal.pos 3162) (Sat.Literal.pos 3161) (Sat.Literal.pos 18) (Sat.Literal.pos 34) (positive_of_descriptor s 3162 (.lex permutation4 18) (by rfl)) (lex_4_18_prefix s) (positive_select s 18) (lex_4_18_image s)

theorem lex_4_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.pos 18), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation4 18 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3161) (Sat.Literal.pos 18) (Sat.Literal.pos 34) (lex_4_18_prefix s) (positive_select s 18) (lex_4_18_image s)

theorem lex_4_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.pos 3161)] :=
  (lex_4_18_gate s).prop _ (List.Mem.head _)

theorem lex_4_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.neg 18), (Sat.Literal.pos 34)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.pos 18), (Sat.Literal.neg 34)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.neg 18), (Sat.Literal.neg 34), (Sat.Literal.pos 3162)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3161), (Sat.Literal.pos 18), (Sat.Literal.pos 34), (Sat.Literal.pos 3162)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3162) = lexBefore s permutation4 17 := by
  exact (positive_lex_of_descriptor s 3162 permutation4 18 (by rfl)).trans ((lex_skipped s permutation4 17 18 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation4 17) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation4 17 by rw [image4_eq]; rfl))

theorem lex_4_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3163) (Sat.Literal.pos 3162) (Sat.Literal.pos 17) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation4 17 (assignment s)
    (Sat.Literal.pos 3163) (Sat.Literal.pos 3162) (Sat.Literal.pos 17) (Sat.Literal.pos 33) (positive_of_descriptor s 3163 (.lex permutation4 17) (by rfl)) (lex_4_17_prefix s) (positive_select s 17) (lex_4_17_image s)

theorem lex_4_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.pos 17), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation4 17 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3162) (Sat.Literal.pos 17) (Sat.Literal.pos 33) (lex_4_17_prefix s) (positive_select s 17) (lex_4_17_image s)

theorem lex_4_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.pos 3162)] :=
  (lex_4_17_gate s).prop _ (List.Mem.head _)

theorem lex_4_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.neg 17), (Sat.Literal.pos 33)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.pos 17), (Sat.Literal.neg 33)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.neg 17), (Sat.Literal.neg 33), (Sat.Literal.pos 3163)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3162), (Sat.Literal.pos 17), (Sat.Literal.pos 33), (Sat.Literal.pos 3163)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3163) = lexBefore s permutation4 16 := by
  exact (positive_lex_of_descriptor s 3163 permutation4 17 (by rfl)).trans ((lex_skipped s permutation4 16 17 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation4 16) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation4 16 by rw [image4_eq]; rfl))

theorem lex_4_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3164) (Sat.Literal.pos 3163) (Sat.Literal.pos 16) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation4 16 (assignment s)
    (Sat.Literal.pos 3164) (Sat.Literal.pos 3163) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (positive_of_descriptor s 3164 (.lex permutation4 16) (by rfl)) (lex_4_16_prefix s) (positive_select s 16) (lex_4_16_image s)

theorem lex_4_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation4 16 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 3163) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (lex_4_16_prefix s) (positive_select s 16) (lex_4_16_image s)

theorem lex_4_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3164), (Sat.Literal.pos 3163)] :=
  (lex_4_16_gate s).prop _ (List.Mem.head _)

theorem lex_4_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3164), (Sat.Literal.neg 16), (Sat.Literal.pos 32)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3164), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.neg 16), (Sat.Literal.neg 32), (Sat.Literal.pos 3164)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3163), (Sat.Literal.pos 16), (Sat.Literal.pos 32), (Sat.Literal.pos 3164)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation5 223 := by
  exact (negative_falsum s).trans ((lex_first s permutation5 223 (by intro j hj; rw [image5_eq]; exact fixedOnRange_spec image5 224 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_5_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation5 223) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation5 223 by rw [image5_eq]; rfl))

theorem lex_5_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3165) (Sat.Literal.neg 256) (Sat.Literal.pos 223) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation5 223 (assignment s)
    (Sat.Literal.pos 3165) (Sat.Literal.neg 256) (Sat.Literal.pos 223) (Sat.Literal.pos 191) (positive_of_descriptor s 3165 (.lex permutation5 223) (by rfl)) (lex_5_223_prefix s) (positive_select s 223) (lex_5_223_image s)

theorem lex_5_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 223), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation5 223 (hmax permutation5) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 223) (Sat.Literal.pos 191) (lex_5_223_prefix s) (positive_select s 223) (lex_5_223_image s)

theorem lex_5_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.neg 256)] :=
  (lex_5_223_gate s).prop _ (List.Mem.head _)

theorem lex_5_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.neg 223), (Sat.Literal.pos 191)] :=
  (lex_5_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.pos 223), (Sat.Literal.neg 191)] :=
  (lex_5_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 223), (Sat.Literal.neg 191), (Sat.Literal.pos 3165)] :=
  (lex_5_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 223), (Sat.Literal.pos 191), (Sat.Literal.pos 3165)] :=
  (lex_5_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3165) = lexBefore s permutation5 222 := by
  exact (positive_lex_of_descriptor s 3165 permutation5 223 (by rfl)).trans ((lex_skipped s permutation5 222 223 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation5 222) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation5 222 by rw [image5_eq]; rfl))

theorem lex_5_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3166) (Sat.Literal.pos 3165) (Sat.Literal.pos 222) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation5 222 (assignment s)
    (Sat.Literal.pos 3166) (Sat.Literal.pos 3165) (Sat.Literal.pos 222) (Sat.Literal.pos 190) (positive_of_descriptor s 3166 (.lex permutation5 222) (by rfl)) (lex_5_222_prefix s) (positive_select s 222) (lex_5_222_image s)

theorem lex_5_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.pos 222), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation5 222 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3165) (Sat.Literal.pos 222) (Sat.Literal.pos 190) (lex_5_222_prefix s) (positive_select s 222) (lex_5_222_image s)

theorem lex_5_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.pos 3165)] :=
  (lex_5_222_gate s).prop _ (List.Mem.head _)

theorem lex_5_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.neg 222), (Sat.Literal.pos 190)] :=
  (lex_5_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.pos 222), (Sat.Literal.neg 190)] :=
  (lex_5_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.neg 222), (Sat.Literal.neg 190), (Sat.Literal.pos 3166)] :=
  (lex_5_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3165), (Sat.Literal.pos 222), (Sat.Literal.pos 190), (Sat.Literal.pos 3166)] :=
  (lex_5_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3166) = lexBefore s permutation5 221 := by
  exact (positive_lex_of_descriptor s 3166 permutation5 222 (by rfl)).trans ((lex_skipped s permutation5 221 222 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation5 221) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation5 221 by rw [image5_eq]; rfl))

theorem lex_5_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3167) (Sat.Literal.pos 3166) (Sat.Literal.pos 221) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation5 221 (assignment s)
    (Sat.Literal.pos 3167) (Sat.Literal.pos 3166) (Sat.Literal.pos 221) (Sat.Literal.pos 189) (positive_of_descriptor s 3167 (.lex permutation5 221) (by rfl)) (lex_5_221_prefix s) (positive_select s 221) (lex_5_221_image s)

theorem lex_5_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.pos 221), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation5 221 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3166) (Sat.Literal.pos 221) (Sat.Literal.pos 189) (lex_5_221_prefix s) (positive_select s 221) (lex_5_221_image s)

theorem lex_5_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.pos 3166)] :=
  (lex_5_221_gate s).prop _ (List.Mem.head _)

theorem lex_5_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.neg 221), (Sat.Literal.pos 189)] :=
  (lex_5_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.pos 221), (Sat.Literal.neg 189)] :=
  (lex_5_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.neg 221), (Sat.Literal.neg 189), (Sat.Literal.pos 3167)] :=
  (lex_5_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3166), (Sat.Literal.pos 221), (Sat.Literal.pos 189), (Sat.Literal.pos 3167)] :=
  (lex_5_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3167) = lexBefore s permutation5 220 := by
  exact (positive_lex_of_descriptor s 3167 permutation5 221 (by rfl)).trans ((lex_skipped s permutation5 220 221 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation5 220) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation5 220 by rw [image5_eq]; rfl))

theorem lex_5_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3168) (Sat.Literal.pos 3167) (Sat.Literal.pos 220) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation5 220 (assignment s)
    (Sat.Literal.pos 3168) (Sat.Literal.pos 3167) (Sat.Literal.pos 220) (Sat.Literal.pos 188) (positive_of_descriptor s 3168 (.lex permutation5 220) (by rfl)) (lex_5_220_prefix s) (positive_select s 220) (lex_5_220_image s)

theorem lex_5_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.pos 220), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation5 220 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3167) (Sat.Literal.pos 220) (Sat.Literal.pos 188) (lex_5_220_prefix s) (positive_select s 220) (lex_5_220_image s)

theorem lex_5_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.pos 3167)] :=
  (lex_5_220_gate s).prop _ (List.Mem.head _)

theorem lex_5_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.neg 220), (Sat.Literal.pos 188)] :=
  (lex_5_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.pos 220), (Sat.Literal.neg 188)] :=
  (lex_5_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.neg 220), (Sat.Literal.neg 188), (Sat.Literal.pos 3168)] :=
  (lex_5_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3167), (Sat.Literal.pos 220), (Sat.Literal.pos 188), (Sat.Literal.pos 3168)] :=
  (lex_5_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3168) = lexBefore s permutation5 219 := by
  exact (positive_lex_of_descriptor s 3168 permutation5 220 (by rfl)).trans ((lex_skipped s permutation5 219 220 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation5 219) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation5 219 by rw [image5_eq]; rfl))

theorem lex_5_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3169) (Sat.Literal.pos 3168) (Sat.Literal.pos 219) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation5 219 (assignment s)
    (Sat.Literal.pos 3169) (Sat.Literal.pos 3168) (Sat.Literal.pos 219) (Sat.Literal.pos 187) (positive_of_descriptor s 3169 (.lex permutation5 219) (by rfl)) (lex_5_219_prefix s) (positive_select s 219) (lex_5_219_image s)

theorem lex_5_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.pos 219), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation5 219 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3168) (Sat.Literal.pos 219) (Sat.Literal.pos 187) (lex_5_219_prefix s) (positive_select s 219) (lex_5_219_image s)

theorem lex_5_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.pos 3168)] :=
  (lex_5_219_gate s).prop _ (List.Mem.head _)

theorem lex_5_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.neg 219), (Sat.Literal.pos 187)] :=
  (lex_5_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.pos 219), (Sat.Literal.neg 187)] :=
  (lex_5_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.neg 219), (Sat.Literal.neg 187), (Sat.Literal.pos 3169)] :=
  (lex_5_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3168), (Sat.Literal.pos 219), (Sat.Literal.pos 187), (Sat.Literal.pos 3169)] :=
  (lex_5_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3169) = lexBefore s permutation5 218 := by
  exact (positive_lex_of_descriptor s 3169 permutation5 219 (by rfl)).trans ((lex_skipped s permutation5 218 219 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation5 218) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation5 218 by rw [image5_eq]; rfl))

theorem lex_5_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3170) (Sat.Literal.pos 3169) (Sat.Literal.pos 218) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation5 218 (assignment s)
    (Sat.Literal.pos 3170) (Sat.Literal.pos 3169) (Sat.Literal.pos 218) (Sat.Literal.pos 186) (positive_of_descriptor s 3170 (.lex permutation5 218) (by rfl)) (lex_5_218_prefix s) (positive_select s 218) (lex_5_218_image s)

theorem lex_5_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.pos 218), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation5 218 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3169) (Sat.Literal.pos 218) (Sat.Literal.pos 186) (lex_5_218_prefix s) (positive_select s 218) (lex_5_218_image s)

theorem lex_5_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.pos 3169)] :=
  (lex_5_218_gate s).prop _ (List.Mem.head _)

theorem lex_5_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.neg 218), (Sat.Literal.pos 186)] :=
  (lex_5_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.pos 218), (Sat.Literal.neg 186)] :=
  (lex_5_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.neg 218), (Sat.Literal.neg 186), (Sat.Literal.pos 3170)] :=
  (lex_5_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3169), (Sat.Literal.pos 218), (Sat.Literal.pos 186), (Sat.Literal.pos 3170)] :=
  (lex_5_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3170) = lexBefore s permutation5 217 := by
  exact (positive_lex_of_descriptor s 3170 permutation5 218 (by rfl)).trans ((lex_skipped s permutation5 217 218 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation5 217) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation5 217 by rw [image5_eq]; rfl))

theorem lex_5_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3171) (Sat.Literal.pos 3170) (Sat.Literal.pos 217) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation5 217 (assignment s)
    (Sat.Literal.pos 3171) (Sat.Literal.pos 3170) (Sat.Literal.pos 217) (Sat.Literal.pos 185) (positive_of_descriptor s 3171 (.lex permutation5 217) (by rfl)) (lex_5_217_prefix s) (positive_select s 217) (lex_5_217_image s)

theorem lex_5_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.pos 217), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation5 217 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3170) (Sat.Literal.pos 217) (Sat.Literal.pos 185) (lex_5_217_prefix s) (positive_select s 217) (lex_5_217_image s)

theorem lex_5_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.pos 3170)] :=
  (lex_5_217_gate s).prop _ (List.Mem.head _)

theorem lex_5_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.neg 217), (Sat.Literal.pos 185)] :=
  (lex_5_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.pos 217), (Sat.Literal.neg 185)] :=
  (lex_5_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.neg 217), (Sat.Literal.neg 185), (Sat.Literal.pos 3171)] :=
  (lex_5_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3170), (Sat.Literal.pos 217), (Sat.Literal.pos 185), (Sat.Literal.pos 3171)] :=
  (lex_5_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3171) = lexBefore s permutation5 216 := by
  exact (positive_lex_of_descriptor s 3171 permutation5 217 (by rfl)).trans ((lex_skipped s permutation5 216 217 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation5 216) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation5 216 by rw [image5_eq]; rfl))

theorem lex_5_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3172) (Sat.Literal.pos 3171) (Sat.Literal.pos 216) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation5 216 (assignment s)
    (Sat.Literal.pos 3172) (Sat.Literal.pos 3171) (Sat.Literal.pos 216) (Sat.Literal.pos 184) (positive_of_descriptor s 3172 (.lex permutation5 216) (by rfl)) (lex_5_216_prefix s) (positive_select s 216) (lex_5_216_image s)

theorem lex_5_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.pos 216), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation5 216 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3171) (Sat.Literal.pos 216) (Sat.Literal.pos 184) (lex_5_216_prefix s) (positive_select s 216) (lex_5_216_image s)

theorem lex_5_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.pos 3171)] :=
  (lex_5_216_gate s).prop _ (List.Mem.head _)

theorem lex_5_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.neg 216), (Sat.Literal.pos 184)] :=
  (lex_5_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.pos 216), (Sat.Literal.neg 184)] :=
  (lex_5_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.neg 216), (Sat.Literal.neg 184), (Sat.Literal.pos 3172)] :=
  (lex_5_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3171), (Sat.Literal.pos 216), (Sat.Literal.pos 184), (Sat.Literal.pos 3172)] :=
  (lex_5_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3172) = lexBefore s permutation5 215 := by
  exact (positive_lex_of_descriptor s 3172 permutation5 216 (by rfl)).trans ((lex_skipped s permutation5 215 216 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation5 215) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation5 215 by rw [image5_eq]; rfl))

theorem lex_5_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3173) (Sat.Literal.pos 3172) (Sat.Literal.pos 215) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation5 215 (assignment s)
    (Sat.Literal.pos 3173) (Sat.Literal.pos 3172) (Sat.Literal.pos 215) (Sat.Literal.pos 183) (positive_of_descriptor s 3173 (.lex permutation5 215) (by rfl)) (lex_5_215_prefix s) (positive_select s 215) (lex_5_215_image s)

theorem lex_5_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.pos 215), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation5 215 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3172) (Sat.Literal.pos 215) (Sat.Literal.pos 183) (lex_5_215_prefix s) (positive_select s 215) (lex_5_215_image s)

theorem lex_5_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.pos 3172)] :=
  (lex_5_215_gate s).prop _ (List.Mem.head _)

theorem lex_5_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.neg 215), (Sat.Literal.pos 183)] :=
  (lex_5_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.pos 215), (Sat.Literal.neg 183)] :=
  (lex_5_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.neg 215), (Sat.Literal.neg 183), (Sat.Literal.pos 3173)] :=
  (lex_5_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3172), (Sat.Literal.pos 215), (Sat.Literal.pos 183), (Sat.Literal.pos 3173)] :=
  (lex_5_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3173) = lexBefore s permutation5 214 := by
  exact (positive_lex_of_descriptor s 3173 permutation5 215 (by rfl)).trans ((lex_skipped s permutation5 214 215 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation5 214) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation5 214 by rw [image5_eq]; rfl))

theorem lex_5_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3174) (Sat.Literal.pos 3173) (Sat.Literal.pos 214) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation5 214 (assignment s)
    (Sat.Literal.pos 3174) (Sat.Literal.pos 3173) (Sat.Literal.pos 214) (Sat.Literal.pos 182) (positive_of_descriptor s 3174 (.lex permutation5 214) (by rfl)) (lex_5_214_prefix s) (positive_select s 214) (lex_5_214_image s)

theorem lex_5_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.pos 214), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation5 214 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3173) (Sat.Literal.pos 214) (Sat.Literal.pos 182) (lex_5_214_prefix s) (positive_select s 214) (lex_5_214_image s)

theorem lex_5_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.pos 3173)] :=
  (lex_5_214_gate s).prop _ (List.Mem.head _)

theorem lex_5_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.neg 214), (Sat.Literal.pos 182)] :=
  (lex_5_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.pos 214), (Sat.Literal.neg 182)] :=
  (lex_5_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.neg 214), (Sat.Literal.neg 182), (Sat.Literal.pos 3174)] :=
  (lex_5_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3173), (Sat.Literal.pos 214), (Sat.Literal.pos 182), (Sat.Literal.pos 3174)] :=
  (lex_5_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3174) = lexBefore s permutation5 213 := by
  exact (positive_lex_of_descriptor s 3174 permutation5 214 (by rfl)).trans ((lex_skipped s permutation5 213 214 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation5 213) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation5 213 by rw [image5_eq]; rfl))

theorem lex_5_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3175) (Sat.Literal.pos 3174) (Sat.Literal.pos 213) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation5 213 (assignment s)
    (Sat.Literal.pos 3175) (Sat.Literal.pos 3174) (Sat.Literal.pos 213) (Sat.Literal.pos 181) (positive_of_descriptor s 3175 (.lex permutation5 213) (by rfl)) (lex_5_213_prefix s) (positive_select s 213) (lex_5_213_image s)

theorem lex_5_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.pos 213), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation5 213 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3174) (Sat.Literal.pos 213) (Sat.Literal.pos 181) (lex_5_213_prefix s) (positive_select s 213) (lex_5_213_image s)

theorem lex_5_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.pos 3174)] :=
  (lex_5_213_gate s).prop _ (List.Mem.head _)

theorem lex_5_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.neg 213), (Sat.Literal.pos 181)] :=
  (lex_5_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.pos 213), (Sat.Literal.neg 181)] :=
  (lex_5_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.neg 213), (Sat.Literal.neg 181), (Sat.Literal.pos 3175)] :=
  (lex_5_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3174), (Sat.Literal.pos 213), (Sat.Literal.pos 181), (Sat.Literal.pos 3175)] :=
  (lex_5_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3175) = lexBefore s permutation5 212 := by
  exact (positive_lex_of_descriptor s 3175 permutation5 213 (by rfl)).trans ((lex_skipped s permutation5 212 213 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation5 212) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation5 212 by rw [image5_eq]; rfl))

theorem lex_5_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3176) (Sat.Literal.pos 3175) (Sat.Literal.pos 212) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation5 212 (assignment s)
    (Sat.Literal.pos 3176) (Sat.Literal.pos 3175) (Sat.Literal.pos 212) (Sat.Literal.pos 180) (positive_of_descriptor s 3176 (.lex permutation5 212) (by rfl)) (lex_5_212_prefix s) (positive_select s 212) (lex_5_212_image s)

theorem lex_5_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.pos 212), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation5 212 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3175) (Sat.Literal.pos 212) (Sat.Literal.pos 180) (lex_5_212_prefix s) (positive_select s 212) (lex_5_212_image s)

theorem lex_5_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.pos 3175)] :=
  (lex_5_212_gate s).prop _ (List.Mem.head _)

theorem lex_5_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.neg 212), (Sat.Literal.pos 180)] :=
  (lex_5_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.pos 212), (Sat.Literal.neg 180)] :=
  (lex_5_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.neg 212), (Sat.Literal.neg 180), (Sat.Literal.pos 3176)] :=
  (lex_5_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3175), (Sat.Literal.pos 212), (Sat.Literal.pos 180), (Sat.Literal.pos 3176)] :=
  (lex_5_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3176) = lexBefore s permutation5 211 := by
  exact (positive_lex_of_descriptor s 3176 permutation5 212 (by rfl)).trans ((lex_skipped s permutation5 211 212 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation5 211) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation5 211 by rw [image5_eq]; rfl))

theorem lex_5_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3177) (Sat.Literal.pos 3176) (Sat.Literal.pos 211) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation5 211 (assignment s)
    (Sat.Literal.pos 3177) (Sat.Literal.pos 3176) (Sat.Literal.pos 211) (Sat.Literal.pos 179) (positive_of_descriptor s 3177 (.lex permutation5 211) (by rfl)) (lex_5_211_prefix s) (positive_select s 211) (lex_5_211_image s)

theorem lex_5_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.pos 211), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation5 211 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3176) (Sat.Literal.pos 211) (Sat.Literal.pos 179) (lex_5_211_prefix s) (positive_select s 211) (lex_5_211_image s)

theorem lex_5_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.pos 3176)] :=
  (lex_5_211_gate s).prop _ (List.Mem.head _)

theorem lex_5_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.neg 211), (Sat.Literal.pos 179)] :=
  (lex_5_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.pos 211), (Sat.Literal.neg 179)] :=
  (lex_5_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.neg 211), (Sat.Literal.neg 179), (Sat.Literal.pos 3177)] :=
  (lex_5_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3176), (Sat.Literal.pos 211), (Sat.Literal.pos 179), (Sat.Literal.pos 3177)] :=
  (lex_5_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3177) = lexBefore s permutation5 210 := by
  exact (positive_lex_of_descriptor s 3177 permutation5 211 (by rfl)).trans ((lex_skipped s permutation5 210 211 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation5 210) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation5 210 by rw [image5_eq]; rfl))

theorem lex_5_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3178) (Sat.Literal.pos 3177) (Sat.Literal.pos 210) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation5 210 (assignment s)
    (Sat.Literal.pos 3178) (Sat.Literal.pos 3177) (Sat.Literal.pos 210) (Sat.Literal.pos 178) (positive_of_descriptor s 3178 (.lex permutation5 210) (by rfl)) (lex_5_210_prefix s) (positive_select s 210) (lex_5_210_image s)

theorem lex_5_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.pos 210), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation5 210 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3177) (Sat.Literal.pos 210) (Sat.Literal.pos 178) (lex_5_210_prefix s) (positive_select s 210) (lex_5_210_image s)

theorem lex_5_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.pos 3177)] :=
  (lex_5_210_gate s).prop _ (List.Mem.head _)

theorem lex_5_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.neg 210), (Sat.Literal.pos 178)] :=
  (lex_5_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.pos 210), (Sat.Literal.neg 178)] :=
  (lex_5_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.neg 210), (Sat.Literal.neg 178), (Sat.Literal.pos 3178)] :=
  (lex_5_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3177), (Sat.Literal.pos 210), (Sat.Literal.pos 178), (Sat.Literal.pos 3178)] :=
  (lex_5_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3178) = lexBefore s permutation5 209 := by
  exact (positive_lex_of_descriptor s 3178 permutation5 210 (by rfl)).trans ((lex_skipped s permutation5 209 210 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation5 209) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation5 209 by rw [image5_eq]; rfl))

theorem lex_5_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3179) (Sat.Literal.pos 3178) (Sat.Literal.pos 209) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation5 209 (assignment s)
    (Sat.Literal.pos 3179) (Sat.Literal.pos 3178) (Sat.Literal.pos 209) (Sat.Literal.pos 177) (positive_of_descriptor s 3179 (.lex permutation5 209) (by rfl)) (lex_5_209_prefix s) (positive_select s 209) (lex_5_209_image s)

theorem lex_5_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.pos 209), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation5 209 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3178) (Sat.Literal.pos 209) (Sat.Literal.pos 177) (lex_5_209_prefix s) (positive_select s 209) (lex_5_209_image s)

theorem lex_5_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.pos 3178)] :=
  (lex_5_209_gate s).prop _ (List.Mem.head _)

theorem lex_5_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.neg 209), (Sat.Literal.pos 177)] :=
  (lex_5_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.pos 209), (Sat.Literal.neg 177)] :=
  (lex_5_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.neg 209), (Sat.Literal.neg 177), (Sat.Literal.pos 3179)] :=
  (lex_5_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3178), (Sat.Literal.pos 209), (Sat.Literal.pos 177), (Sat.Literal.pos 3179)] :=
  (lex_5_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3179) = lexBefore s permutation5 208 := by
  exact (positive_lex_of_descriptor s 3179 permutation5 209 (by rfl)).trans ((lex_skipped s permutation5 208 209 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation5 208) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation5 208 by rw [image5_eq]; rfl))

theorem lex_5_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3180) (Sat.Literal.pos 3179) (Sat.Literal.pos 208) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation5 208 (assignment s)
    (Sat.Literal.pos 3180) (Sat.Literal.pos 3179) (Sat.Literal.pos 208) (Sat.Literal.pos 176) (positive_of_descriptor s 3180 (.lex permutation5 208) (by rfl)) (lex_5_208_prefix s) (positive_select s 208) (lex_5_208_image s)

theorem lex_5_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.pos 208), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation5 208 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3179) (Sat.Literal.pos 208) (Sat.Literal.pos 176) (lex_5_208_prefix s) (positive_select s 208) (lex_5_208_image s)

theorem lex_5_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.pos 3179)] :=
  (lex_5_208_gate s).prop _ (List.Mem.head _)

theorem lex_5_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.neg 208), (Sat.Literal.pos 176)] :=
  (lex_5_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.pos 208), (Sat.Literal.neg 176)] :=
  (lex_5_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.neg 208), (Sat.Literal.neg 176), (Sat.Literal.pos 3180)] :=
  (lex_5_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3179), (Sat.Literal.pos 208), (Sat.Literal.pos 176), (Sat.Literal.pos 3180)] :=
  (lex_5_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3180) = lexBefore s permutation5 207 := by
  exact (positive_lex_of_descriptor s 3180 permutation5 208 (by rfl)).trans ((lex_skipped s permutation5 207 208 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation5 207) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation5 207 by rw [image5_eq]; rfl))

theorem lex_5_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3181) (Sat.Literal.pos 3180) (Sat.Literal.pos 207) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation5 207 (assignment s)
    (Sat.Literal.pos 3181) (Sat.Literal.pos 3180) (Sat.Literal.pos 207) (Sat.Literal.pos 175) (positive_of_descriptor s 3181 (.lex permutation5 207) (by rfl)) (lex_5_207_prefix s) (positive_select s 207) (lex_5_207_image s)

theorem lex_5_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.pos 207), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation5 207 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3180) (Sat.Literal.pos 207) (Sat.Literal.pos 175) (lex_5_207_prefix s) (positive_select s 207) (lex_5_207_image s)

theorem lex_5_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.pos 3180)] :=
  (lex_5_207_gate s).prop _ (List.Mem.head _)

theorem lex_5_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.neg 207), (Sat.Literal.pos 175)] :=
  (lex_5_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.pos 207), (Sat.Literal.neg 175)] :=
  (lex_5_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.neg 207), (Sat.Literal.neg 175), (Sat.Literal.pos 3181)] :=
  (lex_5_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3180), (Sat.Literal.pos 207), (Sat.Literal.pos 175), (Sat.Literal.pos 3181)] :=
  (lex_5_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3181) = lexBefore s permutation5 206 := by
  exact (positive_lex_of_descriptor s 3181 permutation5 207 (by rfl)).trans ((lex_skipped s permutation5 206 207 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation5 206) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation5 206 by rw [image5_eq]; rfl))

theorem lex_5_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3182) (Sat.Literal.pos 3181) (Sat.Literal.pos 206) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation5 206 (assignment s)
    (Sat.Literal.pos 3182) (Sat.Literal.pos 3181) (Sat.Literal.pos 206) (Sat.Literal.pos 174) (positive_of_descriptor s 3182 (.lex permutation5 206) (by rfl)) (lex_5_206_prefix s) (positive_select s 206) (lex_5_206_image s)

theorem lex_5_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.pos 206), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation5 206 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3181) (Sat.Literal.pos 206) (Sat.Literal.pos 174) (lex_5_206_prefix s) (positive_select s 206) (lex_5_206_image s)

theorem lex_5_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.pos 3181)] :=
  (lex_5_206_gate s).prop _ (List.Mem.head _)

theorem lex_5_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.neg 206), (Sat.Literal.pos 174)] :=
  (lex_5_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.pos 206), (Sat.Literal.neg 174)] :=
  (lex_5_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.neg 206), (Sat.Literal.neg 174), (Sat.Literal.pos 3182)] :=
  (lex_5_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3181), (Sat.Literal.pos 206), (Sat.Literal.pos 174), (Sat.Literal.pos 3182)] :=
  (lex_5_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3182) = lexBefore s permutation5 205 := by
  exact (positive_lex_of_descriptor s 3182 permutation5 206 (by rfl)).trans ((lex_skipped s permutation5 205 206 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation5 205) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation5 205 by rw [image5_eq]; rfl))

theorem lex_5_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3183) (Sat.Literal.pos 3182) (Sat.Literal.pos 205) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation5 205 (assignment s)
    (Sat.Literal.pos 3183) (Sat.Literal.pos 3182) (Sat.Literal.pos 205) (Sat.Literal.pos 173) (positive_of_descriptor s 3183 (.lex permutation5 205) (by rfl)) (lex_5_205_prefix s) (positive_select s 205) (lex_5_205_image s)

theorem lex_5_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.pos 205), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation5 205 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3182) (Sat.Literal.pos 205) (Sat.Literal.pos 173) (lex_5_205_prefix s) (positive_select s 205) (lex_5_205_image s)

theorem lex_5_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.pos 3182)] :=
  (lex_5_205_gate s).prop _ (List.Mem.head _)

theorem lex_5_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.neg 205), (Sat.Literal.pos 173)] :=
  (lex_5_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.pos 205), (Sat.Literal.neg 173)] :=
  (lex_5_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.neg 205), (Sat.Literal.neg 173), (Sat.Literal.pos 3183)] :=
  (lex_5_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3182), (Sat.Literal.pos 205), (Sat.Literal.pos 173), (Sat.Literal.pos 3183)] :=
  (lex_5_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3183) = lexBefore s permutation5 204 := by
  exact (positive_lex_of_descriptor s 3183 permutation5 205 (by rfl)).trans ((lex_skipped s permutation5 204 205 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation5 204) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation5 204 by rw [image5_eq]; rfl))

theorem lex_5_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3184) (Sat.Literal.pos 3183) (Sat.Literal.pos 204) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation5 204 (assignment s)
    (Sat.Literal.pos 3184) (Sat.Literal.pos 3183) (Sat.Literal.pos 204) (Sat.Literal.pos 172) (positive_of_descriptor s 3184 (.lex permutation5 204) (by rfl)) (lex_5_204_prefix s) (positive_select s 204) (lex_5_204_image s)

theorem lex_5_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.pos 204), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation5 204 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3183) (Sat.Literal.pos 204) (Sat.Literal.pos 172) (lex_5_204_prefix s) (positive_select s 204) (lex_5_204_image s)

theorem lex_5_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.pos 3183)] :=
  (lex_5_204_gate s).prop _ (List.Mem.head _)

theorem lex_5_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.neg 204), (Sat.Literal.pos 172)] :=
  (lex_5_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.pos 204), (Sat.Literal.neg 172)] :=
  (lex_5_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.neg 204), (Sat.Literal.neg 172), (Sat.Literal.pos 3184)] :=
  (lex_5_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3183), (Sat.Literal.pos 204), (Sat.Literal.pos 172), (Sat.Literal.pos 3184)] :=
  (lex_5_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3184) = lexBefore s permutation5 203 := by
  exact (positive_lex_of_descriptor s 3184 permutation5 204 (by rfl)).trans ((lex_skipped s permutation5 203 204 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation5 203) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation5 203 by rw [image5_eq]; rfl))

theorem lex_5_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3185) (Sat.Literal.pos 3184) (Sat.Literal.pos 203) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation5 203 (assignment s)
    (Sat.Literal.pos 3185) (Sat.Literal.pos 3184) (Sat.Literal.pos 203) (Sat.Literal.pos 171) (positive_of_descriptor s 3185 (.lex permutation5 203) (by rfl)) (lex_5_203_prefix s) (positive_select s 203) (lex_5_203_image s)

theorem lex_5_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.pos 203), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation5 203 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3184) (Sat.Literal.pos 203) (Sat.Literal.pos 171) (lex_5_203_prefix s) (positive_select s 203) (lex_5_203_image s)

theorem lex_5_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.pos 3184)] :=
  (lex_5_203_gate s).prop _ (List.Mem.head _)

theorem lex_5_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.neg 203), (Sat.Literal.pos 171)] :=
  (lex_5_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.pos 203), (Sat.Literal.neg 171)] :=
  (lex_5_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.neg 203), (Sat.Literal.neg 171), (Sat.Literal.pos 3185)] :=
  (lex_5_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3184), (Sat.Literal.pos 203), (Sat.Literal.pos 171), (Sat.Literal.pos 3185)] :=
  (lex_5_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3185) = lexBefore s permutation5 202 := by
  exact (positive_lex_of_descriptor s 3185 permutation5 203 (by rfl)).trans ((lex_skipped s permutation5 202 203 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation5 202) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation5 202 by rw [image5_eq]; rfl))

theorem lex_5_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3186) (Sat.Literal.pos 3185) (Sat.Literal.pos 202) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation5 202 (assignment s)
    (Sat.Literal.pos 3186) (Sat.Literal.pos 3185) (Sat.Literal.pos 202) (Sat.Literal.pos 170) (positive_of_descriptor s 3186 (.lex permutation5 202) (by rfl)) (lex_5_202_prefix s) (positive_select s 202) (lex_5_202_image s)

theorem lex_5_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.pos 202), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation5 202 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3185) (Sat.Literal.pos 202) (Sat.Literal.pos 170) (lex_5_202_prefix s) (positive_select s 202) (lex_5_202_image s)

theorem lex_5_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.pos 3185)] :=
  (lex_5_202_gate s).prop _ (List.Mem.head _)

theorem lex_5_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.neg 202), (Sat.Literal.pos 170)] :=
  (lex_5_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.pos 202), (Sat.Literal.neg 170)] :=
  (lex_5_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.neg 202), (Sat.Literal.neg 170), (Sat.Literal.pos 3186)] :=
  (lex_5_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3185), (Sat.Literal.pos 202), (Sat.Literal.pos 170), (Sat.Literal.pos 3186)] :=
  (lex_5_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3186) = lexBefore s permutation5 201 := by
  exact (positive_lex_of_descriptor s 3186 permutation5 202 (by rfl)).trans ((lex_skipped s permutation5 201 202 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation5 201) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation5 201 by rw [image5_eq]; rfl))

theorem lex_5_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3187) (Sat.Literal.pos 3186) (Sat.Literal.pos 201) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation5 201 (assignment s)
    (Sat.Literal.pos 3187) (Sat.Literal.pos 3186) (Sat.Literal.pos 201) (Sat.Literal.pos 169) (positive_of_descriptor s 3187 (.lex permutation5 201) (by rfl)) (lex_5_201_prefix s) (positive_select s 201) (lex_5_201_image s)

theorem lex_5_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.pos 201), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation5 201 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3186) (Sat.Literal.pos 201) (Sat.Literal.pos 169) (lex_5_201_prefix s) (positive_select s 201) (lex_5_201_image s)

theorem lex_5_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.pos 3186)] :=
  (lex_5_201_gate s).prop _ (List.Mem.head _)

theorem lex_5_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.neg 201), (Sat.Literal.pos 169)] :=
  (lex_5_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.pos 201), (Sat.Literal.neg 169)] :=
  (lex_5_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.neg 201), (Sat.Literal.neg 169), (Sat.Literal.pos 3187)] :=
  (lex_5_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3186), (Sat.Literal.pos 201), (Sat.Literal.pos 169), (Sat.Literal.pos 3187)] :=
  (lex_5_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3187) = lexBefore s permutation5 200 := by
  exact (positive_lex_of_descriptor s 3187 permutation5 201 (by rfl)).trans ((lex_skipped s permutation5 200 201 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation5 200) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation5 200 by rw [image5_eq]; rfl))

theorem lex_5_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3188) (Sat.Literal.pos 3187) (Sat.Literal.pos 200) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation5 200 (assignment s)
    (Sat.Literal.pos 3188) (Sat.Literal.pos 3187) (Sat.Literal.pos 200) (Sat.Literal.pos 168) (positive_of_descriptor s 3188 (.lex permutation5 200) (by rfl)) (lex_5_200_prefix s) (positive_select s 200) (lex_5_200_image s)

theorem lex_5_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.pos 200), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation5 200 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3187) (Sat.Literal.pos 200) (Sat.Literal.pos 168) (lex_5_200_prefix s) (positive_select s 200) (lex_5_200_image s)

theorem lex_5_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.pos 3187)] :=
  (lex_5_200_gate s).prop _ (List.Mem.head _)

theorem lex_5_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.neg 200), (Sat.Literal.pos 168)] :=
  (lex_5_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.pos 200), (Sat.Literal.neg 168)] :=
  (lex_5_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.neg 200), (Sat.Literal.neg 168), (Sat.Literal.pos 3188)] :=
  (lex_5_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3187), (Sat.Literal.pos 200), (Sat.Literal.pos 168), (Sat.Literal.pos 3188)] :=
  (lex_5_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3188) = lexBefore s permutation5 199 := by
  exact (positive_lex_of_descriptor s 3188 permutation5 200 (by rfl)).trans ((lex_skipped s permutation5 199 200 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation5 199) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation5 199 by rw [image5_eq]; rfl))

theorem lex_5_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3189) (Sat.Literal.pos 3188) (Sat.Literal.pos 199) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation5 199 (assignment s)
    (Sat.Literal.pos 3189) (Sat.Literal.pos 3188) (Sat.Literal.pos 199) (Sat.Literal.pos 167) (positive_of_descriptor s 3189 (.lex permutation5 199) (by rfl)) (lex_5_199_prefix s) (positive_select s 199) (lex_5_199_image s)

theorem lex_5_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.pos 199), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation5 199 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3188) (Sat.Literal.pos 199) (Sat.Literal.pos 167) (lex_5_199_prefix s) (positive_select s 199) (lex_5_199_image s)

theorem lex_5_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.pos 3188)] :=
  (lex_5_199_gate s).prop _ (List.Mem.head _)

theorem lex_5_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.neg 199), (Sat.Literal.pos 167)] :=
  (lex_5_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.pos 199), (Sat.Literal.neg 167)] :=
  (lex_5_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.neg 199), (Sat.Literal.neg 167), (Sat.Literal.pos 3189)] :=
  (lex_5_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3188), (Sat.Literal.pos 199), (Sat.Literal.pos 167), (Sat.Literal.pos 3189)] :=
  (lex_5_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3189) = lexBefore s permutation5 198 := by
  exact (positive_lex_of_descriptor s 3189 permutation5 199 (by rfl)).trans ((lex_skipped s permutation5 198 199 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation5 198) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation5 198 by rw [image5_eq]; rfl))

theorem lex_5_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3190) (Sat.Literal.pos 3189) (Sat.Literal.pos 198) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation5 198 (assignment s)
    (Sat.Literal.pos 3190) (Sat.Literal.pos 3189) (Sat.Literal.pos 198) (Sat.Literal.pos 166) (positive_of_descriptor s 3190 (.lex permutation5 198) (by rfl)) (lex_5_198_prefix s) (positive_select s 198) (lex_5_198_image s)

theorem lex_5_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.pos 198), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation5 198 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3189) (Sat.Literal.pos 198) (Sat.Literal.pos 166) (lex_5_198_prefix s) (positive_select s 198) (lex_5_198_image s)

theorem lex_5_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.pos 3189)] :=
  (lex_5_198_gate s).prop _ (List.Mem.head _)

theorem lex_5_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.neg 198), (Sat.Literal.pos 166)] :=
  (lex_5_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.pos 198), (Sat.Literal.neg 166)] :=
  (lex_5_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.neg 198), (Sat.Literal.neg 166), (Sat.Literal.pos 3190)] :=
  (lex_5_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3189), (Sat.Literal.pos 198), (Sat.Literal.pos 166), (Sat.Literal.pos 3190)] :=
  (lex_5_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3190) = lexBefore s permutation5 197 := by
  exact (positive_lex_of_descriptor s 3190 permutation5 198 (by rfl)).trans ((lex_skipped s permutation5 197 198 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation5 197) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation5 197 by rw [image5_eq]; rfl))

theorem lex_5_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3191) (Sat.Literal.pos 3190) (Sat.Literal.pos 197) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation5 197 (assignment s)
    (Sat.Literal.pos 3191) (Sat.Literal.pos 3190) (Sat.Literal.pos 197) (Sat.Literal.pos 165) (positive_of_descriptor s 3191 (.lex permutation5 197) (by rfl)) (lex_5_197_prefix s) (positive_select s 197) (lex_5_197_image s)

theorem lex_5_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.pos 197), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation5 197 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3190) (Sat.Literal.pos 197) (Sat.Literal.pos 165) (lex_5_197_prefix s) (positive_select s 197) (lex_5_197_image s)

theorem lex_5_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.pos 3190)] :=
  (lex_5_197_gate s).prop _ (List.Mem.head _)

theorem lex_5_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.neg 197), (Sat.Literal.pos 165)] :=
  (lex_5_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.pos 197), (Sat.Literal.neg 165)] :=
  (lex_5_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.neg 197), (Sat.Literal.neg 165), (Sat.Literal.pos 3191)] :=
  (lex_5_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3190), (Sat.Literal.pos 197), (Sat.Literal.pos 165), (Sat.Literal.pos 3191)] :=
  (lex_5_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3191) = lexBefore s permutation5 196 := by
  exact (positive_lex_of_descriptor s 3191 permutation5 197 (by rfl)).trans ((lex_skipped s permutation5 196 197 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation5 196) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation5 196 by rw [image5_eq]; rfl))

theorem lex_5_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3192) (Sat.Literal.pos 3191) (Sat.Literal.pos 196) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation5 196 (assignment s)
    (Sat.Literal.pos 3192) (Sat.Literal.pos 3191) (Sat.Literal.pos 196) (Sat.Literal.pos 164) (positive_of_descriptor s 3192 (.lex permutation5 196) (by rfl)) (lex_5_196_prefix s) (positive_select s 196) (lex_5_196_image s)

theorem lex_5_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.pos 196), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation5 196 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3191) (Sat.Literal.pos 196) (Sat.Literal.pos 164) (lex_5_196_prefix s) (positive_select s 196) (lex_5_196_image s)

theorem lex_5_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.pos 3191)] :=
  (lex_5_196_gate s).prop _ (List.Mem.head _)

theorem lex_5_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.neg 196), (Sat.Literal.pos 164)] :=
  (lex_5_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.pos 196), (Sat.Literal.neg 164)] :=
  (lex_5_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.neg 196), (Sat.Literal.neg 164), (Sat.Literal.pos 3192)] :=
  (lex_5_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3191), (Sat.Literal.pos 196), (Sat.Literal.pos 164), (Sat.Literal.pos 3192)] :=
  (lex_5_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3192) = lexBefore s permutation5 195 := by
  exact (positive_lex_of_descriptor s 3192 permutation5 196 (by rfl)).trans ((lex_skipped s permutation5 195 196 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation5 195) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation5 195 by rw [image5_eq]; rfl))

theorem lex_5_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3193) (Sat.Literal.pos 3192) (Sat.Literal.pos 195) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation5 195 (assignment s)
    (Sat.Literal.pos 3193) (Sat.Literal.pos 3192) (Sat.Literal.pos 195) (Sat.Literal.pos 163) (positive_of_descriptor s 3193 (.lex permutation5 195) (by rfl)) (lex_5_195_prefix s) (positive_select s 195) (lex_5_195_image s)

theorem lex_5_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.pos 195), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation5 195 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3192) (Sat.Literal.pos 195) (Sat.Literal.pos 163) (lex_5_195_prefix s) (positive_select s 195) (lex_5_195_image s)

theorem lex_5_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.pos 3192)] :=
  (lex_5_195_gate s).prop _ (List.Mem.head _)

theorem lex_5_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.neg 195), (Sat.Literal.pos 163)] :=
  (lex_5_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.pos 195), (Sat.Literal.neg 163)] :=
  (lex_5_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.neg 195), (Sat.Literal.neg 163), (Sat.Literal.pos 3193)] :=
  (lex_5_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3192), (Sat.Literal.pos 195), (Sat.Literal.pos 163), (Sat.Literal.pos 3193)] :=
  (lex_5_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3193) = lexBefore s permutation5 194 := by
  exact (positive_lex_of_descriptor s 3193 permutation5 195 (by rfl)).trans ((lex_skipped s permutation5 194 195 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation5 194) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation5 194 by rw [image5_eq]; rfl))

theorem lex_5_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3194) (Sat.Literal.pos 3193) (Sat.Literal.pos 194) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation5 194 (assignment s)
    (Sat.Literal.pos 3194) (Sat.Literal.pos 3193) (Sat.Literal.pos 194) (Sat.Literal.pos 162) (positive_of_descriptor s 3194 (.lex permutation5 194) (by rfl)) (lex_5_194_prefix s) (positive_select s 194) (lex_5_194_image s)

theorem lex_5_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.pos 194), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation5 194 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3193) (Sat.Literal.pos 194) (Sat.Literal.pos 162) (lex_5_194_prefix s) (positive_select s 194) (lex_5_194_image s)

theorem lex_5_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.pos 3193)] :=
  (lex_5_194_gate s).prop _ (List.Mem.head _)

theorem lex_5_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.neg 194), (Sat.Literal.pos 162)] :=
  (lex_5_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.pos 194), (Sat.Literal.neg 162)] :=
  (lex_5_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.neg 194), (Sat.Literal.neg 162), (Sat.Literal.pos 3194)] :=
  (lex_5_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3193), (Sat.Literal.pos 194), (Sat.Literal.pos 162), (Sat.Literal.pos 3194)] :=
  (lex_5_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3194) = lexBefore s permutation5 193 := by
  exact (positive_lex_of_descriptor s 3194 permutation5 194 (by rfl)).trans ((lex_skipped s permutation5 193 194 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation5 193) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation5 193 by rw [image5_eq]; rfl))

theorem lex_5_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3195) (Sat.Literal.pos 3194) (Sat.Literal.pos 193) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation5 193 (assignment s)
    (Sat.Literal.pos 3195) (Sat.Literal.pos 3194) (Sat.Literal.pos 193) (Sat.Literal.pos 161) (positive_of_descriptor s 3195 (.lex permutation5 193) (by rfl)) (lex_5_193_prefix s) (positive_select s 193) (lex_5_193_image s)

theorem lex_5_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.pos 193), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation5 193 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3194) (Sat.Literal.pos 193) (Sat.Literal.pos 161) (lex_5_193_prefix s) (positive_select s 193) (lex_5_193_image s)

theorem lex_5_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.pos 3194)] :=
  (lex_5_193_gate s).prop _ (List.Mem.head _)

theorem lex_5_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.neg 193), (Sat.Literal.pos 161)] :=
  (lex_5_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.pos 193), (Sat.Literal.neg 161)] :=
  (lex_5_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.neg 193), (Sat.Literal.neg 161), (Sat.Literal.pos 3195)] :=
  (lex_5_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3194), (Sat.Literal.pos 193), (Sat.Literal.pos 161), (Sat.Literal.pos 3195)] :=
  (lex_5_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3195) = lexBefore s permutation5 192 := by
  exact (positive_lex_of_descriptor s 3195 permutation5 193 (by rfl)).trans ((lex_skipped s permutation5 192 193 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation5 192) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation5 192 by rw [image5_eq]; rfl))

theorem lex_5_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3196) (Sat.Literal.pos 3195) (Sat.Literal.pos 192) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation5 192 (assignment s)
    (Sat.Literal.pos 3196) (Sat.Literal.pos 3195) (Sat.Literal.pos 192) (Sat.Literal.pos 160) (positive_of_descriptor s 3196 (.lex permutation5 192) (by rfl)) (lex_5_192_prefix s) (positive_select s 192) (lex_5_192_image s)

theorem lex_5_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.pos 192), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation5 192 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3195) (Sat.Literal.pos 192) (Sat.Literal.pos 160) (lex_5_192_prefix s) (positive_select s 192) (lex_5_192_image s)

theorem lex_5_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.pos 3195)] :=
  (lex_5_192_gate s).prop _ (List.Mem.head _)

theorem lex_5_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.neg 192), (Sat.Literal.pos 160)] :=
  (lex_5_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.pos 192), (Sat.Literal.neg 160)] :=
  (lex_5_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.neg 192), (Sat.Literal.neg 160), (Sat.Literal.pos 3196)] :=
  (lex_5_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3195), (Sat.Literal.pos 192), (Sat.Literal.pos 160), (Sat.Literal.pos 3196)] :=
  (lex_5_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3196) = lexBefore s permutation5 191 := by
  exact (positive_lex_of_descriptor s 3196 permutation5 192 (by rfl)).trans ((lex_skipped s permutation5 191 192 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation5 191) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation5 191 by rw [image5_eq]; rfl))

theorem lex_5_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3197) (Sat.Literal.pos 3196) (Sat.Literal.pos 191) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation5 191 (assignment s)
    (Sat.Literal.pos 3197) (Sat.Literal.pos 3196) (Sat.Literal.pos 191) (Sat.Literal.pos 223) (positive_of_descriptor s 3197 (.lex permutation5 191) (by rfl)) (lex_5_191_prefix s) (positive_select s 191) (lex_5_191_image s)

theorem lex_5_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.pos 191), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation5 191 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3196) (Sat.Literal.pos 191) (Sat.Literal.pos 223) (lex_5_191_prefix s) (positive_select s 191) (lex_5_191_image s)

theorem lex_5_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.pos 3196)] :=
  (lex_5_191_gate s).prop _ (List.Mem.head _)

theorem lex_5_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.neg 191), (Sat.Literal.pos 223)] :=
  (lex_5_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.pos 191), (Sat.Literal.neg 223)] :=
  (lex_5_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.neg 191), (Sat.Literal.neg 223), (Sat.Literal.pos 3197)] :=
  (lex_5_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3196), (Sat.Literal.pos 191), (Sat.Literal.pos 223), (Sat.Literal.pos 3197)] :=
  (lex_5_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3197) = lexBefore s permutation5 190 := by
  exact (positive_lex_of_descriptor s 3197 permutation5 191 (by rfl)).trans ((lex_skipped s permutation5 190 191 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation5 190) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation5 190 by rw [image5_eq]; rfl))

theorem lex_5_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3198) (Sat.Literal.pos 3197) (Sat.Literal.pos 190) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation5 190 (assignment s)
    (Sat.Literal.pos 3198) (Sat.Literal.pos 3197) (Sat.Literal.pos 190) (Sat.Literal.pos 222) (positive_of_descriptor s 3198 (.lex permutation5 190) (by rfl)) (lex_5_190_prefix s) (positive_select s 190) (lex_5_190_image s)

theorem lex_5_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.pos 190), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation5 190 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3197) (Sat.Literal.pos 190) (Sat.Literal.pos 222) (lex_5_190_prefix s) (positive_select s 190) (lex_5_190_image s)

theorem lex_5_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.pos 3197)] :=
  (lex_5_190_gate s).prop _ (List.Mem.head _)

theorem lex_5_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.neg 190), (Sat.Literal.pos 222)] :=
  (lex_5_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.pos 190), (Sat.Literal.neg 222)] :=
  (lex_5_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.neg 190), (Sat.Literal.neg 222), (Sat.Literal.pos 3198)] :=
  (lex_5_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3197), (Sat.Literal.pos 190), (Sat.Literal.pos 222), (Sat.Literal.pos 3198)] :=
  (lex_5_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3198) = lexBefore s permutation5 189 := by
  exact (positive_lex_of_descriptor s 3198 permutation5 190 (by rfl)).trans ((lex_skipped s permutation5 189 190 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation5 189) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation5 189 by rw [image5_eq]; rfl))

theorem lex_5_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3199) (Sat.Literal.pos 3198) (Sat.Literal.pos 189) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation5 189 (assignment s)
    (Sat.Literal.pos 3199) (Sat.Literal.pos 3198) (Sat.Literal.pos 189) (Sat.Literal.pos 221) (positive_of_descriptor s 3199 (.lex permutation5 189) (by rfl)) (lex_5_189_prefix s) (positive_select s 189) (lex_5_189_image s)

theorem lex_5_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.pos 189), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation5 189 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3198) (Sat.Literal.pos 189) (Sat.Literal.pos 221) (lex_5_189_prefix s) (positive_select s 189) (lex_5_189_image s)

theorem lex_5_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.pos 3198)] :=
  (lex_5_189_gate s).prop _ (List.Mem.head _)

theorem lex_5_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.neg 189), (Sat.Literal.pos 221)] :=
  (lex_5_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.pos 189), (Sat.Literal.neg 221)] :=
  (lex_5_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.neg 189), (Sat.Literal.neg 221), (Sat.Literal.pos 3199)] :=
  (lex_5_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3198), (Sat.Literal.pos 189), (Sat.Literal.pos 221), (Sat.Literal.pos 3199)] :=
  (lex_5_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3199) = lexBefore s permutation5 188 := by
  exact (positive_lex_of_descriptor s 3199 permutation5 189 (by rfl)).trans ((lex_skipped s permutation5 188 189 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation5 188) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation5 188 by rw [image5_eq]; rfl))

theorem lex_5_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3200) (Sat.Literal.pos 3199) (Sat.Literal.pos 188) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation5 188 (assignment s)
    (Sat.Literal.pos 3200) (Sat.Literal.pos 3199) (Sat.Literal.pos 188) (Sat.Literal.pos 220) (positive_of_descriptor s 3200 (.lex permutation5 188) (by rfl)) (lex_5_188_prefix s) (positive_select s 188) (lex_5_188_image s)

theorem lex_5_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.pos 188), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation5 188 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3199) (Sat.Literal.pos 188) (Sat.Literal.pos 220) (lex_5_188_prefix s) (positive_select s 188) (lex_5_188_image s)

theorem lex_5_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.pos 3199)] :=
  (lex_5_188_gate s).prop _ (List.Mem.head _)

theorem lex_5_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.neg 188), (Sat.Literal.pos 220)] :=
  (lex_5_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.pos 188), (Sat.Literal.neg 220)] :=
  (lex_5_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.neg 188), (Sat.Literal.neg 220), (Sat.Literal.pos 3200)] :=
  (lex_5_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3199), (Sat.Literal.pos 188), (Sat.Literal.pos 220), (Sat.Literal.pos 3200)] :=
  (lex_5_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3200) = lexBefore s permutation5 187 := by
  exact (positive_lex_of_descriptor s 3200 permutation5 188 (by rfl)).trans ((lex_skipped s permutation5 187 188 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation5 187) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation5 187 by rw [image5_eq]; rfl))

theorem lex_5_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3201) (Sat.Literal.pos 3200) (Sat.Literal.pos 187) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation5 187 (assignment s)
    (Sat.Literal.pos 3201) (Sat.Literal.pos 3200) (Sat.Literal.pos 187) (Sat.Literal.pos 219) (positive_of_descriptor s 3201 (.lex permutation5 187) (by rfl)) (lex_5_187_prefix s) (positive_select s 187) (lex_5_187_image s)

theorem lex_5_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.pos 187), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation5 187 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3200) (Sat.Literal.pos 187) (Sat.Literal.pos 219) (lex_5_187_prefix s) (positive_select s 187) (lex_5_187_image s)

theorem lex_5_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.pos 3200)] :=
  (lex_5_187_gate s).prop _ (List.Mem.head _)

theorem lex_5_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.neg 187), (Sat.Literal.pos 219)] :=
  (lex_5_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.pos 187), (Sat.Literal.neg 219)] :=
  (lex_5_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.neg 187), (Sat.Literal.neg 219), (Sat.Literal.pos 3201)] :=
  (lex_5_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3200), (Sat.Literal.pos 187), (Sat.Literal.pos 219), (Sat.Literal.pos 3201)] :=
  (lex_5_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3201) = lexBefore s permutation5 186 := by
  exact (positive_lex_of_descriptor s 3201 permutation5 187 (by rfl)).trans ((lex_skipped s permutation5 186 187 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation5 186) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation5 186 by rw [image5_eq]; rfl))

theorem lex_5_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3202) (Sat.Literal.pos 3201) (Sat.Literal.pos 186) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation5 186 (assignment s)
    (Sat.Literal.pos 3202) (Sat.Literal.pos 3201) (Sat.Literal.pos 186) (Sat.Literal.pos 218) (positive_of_descriptor s 3202 (.lex permutation5 186) (by rfl)) (lex_5_186_prefix s) (positive_select s 186) (lex_5_186_image s)

theorem lex_5_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.pos 186), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation5 186 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3201) (Sat.Literal.pos 186) (Sat.Literal.pos 218) (lex_5_186_prefix s) (positive_select s 186) (lex_5_186_image s)

theorem lex_5_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.pos 3201)] :=
  (lex_5_186_gate s).prop _ (List.Mem.head _)

theorem lex_5_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.neg 186), (Sat.Literal.pos 218)] :=
  (lex_5_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.pos 186), (Sat.Literal.neg 218)] :=
  (lex_5_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.neg 186), (Sat.Literal.neg 218), (Sat.Literal.pos 3202)] :=
  (lex_5_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3201), (Sat.Literal.pos 186), (Sat.Literal.pos 218), (Sat.Literal.pos 3202)] :=
  (lex_5_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3202) = lexBefore s permutation5 185 := by
  exact (positive_lex_of_descriptor s 3202 permutation5 186 (by rfl)).trans ((lex_skipped s permutation5 185 186 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation5 185) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation5 185 by rw [image5_eq]; rfl))

theorem lex_5_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3203) (Sat.Literal.pos 3202) (Sat.Literal.pos 185) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation5 185 (assignment s)
    (Sat.Literal.pos 3203) (Sat.Literal.pos 3202) (Sat.Literal.pos 185) (Sat.Literal.pos 217) (positive_of_descriptor s 3203 (.lex permutation5 185) (by rfl)) (lex_5_185_prefix s) (positive_select s 185) (lex_5_185_image s)

theorem lex_5_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.pos 185), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation5 185 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3202) (Sat.Literal.pos 185) (Sat.Literal.pos 217) (lex_5_185_prefix s) (positive_select s 185) (lex_5_185_image s)

theorem lex_5_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.pos 3202)] :=
  (lex_5_185_gate s).prop _ (List.Mem.head _)

theorem lex_5_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.neg 185), (Sat.Literal.pos 217)] :=
  (lex_5_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.pos 185), (Sat.Literal.neg 217)] :=
  (lex_5_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.neg 185), (Sat.Literal.neg 217), (Sat.Literal.pos 3203)] :=
  (lex_5_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3202), (Sat.Literal.pos 185), (Sat.Literal.pos 217), (Sat.Literal.pos 3203)] :=
  (lex_5_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3203) = lexBefore s permutation5 184 := by
  exact (positive_lex_of_descriptor s 3203 permutation5 185 (by rfl)).trans ((lex_skipped s permutation5 184 185 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation5 184) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation5 184 by rw [image5_eq]; rfl))

theorem lex_5_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3204) (Sat.Literal.pos 3203) (Sat.Literal.pos 184) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation5 184 (assignment s)
    (Sat.Literal.pos 3204) (Sat.Literal.pos 3203) (Sat.Literal.pos 184) (Sat.Literal.pos 216) (positive_of_descriptor s 3204 (.lex permutation5 184) (by rfl)) (lex_5_184_prefix s) (positive_select s 184) (lex_5_184_image s)

theorem lex_5_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.pos 184), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation5 184 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3203) (Sat.Literal.pos 184) (Sat.Literal.pos 216) (lex_5_184_prefix s) (positive_select s 184) (lex_5_184_image s)

theorem lex_5_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.pos 3203)] :=
  (lex_5_184_gate s).prop _ (List.Mem.head _)

theorem lex_5_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.neg 184), (Sat.Literal.pos 216)] :=
  (lex_5_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.pos 184), (Sat.Literal.neg 216)] :=
  (lex_5_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.neg 184), (Sat.Literal.neg 216), (Sat.Literal.pos 3204)] :=
  (lex_5_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3203), (Sat.Literal.pos 184), (Sat.Literal.pos 216), (Sat.Literal.pos 3204)] :=
  (lex_5_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3204) = lexBefore s permutation5 183 := by
  exact (positive_lex_of_descriptor s 3204 permutation5 184 (by rfl)).trans ((lex_skipped s permutation5 183 184 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation5 183) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation5 183 by rw [image5_eq]; rfl))

theorem lex_5_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3205) (Sat.Literal.pos 3204) (Sat.Literal.pos 183) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation5 183 (assignment s)
    (Sat.Literal.pos 3205) (Sat.Literal.pos 3204) (Sat.Literal.pos 183) (Sat.Literal.pos 215) (positive_of_descriptor s 3205 (.lex permutation5 183) (by rfl)) (lex_5_183_prefix s) (positive_select s 183) (lex_5_183_image s)

theorem lex_5_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.pos 183), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation5 183 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3204) (Sat.Literal.pos 183) (Sat.Literal.pos 215) (lex_5_183_prefix s) (positive_select s 183) (lex_5_183_image s)

theorem lex_5_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.pos 3204)] :=
  (lex_5_183_gate s).prop _ (List.Mem.head _)

theorem lex_5_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.neg 183), (Sat.Literal.pos 215)] :=
  (lex_5_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.pos 183), (Sat.Literal.neg 215)] :=
  (lex_5_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.neg 183), (Sat.Literal.neg 215), (Sat.Literal.pos 3205)] :=
  (lex_5_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3204), (Sat.Literal.pos 183), (Sat.Literal.pos 215), (Sat.Literal.pos 3205)] :=
  (lex_5_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3205) = lexBefore s permutation5 182 := by
  exact (positive_lex_of_descriptor s 3205 permutation5 183 (by rfl)).trans ((lex_skipped s permutation5 182 183 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation5 182) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation5 182 by rw [image5_eq]; rfl))

theorem lex_5_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3206) (Sat.Literal.pos 3205) (Sat.Literal.pos 182) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation5 182 (assignment s)
    (Sat.Literal.pos 3206) (Sat.Literal.pos 3205) (Sat.Literal.pos 182) (Sat.Literal.pos 214) (positive_of_descriptor s 3206 (.lex permutation5 182) (by rfl)) (lex_5_182_prefix s) (positive_select s 182) (lex_5_182_image s)

theorem lex_5_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.pos 182), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation5 182 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3205) (Sat.Literal.pos 182) (Sat.Literal.pos 214) (lex_5_182_prefix s) (positive_select s 182) (lex_5_182_image s)

theorem lex_5_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.pos 3205)] :=
  (lex_5_182_gate s).prop _ (List.Mem.head _)

theorem lex_5_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.neg 182), (Sat.Literal.pos 214)] :=
  (lex_5_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.pos 182), (Sat.Literal.neg 214)] :=
  (lex_5_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.neg 182), (Sat.Literal.neg 214), (Sat.Literal.pos 3206)] :=
  (lex_5_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3205), (Sat.Literal.pos 182), (Sat.Literal.pos 214), (Sat.Literal.pos 3206)] :=
  (lex_5_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3206) = lexBefore s permutation5 181 := by
  exact (positive_lex_of_descriptor s 3206 permutation5 182 (by rfl)).trans ((lex_skipped s permutation5 181 182 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation5 181) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation5 181 by rw [image5_eq]; rfl))

theorem lex_5_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3207) (Sat.Literal.pos 3206) (Sat.Literal.pos 181) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation5 181 (assignment s)
    (Sat.Literal.pos 3207) (Sat.Literal.pos 3206) (Sat.Literal.pos 181) (Sat.Literal.pos 213) (positive_of_descriptor s 3207 (.lex permutation5 181) (by rfl)) (lex_5_181_prefix s) (positive_select s 181) (lex_5_181_image s)

theorem lex_5_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.pos 181), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation5 181 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3206) (Sat.Literal.pos 181) (Sat.Literal.pos 213) (lex_5_181_prefix s) (positive_select s 181) (lex_5_181_image s)

theorem lex_5_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.pos 3206)] :=
  (lex_5_181_gate s).prop _ (List.Mem.head _)

theorem lex_5_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.neg 181), (Sat.Literal.pos 213)] :=
  (lex_5_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.pos 181), (Sat.Literal.neg 213)] :=
  (lex_5_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.neg 181), (Sat.Literal.neg 213), (Sat.Literal.pos 3207)] :=
  (lex_5_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3206), (Sat.Literal.pos 181), (Sat.Literal.pos 213), (Sat.Literal.pos 3207)] :=
  (lex_5_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3207) = lexBefore s permutation5 180 := by
  exact (positive_lex_of_descriptor s 3207 permutation5 181 (by rfl)).trans ((lex_skipped s permutation5 180 181 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation5 180) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation5 180 by rw [image5_eq]; rfl))

theorem lex_5_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3208) (Sat.Literal.pos 3207) (Sat.Literal.pos 180) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation5 180 (assignment s)
    (Sat.Literal.pos 3208) (Sat.Literal.pos 3207) (Sat.Literal.pos 180) (Sat.Literal.pos 212) (positive_of_descriptor s 3208 (.lex permutation5 180) (by rfl)) (lex_5_180_prefix s) (positive_select s 180) (lex_5_180_image s)

theorem lex_5_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.pos 180), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation5 180 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3207) (Sat.Literal.pos 180) (Sat.Literal.pos 212) (lex_5_180_prefix s) (positive_select s 180) (lex_5_180_image s)

theorem lex_5_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.pos 3207)] :=
  (lex_5_180_gate s).prop _ (List.Mem.head _)

theorem lex_5_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.neg 180), (Sat.Literal.pos 212)] :=
  (lex_5_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.pos 180), (Sat.Literal.neg 212)] :=
  (lex_5_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.neg 180), (Sat.Literal.neg 212), (Sat.Literal.pos 3208)] :=
  (lex_5_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3207), (Sat.Literal.pos 180), (Sat.Literal.pos 212), (Sat.Literal.pos 3208)] :=
  (lex_5_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3208) = lexBefore s permutation5 179 := by
  exact (positive_lex_of_descriptor s 3208 permutation5 180 (by rfl)).trans ((lex_skipped s permutation5 179 180 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation5 179) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation5 179 by rw [image5_eq]; rfl))

theorem lex_5_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3209) (Sat.Literal.pos 3208) (Sat.Literal.pos 179) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation5 179 (assignment s)
    (Sat.Literal.pos 3209) (Sat.Literal.pos 3208) (Sat.Literal.pos 179) (Sat.Literal.pos 211) (positive_of_descriptor s 3209 (.lex permutation5 179) (by rfl)) (lex_5_179_prefix s) (positive_select s 179) (lex_5_179_image s)

theorem lex_5_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.pos 179), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation5 179 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3208) (Sat.Literal.pos 179) (Sat.Literal.pos 211) (lex_5_179_prefix s) (positive_select s 179) (lex_5_179_image s)

theorem lex_5_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.pos 3208)] :=
  (lex_5_179_gate s).prop _ (List.Mem.head _)

theorem lex_5_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.neg 179), (Sat.Literal.pos 211)] :=
  (lex_5_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.pos 179), (Sat.Literal.neg 211)] :=
  (lex_5_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.neg 179), (Sat.Literal.neg 211), (Sat.Literal.pos 3209)] :=
  (lex_5_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3208), (Sat.Literal.pos 179), (Sat.Literal.pos 211), (Sat.Literal.pos 3209)] :=
  (lex_5_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3209) = lexBefore s permutation5 178 := by
  exact (positive_lex_of_descriptor s 3209 permutation5 179 (by rfl)).trans ((lex_skipped s permutation5 178 179 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation5 178) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation5 178 by rw [image5_eq]; rfl))

theorem lex_5_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3210) (Sat.Literal.pos 3209) (Sat.Literal.pos 178) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation5 178 (assignment s)
    (Sat.Literal.pos 3210) (Sat.Literal.pos 3209) (Sat.Literal.pos 178) (Sat.Literal.pos 210) (positive_of_descriptor s 3210 (.lex permutation5 178) (by rfl)) (lex_5_178_prefix s) (positive_select s 178) (lex_5_178_image s)

theorem lex_5_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.pos 178), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation5 178 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3209) (Sat.Literal.pos 178) (Sat.Literal.pos 210) (lex_5_178_prefix s) (positive_select s 178) (lex_5_178_image s)

theorem lex_5_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.pos 3209)] :=
  (lex_5_178_gate s).prop _ (List.Mem.head _)

theorem lex_5_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.neg 178), (Sat.Literal.pos 210)] :=
  (lex_5_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.pos 178), (Sat.Literal.neg 210)] :=
  (lex_5_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.neg 178), (Sat.Literal.neg 210), (Sat.Literal.pos 3210)] :=
  (lex_5_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3209), (Sat.Literal.pos 178), (Sat.Literal.pos 210), (Sat.Literal.pos 3210)] :=
  (lex_5_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3210) = lexBefore s permutation5 177 := by
  exact (positive_lex_of_descriptor s 3210 permutation5 178 (by rfl)).trans ((lex_skipped s permutation5 177 178 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation5 177) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation5 177 by rw [image5_eq]; rfl))

theorem lex_5_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3211) (Sat.Literal.pos 3210) (Sat.Literal.pos 177) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation5 177 (assignment s)
    (Sat.Literal.pos 3211) (Sat.Literal.pos 3210) (Sat.Literal.pos 177) (Sat.Literal.pos 209) (positive_of_descriptor s 3211 (.lex permutation5 177) (by rfl)) (lex_5_177_prefix s) (positive_select s 177) (lex_5_177_image s)

theorem lex_5_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.pos 177), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation5 177 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3210) (Sat.Literal.pos 177) (Sat.Literal.pos 209) (lex_5_177_prefix s) (positive_select s 177) (lex_5_177_image s)

theorem lex_5_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.pos 3210)] :=
  (lex_5_177_gate s).prop _ (List.Mem.head _)

theorem lex_5_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.neg 177), (Sat.Literal.pos 209)] :=
  (lex_5_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.pos 177), (Sat.Literal.neg 209)] :=
  (lex_5_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.neg 177), (Sat.Literal.neg 209), (Sat.Literal.pos 3211)] :=
  (lex_5_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3210), (Sat.Literal.pos 177), (Sat.Literal.pos 209), (Sat.Literal.pos 3211)] :=
  (lex_5_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3211) = lexBefore s permutation5 176 := by
  exact (positive_lex_of_descriptor s 3211 permutation5 177 (by rfl)).trans ((lex_skipped s permutation5 176 177 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation5 176) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation5 176 by rw [image5_eq]; rfl))

theorem lex_5_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3212) (Sat.Literal.pos 3211) (Sat.Literal.pos 176) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation5 176 (assignment s)
    (Sat.Literal.pos 3212) (Sat.Literal.pos 3211) (Sat.Literal.pos 176) (Sat.Literal.pos 208) (positive_of_descriptor s 3212 (.lex permutation5 176) (by rfl)) (lex_5_176_prefix s) (positive_select s 176) (lex_5_176_image s)

theorem lex_5_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.pos 176), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation5 176 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3211) (Sat.Literal.pos 176) (Sat.Literal.pos 208) (lex_5_176_prefix s) (positive_select s 176) (lex_5_176_image s)

theorem lex_5_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.pos 3211)] :=
  (lex_5_176_gate s).prop _ (List.Mem.head _)

theorem lex_5_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.neg 176), (Sat.Literal.pos 208)] :=
  (lex_5_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.pos 176), (Sat.Literal.neg 208)] :=
  (lex_5_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.neg 176), (Sat.Literal.neg 208), (Sat.Literal.pos 3212)] :=
  (lex_5_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3211), (Sat.Literal.pos 176), (Sat.Literal.pos 208), (Sat.Literal.pos 3212)] :=
  (lex_5_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3212) = lexBefore s permutation5 175 := by
  exact (positive_lex_of_descriptor s 3212 permutation5 176 (by rfl)).trans ((lex_skipped s permutation5 175 176 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation5 175) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation5 175 by rw [image5_eq]; rfl))

theorem lex_5_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3213) (Sat.Literal.pos 3212) (Sat.Literal.pos 175) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation5 175 (assignment s)
    (Sat.Literal.pos 3213) (Sat.Literal.pos 3212) (Sat.Literal.pos 175) (Sat.Literal.pos 207) (positive_of_descriptor s 3213 (.lex permutation5 175) (by rfl)) (lex_5_175_prefix s) (positive_select s 175) (lex_5_175_image s)

theorem lex_5_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.pos 175), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation5 175 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3212) (Sat.Literal.pos 175) (Sat.Literal.pos 207) (lex_5_175_prefix s) (positive_select s 175) (lex_5_175_image s)

theorem lex_5_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.pos 3212)] :=
  (lex_5_175_gate s).prop _ (List.Mem.head _)

theorem lex_5_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.neg 175), (Sat.Literal.pos 207)] :=
  (lex_5_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.pos 175), (Sat.Literal.neg 207)] :=
  (lex_5_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.neg 175), (Sat.Literal.neg 207), (Sat.Literal.pos 3213)] :=
  (lex_5_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3212), (Sat.Literal.pos 175), (Sat.Literal.pos 207), (Sat.Literal.pos 3213)] :=
  (lex_5_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3213) = lexBefore s permutation5 174 := by
  exact (positive_lex_of_descriptor s 3213 permutation5 175 (by rfl)).trans ((lex_skipped s permutation5 174 175 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation5 174) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation5 174 by rw [image5_eq]; rfl))

theorem lex_5_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3214) (Sat.Literal.pos 3213) (Sat.Literal.pos 174) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation5 174 (assignment s)
    (Sat.Literal.pos 3214) (Sat.Literal.pos 3213) (Sat.Literal.pos 174) (Sat.Literal.pos 206) (positive_of_descriptor s 3214 (.lex permutation5 174) (by rfl)) (lex_5_174_prefix s) (positive_select s 174) (lex_5_174_image s)

theorem lex_5_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.pos 174), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation5 174 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3213) (Sat.Literal.pos 174) (Sat.Literal.pos 206) (lex_5_174_prefix s) (positive_select s 174) (lex_5_174_image s)

theorem lex_5_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.pos 3213)] :=
  (lex_5_174_gate s).prop _ (List.Mem.head _)

theorem lex_5_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.neg 174), (Sat.Literal.pos 206)] :=
  (lex_5_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.pos 174), (Sat.Literal.neg 206)] :=
  (lex_5_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.neg 174), (Sat.Literal.neg 206), (Sat.Literal.pos 3214)] :=
  (lex_5_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3213), (Sat.Literal.pos 174), (Sat.Literal.pos 206), (Sat.Literal.pos 3214)] :=
  (lex_5_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3214) = lexBefore s permutation5 173 := by
  exact (positive_lex_of_descriptor s 3214 permutation5 174 (by rfl)).trans ((lex_skipped s permutation5 173 174 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation5 173) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation5 173 by rw [image5_eq]; rfl))

theorem lex_5_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3215) (Sat.Literal.pos 3214) (Sat.Literal.pos 173) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation5 173 (assignment s)
    (Sat.Literal.pos 3215) (Sat.Literal.pos 3214) (Sat.Literal.pos 173) (Sat.Literal.pos 205) (positive_of_descriptor s 3215 (.lex permutation5 173) (by rfl)) (lex_5_173_prefix s) (positive_select s 173) (lex_5_173_image s)

theorem lex_5_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.pos 173), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation5 173 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3214) (Sat.Literal.pos 173) (Sat.Literal.pos 205) (lex_5_173_prefix s) (positive_select s 173) (lex_5_173_image s)

theorem lex_5_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.pos 3214)] :=
  (lex_5_173_gate s).prop _ (List.Mem.head _)

theorem lex_5_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.neg 173), (Sat.Literal.pos 205)] :=
  (lex_5_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.pos 173), (Sat.Literal.neg 205)] :=
  (lex_5_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.neg 173), (Sat.Literal.neg 205), (Sat.Literal.pos 3215)] :=
  (lex_5_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3214), (Sat.Literal.pos 173), (Sat.Literal.pos 205), (Sat.Literal.pos 3215)] :=
  (lex_5_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3215) = lexBefore s permutation5 172 := by
  exact (positive_lex_of_descriptor s 3215 permutation5 173 (by rfl)).trans ((lex_skipped s permutation5 172 173 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation5 172) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation5 172 by rw [image5_eq]; rfl))

theorem lex_5_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3216) (Sat.Literal.pos 3215) (Sat.Literal.pos 172) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation5 172 (assignment s)
    (Sat.Literal.pos 3216) (Sat.Literal.pos 3215) (Sat.Literal.pos 172) (Sat.Literal.pos 204) (positive_of_descriptor s 3216 (.lex permutation5 172) (by rfl)) (lex_5_172_prefix s) (positive_select s 172) (lex_5_172_image s)

theorem lex_5_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.pos 172), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation5 172 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3215) (Sat.Literal.pos 172) (Sat.Literal.pos 204) (lex_5_172_prefix s) (positive_select s 172) (lex_5_172_image s)

theorem lex_5_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.pos 3215)] :=
  (lex_5_172_gate s).prop _ (List.Mem.head _)

theorem lex_5_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.neg 172), (Sat.Literal.pos 204)] :=
  (lex_5_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.pos 172), (Sat.Literal.neg 204)] :=
  (lex_5_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.neg 172), (Sat.Literal.neg 204), (Sat.Literal.pos 3216)] :=
  (lex_5_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3215), (Sat.Literal.pos 172), (Sat.Literal.pos 204), (Sat.Literal.pos 3216)] :=
  (lex_5_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3216) = lexBefore s permutation5 171 := by
  exact (positive_lex_of_descriptor s 3216 permutation5 172 (by rfl)).trans ((lex_skipped s permutation5 171 172 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation5 171) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation5 171 by rw [image5_eq]; rfl))

theorem lex_5_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3217) (Sat.Literal.pos 3216) (Sat.Literal.pos 171) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation5 171 (assignment s)
    (Sat.Literal.pos 3217) (Sat.Literal.pos 3216) (Sat.Literal.pos 171) (Sat.Literal.pos 203) (positive_of_descriptor s 3217 (.lex permutation5 171) (by rfl)) (lex_5_171_prefix s) (positive_select s 171) (lex_5_171_image s)

theorem lex_5_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.pos 171), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation5 171 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3216) (Sat.Literal.pos 171) (Sat.Literal.pos 203) (lex_5_171_prefix s) (positive_select s 171) (lex_5_171_image s)

theorem lex_5_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.pos 3216)] :=
  (lex_5_171_gate s).prop _ (List.Mem.head _)

theorem lex_5_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.neg 171), (Sat.Literal.pos 203)] :=
  (lex_5_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.pos 171), (Sat.Literal.neg 203)] :=
  (lex_5_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.neg 171), (Sat.Literal.neg 203), (Sat.Literal.pos 3217)] :=
  (lex_5_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3216), (Sat.Literal.pos 171), (Sat.Literal.pos 203), (Sat.Literal.pos 3217)] :=
  (lex_5_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3217) = lexBefore s permutation5 170 := by
  exact (positive_lex_of_descriptor s 3217 permutation5 171 (by rfl)).trans ((lex_skipped s permutation5 170 171 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation5 170) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation5 170 by rw [image5_eq]; rfl))

theorem lex_5_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3218) (Sat.Literal.pos 3217) (Sat.Literal.pos 170) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation5 170 (assignment s)
    (Sat.Literal.pos 3218) (Sat.Literal.pos 3217) (Sat.Literal.pos 170) (Sat.Literal.pos 202) (positive_of_descriptor s 3218 (.lex permutation5 170) (by rfl)) (lex_5_170_prefix s) (positive_select s 170) (lex_5_170_image s)

theorem lex_5_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.pos 170), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation5 170 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3217) (Sat.Literal.pos 170) (Sat.Literal.pos 202) (lex_5_170_prefix s) (positive_select s 170) (lex_5_170_image s)

theorem lex_5_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.pos 3217)] :=
  (lex_5_170_gate s).prop _ (List.Mem.head _)

theorem lex_5_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.neg 170), (Sat.Literal.pos 202)] :=
  (lex_5_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.pos 170), (Sat.Literal.neg 202)] :=
  (lex_5_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.neg 170), (Sat.Literal.neg 202), (Sat.Literal.pos 3218)] :=
  (lex_5_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3217), (Sat.Literal.pos 170), (Sat.Literal.pos 202), (Sat.Literal.pos 3218)] :=
  (lex_5_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3218) = lexBefore s permutation5 169 := by
  exact (positive_lex_of_descriptor s 3218 permutation5 170 (by rfl)).trans ((lex_skipped s permutation5 169 170 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation5 169) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation5 169 by rw [image5_eq]; rfl))

theorem lex_5_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3219) (Sat.Literal.pos 3218) (Sat.Literal.pos 169) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation5 169 (assignment s)
    (Sat.Literal.pos 3219) (Sat.Literal.pos 3218) (Sat.Literal.pos 169) (Sat.Literal.pos 201) (positive_of_descriptor s 3219 (.lex permutation5 169) (by rfl)) (lex_5_169_prefix s) (positive_select s 169) (lex_5_169_image s)

theorem lex_5_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.pos 169), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation5 169 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3218) (Sat.Literal.pos 169) (Sat.Literal.pos 201) (lex_5_169_prefix s) (positive_select s 169) (lex_5_169_image s)

theorem lex_5_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.pos 3218)] :=
  (lex_5_169_gate s).prop _ (List.Mem.head _)

theorem lex_5_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.neg 169), (Sat.Literal.pos 201)] :=
  (lex_5_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.pos 169), (Sat.Literal.neg 201)] :=
  (lex_5_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.neg 169), (Sat.Literal.neg 201), (Sat.Literal.pos 3219)] :=
  (lex_5_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3218), (Sat.Literal.pos 169), (Sat.Literal.pos 201), (Sat.Literal.pos 3219)] :=
  (lex_5_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3219) = lexBefore s permutation5 168 := by
  exact (positive_lex_of_descriptor s 3219 permutation5 169 (by rfl)).trans ((lex_skipped s permutation5 168 169 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation5 168) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation5 168 by rw [image5_eq]; rfl))

theorem lex_5_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3220) (Sat.Literal.pos 3219) (Sat.Literal.pos 168) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation5 168 (assignment s)
    (Sat.Literal.pos 3220) (Sat.Literal.pos 3219) (Sat.Literal.pos 168) (Sat.Literal.pos 200) (positive_of_descriptor s 3220 (.lex permutation5 168) (by rfl)) (lex_5_168_prefix s) (positive_select s 168) (lex_5_168_image s)

theorem lex_5_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.pos 168), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation5 168 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3219) (Sat.Literal.pos 168) (Sat.Literal.pos 200) (lex_5_168_prefix s) (positive_select s 168) (lex_5_168_image s)

theorem lex_5_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.pos 3219)] :=
  (lex_5_168_gate s).prop _ (List.Mem.head _)

theorem lex_5_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.neg 168), (Sat.Literal.pos 200)] :=
  (lex_5_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.pos 168), (Sat.Literal.neg 200)] :=
  (lex_5_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.neg 168), (Sat.Literal.neg 200), (Sat.Literal.pos 3220)] :=
  (lex_5_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3219), (Sat.Literal.pos 168), (Sat.Literal.pos 200), (Sat.Literal.pos 3220)] :=
  (lex_5_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3220) = lexBefore s permutation5 167 := by
  exact (positive_lex_of_descriptor s 3220 permutation5 168 (by rfl)).trans ((lex_skipped s permutation5 167 168 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation5 167) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation5 167 by rw [image5_eq]; rfl))

theorem lex_5_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3221) (Sat.Literal.pos 3220) (Sat.Literal.pos 167) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation5 167 (assignment s)
    (Sat.Literal.pos 3221) (Sat.Literal.pos 3220) (Sat.Literal.pos 167) (Sat.Literal.pos 199) (positive_of_descriptor s 3221 (.lex permutation5 167) (by rfl)) (lex_5_167_prefix s) (positive_select s 167) (lex_5_167_image s)

theorem lex_5_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.pos 167), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation5 167 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3220) (Sat.Literal.pos 167) (Sat.Literal.pos 199) (lex_5_167_prefix s) (positive_select s 167) (lex_5_167_image s)

theorem lex_5_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.pos 3220)] :=
  (lex_5_167_gate s).prop _ (List.Mem.head _)

theorem lex_5_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.neg 167), (Sat.Literal.pos 199)] :=
  (lex_5_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.pos 167), (Sat.Literal.neg 199)] :=
  (lex_5_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.neg 167), (Sat.Literal.neg 199), (Sat.Literal.pos 3221)] :=
  (lex_5_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3220), (Sat.Literal.pos 167), (Sat.Literal.pos 199), (Sat.Literal.pos 3221)] :=
  (lex_5_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3221) = lexBefore s permutation5 166 := by
  exact (positive_lex_of_descriptor s 3221 permutation5 167 (by rfl)).trans ((lex_skipped s permutation5 166 167 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation5 166) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation5 166 by rw [image5_eq]; rfl))

theorem lex_5_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3222) (Sat.Literal.pos 3221) (Sat.Literal.pos 166) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation5 166 (assignment s)
    (Sat.Literal.pos 3222) (Sat.Literal.pos 3221) (Sat.Literal.pos 166) (Sat.Literal.pos 198) (positive_of_descriptor s 3222 (.lex permutation5 166) (by rfl)) (lex_5_166_prefix s) (positive_select s 166) (lex_5_166_image s)

theorem lex_5_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.pos 166), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation5 166 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3221) (Sat.Literal.pos 166) (Sat.Literal.pos 198) (lex_5_166_prefix s) (positive_select s 166) (lex_5_166_image s)

theorem lex_5_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.pos 3221)] :=
  (lex_5_166_gate s).prop _ (List.Mem.head _)

theorem lex_5_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.neg 166), (Sat.Literal.pos 198)] :=
  (lex_5_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.pos 166), (Sat.Literal.neg 198)] :=
  (lex_5_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.neg 166), (Sat.Literal.neg 198), (Sat.Literal.pos 3222)] :=
  (lex_5_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3221), (Sat.Literal.pos 166), (Sat.Literal.pos 198), (Sat.Literal.pos 3222)] :=
  (lex_5_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3222) = lexBefore s permutation5 165 := by
  exact (positive_lex_of_descriptor s 3222 permutation5 166 (by rfl)).trans ((lex_skipped s permutation5 165 166 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation5 165) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation5 165 by rw [image5_eq]; rfl))

theorem lex_5_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3223) (Sat.Literal.pos 3222) (Sat.Literal.pos 165) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation5 165 (assignment s)
    (Sat.Literal.pos 3223) (Sat.Literal.pos 3222) (Sat.Literal.pos 165) (Sat.Literal.pos 197) (positive_of_descriptor s 3223 (.lex permutation5 165) (by rfl)) (lex_5_165_prefix s) (positive_select s 165) (lex_5_165_image s)

theorem lex_5_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.pos 165), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation5 165 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3222) (Sat.Literal.pos 165) (Sat.Literal.pos 197) (lex_5_165_prefix s) (positive_select s 165) (lex_5_165_image s)

theorem lex_5_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.pos 3222)] :=
  (lex_5_165_gate s).prop _ (List.Mem.head _)

theorem lex_5_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.neg 165), (Sat.Literal.pos 197)] :=
  (lex_5_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.pos 165), (Sat.Literal.neg 197)] :=
  (lex_5_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.neg 165), (Sat.Literal.neg 197), (Sat.Literal.pos 3223)] :=
  (lex_5_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3222), (Sat.Literal.pos 165), (Sat.Literal.pos 197), (Sat.Literal.pos 3223)] :=
  (lex_5_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3223) = lexBefore s permutation5 164 := by
  exact (positive_lex_of_descriptor s 3223 permutation5 165 (by rfl)).trans ((lex_skipped s permutation5 164 165 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation5 164) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation5 164 by rw [image5_eq]; rfl))

theorem lex_5_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3224) (Sat.Literal.pos 3223) (Sat.Literal.pos 164) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation5 164 (assignment s)
    (Sat.Literal.pos 3224) (Sat.Literal.pos 3223) (Sat.Literal.pos 164) (Sat.Literal.pos 196) (positive_of_descriptor s 3224 (.lex permutation5 164) (by rfl)) (lex_5_164_prefix s) (positive_select s 164) (lex_5_164_image s)

theorem lex_5_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.pos 164), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation5 164 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 3223) (Sat.Literal.pos 164) (Sat.Literal.pos 196) (lex_5_164_prefix s) (positive_select s 164) (lex_5_164_image s)

theorem lex_5_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.pos 3223)] :=
  (lex_5_164_gate s).prop _ (List.Mem.head _)

theorem lex_5_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.neg 164), (Sat.Literal.pos 196)] :=
  (lex_5_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3224), (Sat.Literal.pos 164), (Sat.Literal.neg 196)] :=
  (lex_5_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.neg 164), (Sat.Literal.neg 196), (Sat.Literal.pos 3224)] :=
  (lex_5_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3223), (Sat.Literal.pos 164), (Sat.Literal.pos 196), (Sat.Literal.pos 3224)] :=
  (lex_5_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_4_87_gate

end Crown.CertificateData
