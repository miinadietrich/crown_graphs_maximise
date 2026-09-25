import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_8_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3824) = lexBefore s permutation8 103 := by
  exact (positive_lex_of_descriptor s 3824 permutation8 104 (by rfl)).trans ((lex_skipped s permutation8 103 104 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation8 103) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation8 103 by rw [image8_eq]; rfl))

theorem lex_8_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3825) (Sat.Literal.pos 3824) (Sat.Literal.pos 103) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation8 103 (assignment s)
    (Sat.Literal.pos 3825) (Sat.Literal.pos 3824) (Sat.Literal.pos 103) (Sat.Literal.pos 157) (positive_of_descriptor s 3825 (.lex permutation8 103) (by rfl)) (lex_8_103_prefix s) (positive_select s 103) (lex_8_103_image s)

theorem lex_8_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.pos 103), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation8 103 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3824) (Sat.Literal.pos 103) (Sat.Literal.pos 157) (lex_8_103_prefix s) (positive_select s 103) (lex_8_103_image s)

theorem lex_8_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.pos 3824)] :=
  (lex_8_103_gate s).prop _ (List.Mem.head _)

theorem lex_8_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.neg 103), (Sat.Literal.pos 157)] :=
  (lex_8_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.pos 103), (Sat.Literal.neg 157)] :=
  (lex_8_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.neg 103), (Sat.Literal.neg 157), (Sat.Literal.pos 3825)] :=
  (lex_8_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3824), (Sat.Literal.pos 103), (Sat.Literal.pos 157), (Sat.Literal.pos 3825)] :=
  (lex_8_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3825) = lexBefore s permutation8 102 := by
  exact (positive_lex_of_descriptor s 3825 permutation8 103 (by rfl)).trans ((lex_skipped s permutation8 102 103 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation8 102) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation8 102 by rw [image8_eq]; rfl))

theorem lex_8_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3826) (Sat.Literal.pos 3825) (Sat.Literal.pos 102) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation8 102 (assignment s)
    (Sat.Literal.pos 3826) (Sat.Literal.pos 3825) (Sat.Literal.pos 102) (Sat.Literal.pos 153) (positive_of_descriptor s 3826 (.lex permutation8 102) (by rfl)) (lex_8_102_prefix s) (positive_select s 102) (lex_8_102_image s)

theorem lex_8_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.pos 102), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation8 102 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3825) (Sat.Literal.pos 102) (Sat.Literal.pos 153) (lex_8_102_prefix s) (positive_select s 102) (lex_8_102_image s)

theorem lex_8_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.pos 3825)] :=
  (lex_8_102_gate s).prop _ (List.Mem.head _)

theorem lex_8_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.neg 102), (Sat.Literal.pos 153)] :=
  (lex_8_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.pos 102), (Sat.Literal.neg 153)] :=
  (lex_8_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.neg 102), (Sat.Literal.neg 153), (Sat.Literal.pos 3826)] :=
  (lex_8_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3825), (Sat.Literal.pos 102), (Sat.Literal.pos 153), (Sat.Literal.pos 3826)] :=
  (lex_8_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3826) = lexBefore s permutation8 101 := by
  exact (positive_lex_of_descriptor s 3826 permutation8 102 (by rfl)).trans ((lex_skipped s permutation8 101 102 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation8 101) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation8 101 by rw [image8_eq]; rfl))

theorem lex_8_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3827) (Sat.Literal.pos 3826) (Sat.Literal.pos 101) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation8 101 (assignment s)
    (Sat.Literal.pos 3827) (Sat.Literal.pos 3826) (Sat.Literal.pos 101) (Sat.Literal.pos 149) (positive_of_descriptor s 3827 (.lex permutation8 101) (by rfl)) (lex_8_101_prefix s) (positive_select s 101) (lex_8_101_image s)

theorem lex_8_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.pos 101), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation8 101 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3826) (Sat.Literal.pos 101) (Sat.Literal.pos 149) (lex_8_101_prefix s) (positive_select s 101) (lex_8_101_image s)

theorem lex_8_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.pos 3826)] :=
  (lex_8_101_gate s).prop _ (List.Mem.head _)

theorem lex_8_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.neg 101), (Sat.Literal.pos 149)] :=
  (lex_8_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.pos 101), (Sat.Literal.neg 149)] :=
  (lex_8_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.neg 101), (Sat.Literal.neg 149), (Sat.Literal.pos 3827)] :=
  (lex_8_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3826), (Sat.Literal.pos 101), (Sat.Literal.pos 149), (Sat.Literal.pos 3827)] :=
  (lex_8_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3827) = lexBefore s permutation8 100 := by
  exact (positive_lex_of_descriptor s 3827 permutation8 101 (by rfl)).trans ((lex_skipped s permutation8 100 101 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation8 100) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation8 100 by rw [image8_eq]; rfl))

theorem lex_8_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3828) (Sat.Literal.pos 3827) (Sat.Literal.pos 100) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation8 100 (assignment s)
    (Sat.Literal.pos 3828) (Sat.Literal.pos 3827) (Sat.Literal.pos 100) (Sat.Literal.pos 145) (positive_of_descriptor s 3828 (.lex permutation8 100) (by rfl)) (lex_8_100_prefix s) (positive_select s 100) (lex_8_100_image s)

theorem lex_8_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.pos 100), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation8 100 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3827) (Sat.Literal.pos 100) (Sat.Literal.pos 145) (lex_8_100_prefix s) (positive_select s 100) (lex_8_100_image s)

theorem lex_8_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.pos 3827)] :=
  (lex_8_100_gate s).prop _ (List.Mem.head _)

theorem lex_8_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.neg 100), (Sat.Literal.pos 145)] :=
  (lex_8_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.pos 100), (Sat.Literal.neg 145)] :=
  (lex_8_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.neg 100), (Sat.Literal.neg 145), (Sat.Literal.pos 3828)] :=
  (lex_8_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3827), (Sat.Literal.pos 100), (Sat.Literal.pos 145), (Sat.Literal.pos 3828)] :=
  (lex_8_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3828) = lexBefore s permutation8 99 := by
  exact (positive_lex_of_descriptor s 3828 permutation8 100 (by rfl)).trans ((lex_skipped s permutation8 99 100 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation8 99) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation8 99 by rw [image8_eq]; rfl))

theorem lex_8_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3829) (Sat.Literal.pos 3828) (Sat.Literal.pos 99) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation8 99 (assignment s)
    (Sat.Literal.pos 3829) (Sat.Literal.pos 3828) (Sat.Literal.pos 99) (Sat.Literal.pos 141) (positive_of_descriptor s 3829 (.lex permutation8 99) (by rfl)) (lex_8_99_prefix s) (positive_select s 99) (lex_8_99_image s)

theorem lex_8_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.pos 99), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation8 99 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3828) (Sat.Literal.pos 99) (Sat.Literal.pos 141) (lex_8_99_prefix s) (positive_select s 99) (lex_8_99_image s)

theorem lex_8_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.pos 3828)] :=
  (lex_8_99_gate s).prop _ (List.Mem.head _)

theorem lex_8_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.neg 99), (Sat.Literal.pos 141)] :=
  (lex_8_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.pos 99), (Sat.Literal.neg 141)] :=
  (lex_8_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.neg 99), (Sat.Literal.neg 141), (Sat.Literal.pos 3829)] :=
  (lex_8_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3828), (Sat.Literal.pos 99), (Sat.Literal.pos 141), (Sat.Literal.pos 3829)] :=
  (lex_8_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3829) = lexBefore s permutation8 98 := by
  exact (positive_lex_of_descriptor s 3829 permutation8 99 (by rfl)).trans ((lex_skipped s permutation8 98 99 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation8 98) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation8 98 by rw [image8_eq]; rfl))

theorem lex_8_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3830) (Sat.Literal.pos 3829) (Sat.Literal.pos 98) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation8 98 (assignment s)
    (Sat.Literal.pos 3830) (Sat.Literal.pos 3829) (Sat.Literal.pos 98) (Sat.Literal.pos 137) (positive_of_descriptor s 3830 (.lex permutation8 98) (by rfl)) (lex_8_98_prefix s) (positive_select s 98) (lex_8_98_image s)

theorem lex_8_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.pos 98), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation8 98 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3829) (Sat.Literal.pos 98) (Sat.Literal.pos 137) (lex_8_98_prefix s) (positive_select s 98) (lex_8_98_image s)

theorem lex_8_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.pos 3829)] :=
  (lex_8_98_gate s).prop _ (List.Mem.head _)

theorem lex_8_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.neg 98), (Sat.Literal.pos 137)] :=
  (lex_8_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.pos 98), (Sat.Literal.neg 137)] :=
  (lex_8_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.neg 98), (Sat.Literal.neg 137), (Sat.Literal.pos 3830)] :=
  (lex_8_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3829), (Sat.Literal.pos 98), (Sat.Literal.pos 137), (Sat.Literal.pos 3830)] :=
  (lex_8_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3830) = lexBefore s permutation8 97 := by
  exact (positive_lex_of_descriptor s 3830 permutation8 98 (by rfl)).trans ((lex_skipped s permutation8 97 98 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation8 97) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation8 97 by rw [image8_eq]; rfl))

theorem lex_8_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3831) (Sat.Literal.pos 3830) (Sat.Literal.pos 97) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation8 97 (assignment s)
    (Sat.Literal.pos 3831) (Sat.Literal.pos 3830) (Sat.Literal.pos 97) (Sat.Literal.pos 133) (positive_of_descriptor s 3831 (.lex permutation8 97) (by rfl)) (lex_8_97_prefix s) (positive_select s 97) (lex_8_97_image s)

theorem lex_8_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.pos 97), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation8 97 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3830) (Sat.Literal.pos 97) (Sat.Literal.pos 133) (lex_8_97_prefix s) (positive_select s 97) (lex_8_97_image s)

theorem lex_8_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.pos 3830)] :=
  (lex_8_97_gate s).prop _ (List.Mem.head _)

theorem lex_8_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.neg 97), (Sat.Literal.pos 133)] :=
  (lex_8_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.pos 97), (Sat.Literal.neg 133)] :=
  (lex_8_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.neg 97), (Sat.Literal.neg 133), (Sat.Literal.pos 3831)] :=
  (lex_8_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3830), (Sat.Literal.pos 97), (Sat.Literal.pos 133), (Sat.Literal.pos 3831)] :=
  (lex_8_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3831) = lexBefore s permutation8 96 := by
  exact (positive_lex_of_descriptor s 3831 permutation8 97 (by rfl)).trans ((lex_skipped s permutation8 96 97 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation8 96) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation8 96 by rw [image8_eq]; rfl))

theorem lex_8_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3832) (Sat.Literal.pos 3831) (Sat.Literal.pos 96) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation8 96 (assignment s)
    (Sat.Literal.pos 3832) (Sat.Literal.pos 3831) (Sat.Literal.pos 96) (Sat.Literal.pos 129) (positive_of_descriptor s 3832 (.lex permutation8 96) (by rfl)) (lex_8_96_prefix s) (positive_select s 96) (lex_8_96_image s)

theorem lex_8_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.pos 96), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation8 96 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3831) (Sat.Literal.pos 96) (Sat.Literal.pos 129) (lex_8_96_prefix s) (positive_select s 96) (lex_8_96_image s)

theorem lex_8_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.pos 3831)] :=
  (lex_8_96_gate s).prop _ (List.Mem.head _)

theorem lex_8_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.neg 96), (Sat.Literal.pos 129)] :=
  (lex_8_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.pos 96), (Sat.Literal.neg 129)] :=
  (lex_8_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.neg 96), (Sat.Literal.neg 129), (Sat.Literal.pos 3832)] :=
  (lex_8_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3831), (Sat.Literal.pos 96), (Sat.Literal.pos 129), (Sat.Literal.pos 3832)] :=
  (lex_8_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3832) = lexBefore s permutation8 95 := by
  exact (positive_lex_of_descriptor s 3832 permutation8 96 (by rfl)).trans ((lex_skipped s permutation8 95 96 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation8 95) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation8 95 by rw [image8_eq]; rfl))

theorem lex_8_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3833) (Sat.Literal.pos 3832) (Sat.Literal.pos 95) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation8 95 (assignment s)
    (Sat.Literal.pos 3833) (Sat.Literal.pos 3832) (Sat.Literal.pos 95) (Sat.Literal.pos 125) (positive_of_descriptor s 3833 (.lex permutation8 95) (by rfl)) (lex_8_95_prefix s) (positive_select s 95) (lex_8_95_image s)

theorem lex_8_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.pos 95), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation8 95 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3832) (Sat.Literal.pos 95) (Sat.Literal.pos 125) (lex_8_95_prefix s) (positive_select s 95) (lex_8_95_image s)

theorem lex_8_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.pos 3832)] :=
  (lex_8_95_gate s).prop _ (List.Mem.head _)

theorem lex_8_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.neg 95), (Sat.Literal.pos 125)] :=
  (lex_8_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.pos 95), (Sat.Literal.neg 125)] :=
  (lex_8_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.neg 95), (Sat.Literal.neg 125), (Sat.Literal.pos 3833)] :=
  (lex_8_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3832), (Sat.Literal.pos 95), (Sat.Literal.pos 125), (Sat.Literal.pos 3833)] :=
  (lex_8_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3833) = lexBefore s permutation8 94 := by
  exact (positive_lex_of_descriptor s 3833 permutation8 95 (by rfl)).trans ((lex_skipped s permutation8 94 95 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation8 94) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation8 94 by rw [image8_eq]; rfl))

theorem lex_8_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3834) (Sat.Literal.pos 3833) (Sat.Literal.pos 94) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation8 94 (assignment s)
    (Sat.Literal.pos 3834) (Sat.Literal.pos 3833) (Sat.Literal.pos 94) (Sat.Literal.pos 121) (positive_of_descriptor s 3834 (.lex permutation8 94) (by rfl)) (lex_8_94_prefix s) (positive_select s 94) (lex_8_94_image s)

theorem lex_8_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.pos 94), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation8 94 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3833) (Sat.Literal.pos 94) (Sat.Literal.pos 121) (lex_8_94_prefix s) (positive_select s 94) (lex_8_94_image s)

theorem lex_8_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.pos 3833)] :=
  (lex_8_94_gate s).prop _ (List.Mem.head _)

theorem lex_8_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.neg 94), (Sat.Literal.pos 121)] :=
  (lex_8_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.pos 94), (Sat.Literal.neg 121)] :=
  (lex_8_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.neg 94), (Sat.Literal.neg 121), (Sat.Literal.pos 3834)] :=
  (lex_8_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3833), (Sat.Literal.pos 94), (Sat.Literal.pos 121), (Sat.Literal.pos 3834)] :=
  (lex_8_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3834) = lexBefore s permutation8 93 := by
  exact (positive_lex_of_descriptor s 3834 permutation8 94 (by rfl)).trans ((lex_skipped s permutation8 93 94 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation8 93) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation8 93 by rw [image8_eq]; rfl))

theorem lex_8_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3835) (Sat.Literal.pos 3834) (Sat.Literal.pos 93) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation8 93 (assignment s)
    (Sat.Literal.pos 3835) (Sat.Literal.pos 3834) (Sat.Literal.pos 93) (Sat.Literal.pos 117) (positive_of_descriptor s 3835 (.lex permutation8 93) (by rfl)) (lex_8_93_prefix s) (positive_select s 93) (lex_8_93_image s)

theorem lex_8_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.pos 93), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation8 93 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3834) (Sat.Literal.pos 93) (Sat.Literal.pos 117) (lex_8_93_prefix s) (positive_select s 93) (lex_8_93_image s)

theorem lex_8_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.pos 3834)] :=
  (lex_8_93_gate s).prop _ (List.Mem.head _)

theorem lex_8_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.neg 93), (Sat.Literal.pos 117)] :=
  (lex_8_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.pos 93), (Sat.Literal.neg 117)] :=
  (lex_8_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.neg 93), (Sat.Literal.neg 117), (Sat.Literal.pos 3835)] :=
  (lex_8_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3834), (Sat.Literal.pos 93), (Sat.Literal.pos 117), (Sat.Literal.pos 3835)] :=
  (lex_8_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3835) = lexBefore s permutation8 92 := by
  exact (positive_lex_of_descriptor s 3835 permutation8 93 (by rfl)).trans ((lex_skipped s permutation8 92 93 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation8 92) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation8 92 by rw [image8_eq]; rfl))

theorem lex_8_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3836) (Sat.Literal.pos 3835) (Sat.Literal.pos 92) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation8 92 (assignment s)
    (Sat.Literal.pos 3836) (Sat.Literal.pos 3835) (Sat.Literal.pos 92) (Sat.Literal.pos 113) (positive_of_descriptor s 3836 (.lex permutation8 92) (by rfl)) (lex_8_92_prefix s) (positive_select s 92) (lex_8_92_image s)

theorem lex_8_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.pos 92), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation8 92 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3835) (Sat.Literal.pos 92) (Sat.Literal.pos 113) (lex_8_92_prefix s) (positive_select s 92) (lex_8_92_image s)

theorem lex_8_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.pos 3835)] :=
  (lex_8_92_gate s).prop _ (List.Mem.head _)

theorem lex_8_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.neg 92), (Sat.Literal.pos 113)] :=
  (lex_8_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.pos 92), (Sat.Literal.neg 113)] :=
  (lex_8_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.neg 92), (Sat.Literal.neg 113), (Sat.Literal.pos 3836)] :=
  (lex_8_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3835), (Sat.Literal.pos 92), (Sat.Literal.pos 113), (Sat.Literal.pos 3836)] :=
  (lex_8_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3836) = lexBefore s permutation8 91 := by
  exact (positive_lex_of_descriptor s 3836 permutation8 92 (by rfl)).trans ((lex_skipped s permutation8 91 92 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation8 91) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation8 91 by rw [image8_eq]; rfl))

theorem lex_8_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3837) (Sat.Literal.pos 3836) (Sat.Literal.pos 91) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation8 91 (assignment s)
    (Sat.Literal.pos 3837) (Sat.Literal.pos 3836) (Sat.Literal.pos 91) (Sat.Literal.pos 109) (positive_of_descriptor s 3837 (.lex permutation8 91) (by rfl)) (lex_8_91_prefix s) (positive_select s 91) (lex_8_91_image s)

theorem lex_8_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.pos 91), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation8 91 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3836) (Sat.Literal.pos 91) (Sat.Literal.pos 109) (lex_8_91_prefix s) (positive_select s 91) (lex_8_91_image s)

theorem lex_8_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.pos 3836)] :=
  (lex_8_91_gate s).prop _ (List.Mem.head _)

theorem lex_8_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.neg 91), (Sat.Literal.pos 109)] :=
  (lex_8_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.pos 91), (Sat.Literal.neg 109)] :=
  (lex_8_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.neg 91), (Sat.Literal.neg 109), (Sat.Literal.pos 3837)] :=
  (lex_8_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3836), (Sat.Literal.pos 91), (Sat.Literal.pos 109), (Sat.Literal.pos 3837)] :=
  (lex_8_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3837) = lexBefore s permutation8 90 := by
  exact (positive_lex_of_descriptor s 3837 permutation8 91 (by rfl)).trans ((lex_skipped s permutation8 90 91 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation8 90) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation8 90 by rw [image8_eq]; rfl))

theorem lex_8_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3838) (Sat.Literal.pos 3837) (Sat.Literal.pos 90) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation8 90 (assignment s)
    (Sat.Literal.pos 3838) (Sat.Literal.pos 3837) (Sat.Literal.pos 90) (Sat.Literal.pos 105) (positive_of_descriptor s 3838 (.lex permutation8 90) (by rfl)) (lex_8_90_prefix s) (positive_select s 90) (lex_8_90_image s)

theorem lex_8_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.pos 90), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation8 90 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3837) (Sat.Literal.pos 90) (Sat.Literal.pos 105) (lex_8_90_prefix s) (positive_select s 90) (lex_8_90_image s)

theorem lex_8_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.pos 3837)] :=
  (lex_8_90_gate s).prop _ (List.Mem.head _)

theorem lex_8_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.neg 90), (Sat.Literal.pos 105)] :=
  (lex_8_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.pos 90), (Sat.Literal.neg 105)] :=
  (lex_8_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.neg 90), (Sat.Literal.neg 105), (Sat.Literal.pos 3838)] :=
  (lex_8_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3837), (Sat.Literal.pos 90), (Sat.Literal.pos 105), (Sat.Literal.pos 3838)] :=
  (lex_8_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3838) = lexBefore s permutation8 89 := by
  exact (positive_lex_of_descriptor s 3838 permutation8 90 (by rfl)).trans ((lex_skipped s permutation8 89 90 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation8 89) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation8 89 by rw [image8_eq]; rfl))

theorem lex_8_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3839) (Sat.Literal.pos 3838) (Sat.Literal.pos 89) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation8 89 (assignment s)
    (Sat.Literal.pos 3839) (Sat.Literal.pos 3838) (Sat.Literal.pos 89) (Sat.Literal.pos 101) (positive_of_descriptor s 3839 (.lex permutation8 89) (by rfl)) (lex_8_89_prefix s) (positive_select s 89) (lex_8_89_image s)

theorem lex_8_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.pos 89), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation8 89 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3838) (Sat.Literal.pos 89) (Sat.Literal.pos 101) (lex_8_89_prefix s) (positive_select s 89) (lex_8_89_image s)

theorem lex_8_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.pos 3838)] :=
  (lex_8_89_gate s).prop _ (List.Mem.head _)

theorem lex_8_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.neg 89), (Sat.Literal.pos 101)] :=
  (lex_8_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.pos 89), (Sat.Literal.neg 101)] :=
  (lex_8_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.neg 89), (Sat.Literal.neg 101), (Sat.Literal.pos 3839)] :=
  (lex_8_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3838), (Sat.Literal.pos 89), (Sat.Literal.pos 101), (Sat.Literal.pos 3839)] :=
  (lex_8_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3839) = lexBefore s permutation8 88 := by
  exact (positive_lex_of_descriptor s 3839 permutation8 89 (by rfl)).trans ((lex_skipped s permutation8 88 89 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation8 88) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation8 88 by rw [image8_eq]; rfl))

theorem lex_8_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3840) (Sat.Literal.pos 3839) (Sat.Literal.pos 88) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation8 88 (assignment s)
    (Sat.Literal.pos 3840) (Sat.Literal.pos 3839) (Sat.Literal.pos 88) (Sat.Literal.pos 97) (positive_of_descriptor s 3840 (.lex permutation8 88) (by rfl)) (lex_8_88_prefix s) (positive_select s 88) (lex_8_88_image s)

theorem lex_8_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.pos 88), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation8 88 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3839) (Sat.Literal.pos 88) (Sat.Literal.pos 97) (lex_8_88_prefix s) (positive_select s 88) (lex_8_88_image s)

theorem lex_8_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.pos 3839)] :=
  (lex_8_88_gate s).prop _ (List.Mem.head _)

theorem lex_8_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.neg 88), (Sat.Literal.pos 97)] :=
  (lex_8_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.pos 88), (Sat.Literal.neg 97)] :=
  (lex_8_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.neg 88), (Sat.Literal.neg 97), (Sat.Literal.pos 3840)] :=
  (lex_8_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3839), (Sat.Literal.pos 88), (Sat.Literal.pos 97), (Sat.Literal.pos 3840)] :=
  (lex_8_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3840) = lexBefore s permutation8 87 := by
  exact (positive_lex_of_descriptor s 3840 permutation8 88 (by rfl)).trans ((lex_skipped s permutation8 87 88 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation8 87) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation8 87 by rw [image8_eq]; rfl))

theorem lex_8_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3841) (Sat.Literal.pos 3840) (Sat.Literal.pos 87) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation8 87 (assignment s)
    (Sat.Literal.pos 3841) (Sat.Literal.pos 3840) (Sat.Literal.pos 87) (Sat.Literal.pos 93) (positive_of_descriptor s 3841 (.lex permutation8 87) (by rfl)) (lex_8_87_prefix s) (positive_select s 87) (lex_8_87_image s)

theorem lex_8_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.pos 87), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation8 87 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3840) (Sat.Literal.pos 87) (Sat.Literal.pos 93) (lex_8_87_prefix s) (positive_select s 87) (lex_8_87_image s)

theorem lex_8_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.pos 3840)] :=
  (lex_8_87_gate s).prop _ (List.Mem.head _)

theorem lex_8_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.neg 87), (Sat.Literal.pos 93)] :=
  (lex_8_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.pos 87), (Sat.Literal.neg 93)] :=
  (lex_8_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.neg 87), (Sat.Literal.neg 93), (Sat.Literal.pos 3841)] :=
  (lex_8_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3840), (Sat.Literal.pos 87), (Sat.Literal.pos 93), (Sat.Literal.pos 3841)] :=
  (lex_8_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3841) = lexBefore s permutation8 86 := by
  exact (positive_lex_of_descriptor s 3841 permutation8 87 (by rfl)).trans ((lex_skipped s permutation8 86 87 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation8 86) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation8 86 by rw [image8_eq]; rfl))

theorem lex_8_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3842) (Sat.Literal.pos 3841) (Sat.Literal.pos 86) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation8 86 (assignment s)
    (Sat.Literal.pos 3842) (Sat.Literal.pos 3841) (Sat.Literal.pos 86) (Sat.Literal.pos 89) (positive_of_descriptor s 3842 (.lex permutation8 86) (by rfl)) (lex_8_86_prefix s) (positive_select s 86) (lex_8_86_image s)

theorem lex_8_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.pos 86), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation8 86 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3841) (Sat.Literal.pos 86) (Sat.Literal.pos 89) (lex_8_86_prefix s) (positive_select s 86) (lex_8_86_image s)

theorem lex_8_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.pos 3841)] :=
  (lex_8_86_gate s).prop _ (List.Mem.head _)

theorem lex_8_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.neg 86), (Sat.Literal.pos 89)] :=
  (lex_8_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.pos 86), (Sat.Literal.neg 89)] :=
  (lex_8_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.neg 86), (Sat.Literal.neg 89), (Sat.Literal.pos 3842)] :=
  (lex_8_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3841), (Sat.Literal.pos 86), (Sat.Literal.pos 89), (Sat.Literal.pos 3842)] :=
  (lex_8_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3842) = lexBefore s permutation8 84 := by
  exact (positive_lex_of_descriptor s 3842 permutation8 86 (by rfl)).trans ((lex_skipped s permutation8 84 86 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 85 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation8 84) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation8 84 by rw [image8_eq]; rfl))

theorem lex_8_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3843) (Sat.Literal.pos 3842) (Sat.Literal.pos 84) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation8 84 (assignment s)
    (Sat.Literal.pos 3843) (Sat.Literal.pos 3842) (Sat.Literal.pos 84) (Sat.Literal.pos 81) (positive_of_descriptor s 3843 (.lex permutation8 84) (by rfl)) (lex_8_84_prefix s) (positive_select s 84) (lex_8_84_image s)

theorem lex_8_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.pos 84), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation8 84 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3842) (Sat.Literal.pos 84) (Sat.Literal.pos 81) (lex_8_84_prefix s) (positive_select s 84) (lex_8_84_image s)

theorem lex_8_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.pos 3842)] :=
  (lex_8_84_gate s).prop _ (List.Mem.head _)

theorem lex_8_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.neg 84), (Sat.Literal.pos 81)] :=
  (lex_8_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.pos 84), (Sat.Literal.neg 81)] :=
  (lex_8_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.neg 84), (Sat.Literal.neg 81), (Sat.Literal.pos 3843)] :=
  (lex_8_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3842), (Sat.Literal.pos 84), (Sat.Literal.pos 81), (Sat.Literal.pos 3843)] :=
  (lex_8_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3843) = lexBefore s permutation8 83 := by
  exact (positive_lex_of_descriptor s 3843 permutation8 84 (by rfl)).trans ((lex_skipped s permutation8 83 84 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation8 83) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation8 83 by rw [image8_eq]; rfl))

theorem lex_8_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3844) (Sat.Literal.pos 3843) (Sat.Literal.pos 83) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation8 83 (assignment s)
    (Sat.Literal.pos 3844) (Sat.Literal.pos 3843) (Sat.Literal.pos 83) (Sat.Literal.pos 77) (positive_of_descriptor s 3844 (.lex permutation8 83) (by rfl)) (lex_8_83_prefix s) (positive_select s 83) (lex_8_83_image s)

theorem lex_8_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.pos 83), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation8 83 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3843) (Sat.Literal.pos 83) (Sat.Literal.pos 77) (lex_8_83_prefix s) (positive_select s 83) (lex_8_83_image s)

theorem lex_8_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.pos 3843)] :=
  (lex_8_83_gate s).prop _ (List.Mem.head _)

theorem lex_8_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.neg 83), (Sat.Literal.pos 77)] :=
  (lex_8_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.pos 83), (Sat.Literal.neg 77)] :=
  (lex_8_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.neg 83), (Sat.Literal.neg 77), (Sat.Literal.pos 3844)] :=
  (lex_8_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3843), (Sat.Literal.pos 83), (Sat.Literal.pos 77), (Sat.Literal.pos 3844)] :=
  (lex_8_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3844) = lexBefore s permutation8 82 := by
  exact (positive_lex_of_descriptor s 3844 permutation8 83 (by rfl)).trans ((lex_skipped s permutation8 82 83 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation8 82) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation8 82 by rw [image8_eq]; rfl))

theorem lex_8_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3845) (Sat.Literal.pos 3844) (Sat.Literal.pos 82) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation8 82 (assignment s)
    (Sat.Literal.pos 3845) (Sat.Literal.pos 3844) (Sat.Literal.pos 82) (Sat.Literal.pos 73) (positive_of_descriptor s 3845 (.lex permutation8 82) (by rfl)) (lex_8_82_prefix s) (positive_select s 82) (lex_8_82_image s)

theorem lex_8_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.pos 82), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation8 82 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3844) (Sat.Literal.pos 82) (Sat.Literal.pos 73) (lex_8_82_prefix s) (positive_select s 82) (lex_8_82_image s)

theorem lex_8_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.pos 3844)] :=
  (lex_8_82_gate s).prop _ (List.Mem.head _)

theorem lex_8_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.neg 82), (Sat.Literal.pos 73)] :=
  (lex_8_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.pos 82), (Sat.Literal.neg 73)] :=
  (lex_8_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.neg 82), (Sat.Literal.neg 73), (Sat.Literal.pos 3845)] :=
  (lex_8_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3844), (Sat.Literal.pos 82), (Sat.Literal.pos 73), (Sat.Literal.pos 3845)] :=
  (lex_8_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3845) = lexBefore s permutation8 81 := by
  exact (positive_lex_of_descriptor s 3845 permutation8 82 (by rfl)).trans ((lex_skipped s permutation8 81 82 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation8 81) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation8 81 by rw [image8_eq]; rfl))

theorem lex_8_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3846) (Sat.Literal.pos 3845) (Sat.Literal.pos 81) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation8 81 (assignment s)
    (Sat.Literal.pos 3846) (Sat.Literal.pos 3845) (Sat.Literal.pos 81) (Sat.Literal.pos 69) (positive_of_descriptor s 3846 (.lex permutation8 81) (by rfl)) (lex_8_81_prefix s) (positive_select s 81) (lex_8_81_image s)

theorem lex_8_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.pos 81), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation8 81 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3845) (Sat.Literal.pos 81) (Sat.Literal.pos 69) (lex_8_81_prefix s) (positive_select s 81) (lex_8_81_image s)

theorem lex_8_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.pos 3845)] :=
  (lex_8_81_gate s).prop _ (List.Mem.head _)

theorem lex_8_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.neg 81), (Sat.Literal.pos 69)] :=
  (lex_8_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.pos 81), (Sat.Literal.neg 69)] :=
  (lex_8_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.neg 81), (Sat.Literal.neg 69), (Sat.Literal.pos 3846)] :=
  (lex_8_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3845), (Sat.Literal.pos 81), (Sat.Literal.pos 69), (Sat.Literal.pos 3846)] :=
  (lex_8_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3846) = lexBefore s permutation8 80 := by
  exact (positive_lex_of_descriptor s 3846 permutation8 81 (by rfl)).trans ((lex_skipped s permutation8 80 81 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation8 80) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation8 80 by rw [image8_eq]; rfl))

theorem lex_8_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3847) (Sat.Literal.pos 3846) (Sat.Literal.pos 80) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation8 80 (assignment s)
    (Sat.Literal.pos 3847) (Sat.Literal.pos 3846) (Sat.Literal.pos 80) (Sat.Literal.pos 65) (positive_of_descriptor s 3847 (.lex permutation8 80) (by rfl)) (lex_8_80_prefix s) (positive_select s 80) (lex_8_80_image s)

theorem lex_8_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.pos 80), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation8 80 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3846) (Sat.Literal.pos 80) (Sat.Literal.pos 65) (lex_8_80_prefix s) (positive_select s 80) (lex_8_80_image s)

theorem lex_8_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.pos 3846)] :=
  (lex_8_80_gate s).prop _ (List.Mem.head _)

theorem lex_8_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.neg 80), (Sat.Literal.pos 65)] :=
  (lex_8_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.pos 80), (Sat.Literal.neg 65)] :=
  (lex_8_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.neg 80), (Sat.Literal.neg 65), (Sat.Literal.pos 3847)] :=
  (lex_8_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3846), (Sat.Literal.pos 80), (Sat.Literal.pos 65), (Sat.Literal.pos 3847)] :=
  (lex_8_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3847) = lexBefore s permutation8 79 := by
  exact (positive_lex_of_descriptor s 3847 permutation8 80 (by rfl)).trans ((lex_skipped s permutation8 79 80 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation8 79) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation8 79 by rw [image8_eq]; rfl))

theorem lex_8_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3848) (Sat.Literal.pos 3847) (Sat.Literal.pos 79) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation8 79 (assignment s)
    (Sat.Literal.pos 3848) (Sat.Literal.pos 3847) (Sat.Literal.pos 79) (Sat.Literal.pos 61) (positive_of_descriptor s 3848 (.lex permutation8 79) (by rfl)) (lex_8_79_prefix s) (positive_select s 79) (lex_8_79_image s)

theorem lex_8_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.pos 79), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation8 79 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3847) (Sat.Literal.pos 79) (Sat.Literal.pos 61) (lex_8_79_prefix s) (positive_select s 79) (lex_8_79_image s)

theorem lex_8_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.pos 3847)] :=
  (lex_8_79_gate s).prop _ (List.Mem.head _)

theorem lex_8_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.neg 79), (Sat.Literal.pos 61)] :=
  (lex_8_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.pos 79), (Sat.Literal.neg 61)] :=
  (lex_8_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.neg 79), (Sat.Literal.neg 61), (Sat.Literal.pos 3848)] :=
  (lex_8_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3847), (Sat.Literal.pos 79), (Sat.Literal.pos 61), (Sat.Literal.pos 3848)] :=
  (lex_8_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3848) = lexBefore s permutation8 78 := by
  exact (positive_lex_of_descriptor s 3848 permutation8 79 (by rfl)).trans ((lex_skipped s permutation8 78 79 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation8 78) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation8 78 by rw [image8_eq]; rfl))

theorem lex_8_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3849) (Sat.Literal.pos 3848) (Sat.Literal.pos 78) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation8 78 (assignment s)
    (Sat.Literal.pos 3849) (Sat.Literal.pos 3848) (Sat.Literal.pos 78) (Sat.Literal.pos 57) (positive_of_descriptor s 3849 (.lex permutation8 78) (by rfl)) (lex_8_78_prefix s) (positive_select s 78) (lex_8_78_image s)

theorem lex_8_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.pos 78), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation8 78 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3848) (Sat.Literal.pos 78) (Sat.Literal.pos 57) (lex_8_78_prefix s) (positive_select s 78) (lex_8_78_image s)

theorem lex_8_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.pos 3848)] :=
  (lex_8_78_gate s).prop _ (List.Mem.head _)

theorem lex_8_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.neg 78), (Sat.Literal.pos 57)] :=
  (lex_8_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.pos 78), (Sat.Literal.neg 57)] :=
  (lex_8_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.neg 78), (Sat.Literal.neg 57), (Sat.Literal.pos 3849)] :=
  (lex_8_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3848), (Sat.Literal.pos 78), (Sat.Literal.pos 57), (Sat.Literal.pos 3849)] :=
  (lex_8_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3849) = lexBefore s permutation8 77 := by
  exact (positive_lex_of_descriptor s 3849 permutation8 78 (by rfl)).trans ((lex_skipped s permutation8 77 78 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation8 77) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation8 77 by rw [image8_eq]; rfl))

theorem lex_8_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3850) (Sat.Literal.pos 3849) (Sat.Literal.pos 77) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation8 77 (assignment s)
    (Sat.Literal.pos 3850) (Sat.Literal.pos 3849) (Sat.Literal.pos 77) (Sat.Literal.pos 53) (positive_of_descriptor s 3850 (.lex permutation8 77) (by rfl)) (lex_8_77_prefix s) (positive_select s 77) (lex_8_77_image s)

theorem lex_8_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.pos 77), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation8 77 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3849) (Sat.Literal.pos 77) (Sat.Literal.pos 53) (lex_8_77_prefix s) (positive_select s 77) (lex_8_77_image s)

theorem lex_8_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.pos 3849)] :=
  (lex_8_77_gate s).prop _ (List.Mem.head _)

theorem lex_8_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.neg 77), (Sat.Literal.pos 53)] :=
  (lex_8_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.pos 77), (Sat.Literal.neg 53)] :=
  (lex_8_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.neg 77), (Sat.Literal.neg 53), (Sat.Literal.pos 3850)] :=
  (lex_8_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3849), (Sat.Literal.pos 77), (Sat.Literal.pos 53), (Sat.Literal.pos 3850)] :=
  (lex_8_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3850) = lexBefore s permutation8 76 := by
  exact (positive_lex_of_descriptor s 3850 permutation8 77 (by rfl)).trans ((lex_skipped s permutation8 76 77 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation8 76) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation8 76 by rw [image8_eq]; rfl))

theorem lex_8_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3851) (Sat.Literal.pos 3850) (Sat.Literal.pos 76) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation8 76 (assignment s)
    (Sat.Literal.pos 3851) (Sat.Literal.pos 3850) (Sat.Literal.pos 76) (Sat.Literal.pos 49) (positive_of_descriptor s 3851 (.lex permutation8 76) (by rfl)) (lex_8_76_prefix s) (positive_select s 76) (lex_8_76_image s)

theorem lex_8_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.pos 76), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation8 76 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3850) (Sat.Literal.pos 76) (Sat.Literal.pos 49) (lex_8_76_prefix s) (positive_select s 76) (lex_8_76_image s)

theorem lex_8_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.pos 3850)] :=
  (lex_8_76_gate s).prop _ (List.Mem.head _)

theorem lex_8_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.neg 76), (Sat.Literal.pos 49)] :=
  (lex_8_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.pos 76), (Sat.Literal.neg 49)] :=
  (lex_8_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.neg 76), (Sat.Literal.neg 49), (Sat.Literal.pos 3851)] :=
  (lex_8_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3850), (Sat.Literal.pos 76), (Sat.Literal.pos 49), (Sat.Literal.pos 3851)] :=
  (lex_8_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3851) = lexBefore s permutation8 75 := by
  exact (positive_lex_of_descriptor s 3851 permutation8 76 (by rfl)).trans ((lex_skipped s permutation8 75 76 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation8 75) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation8 75 by rw [image8_eq]; rfl))

theorem lex_8_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3852) (Sat.Literal.pos 3851) (Sat.Literal.pos 75) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation8 75 (assignment s)
    (Sat.Literal.pos 3852) (Sat.Literal.pos 3851) (Sat.Literal.pos 75) (Sat.Literal.pos 45) (positive_of_descriptor s 3852 (.lex permutation8 75) (by rfl)) (lex_8_75_prefix s) (positive_select s 75) (lex_8_75_image s)

theorem lex_8_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.pos 75), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation8 75 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3851) (Sat.Literal.pos 75) (Sat.Literal.pos 45) (lex_8_75_prefix s) (positive_select s 75) (lex_8_75_image s)

theorem lex_8_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.pos 3851)] :=
  (lex_8_75_gate s).prop _ (List.Mem.head _)

theorem lex_8_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.neg 75), (Sat.Literal.pos 45)] :=
  (lex_8_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.pos 75), (Sat.Literal.neg 45)] :=
  (lex_8_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.neg 75), (Sat.Literal.neg 45), (Sat.Literal.pos 3852)] :=
  (lex_8_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3851), (Sat.Literal.pos 75), (Sat.Literal.pos 45), (Sat.Literal.pos 3852)] :=
  (lex_8_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3852) = lexBefore s permutation8 74 := by
  exact (positive_lex_of_descriptor s 3852 permutation8 75 (by rfl)).trans ((lex_skipped s permutation8 74 75 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation8 74) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation8 74 by rw [image8_eq]; rfl))

theorem lex_8_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3853) (Sat.Literal.pos 3852) (Sat.Literal.pos 74) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation8 74 (assignment s)
    (Sat.Literal.pos 3853) (Sat.Literal.pos 3852) (Sat.Literal.pos 74) (Sat.Literal.pos 41) (positive_of_descriptor s 3853 (.lex permutation8 74) (by rfl)) (lex_8_74_prefix s) (positive_select s 74) (lex_8_74_image s)

theorem lex_8_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.pos 74), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation8 74 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3852) (Sat.Literal.pos 74) (Sat.Literal.pos 41) (lex_8_74_prefix s) (positive_select s 74) (lex_8_74_image s)

theorem lex_8_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.pos 3852)] :=
  (lex_8_74_gate s).prop _ (List.Mem.head _)

theorem lex_8_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.neg 74), (Sat.Literal.pos 41)] :=
  (lex_8_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.pos 74), (Sat.Literal.neg 41)] :=
  (lex_8_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.neg 74), (Sat.Literal.neg 41), (Sat.Literal.pos 3853)] :=
  (lex_8_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3852), (Sat.Literal.pos 74), (Sat.Literal.pos 41), (Sat.Literal.pos 3853)] :=
  (lex_8_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3853) = lexBefore s permutation8 73 := by
  exact (positive_lex_of_descriptor s 3853 permutation8 74 (by rfl)).trans ((lex_skipped s permutation8 73 74 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation8 73) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation8 73 by rw [image8_eq]; rfl))

theorem lex_8_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3854) (Sat.Literal.pos 3853) (Sat.Literal.pos 73) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation8 73 (assignment s)
    (Sat.Literal.pos 3854) (Sat.Literal.pos 3853) (Sat.Literal.pos 73) (Sat.Literal.pos 37) (positive_of_descriptor s 3854 (.lex permutation8 73) (by rfl)) (lex_8_73_prefix s) (positive_select s 73) (lex_8_73_image s)

theorem lex_8_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.pos 73), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation8 73 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3853) (Sat.Literal.pos 73) (Sat.Literal.pos 37) (lex_8_73_prefix s) (positive_select s 73) (lex_8_73_image s)

theorem lex_8_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.pos 3853)] :=
  (lex_8_73_gate s).prop _ (List.Mem.head _)

theorem lex_8_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.neg 73), (Sat.Literal.pos 37)] :=
  (lex_8_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.pos 73), (Sat.Literal.neg 37)] :=
  (lex_8_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.neg 73), (Sat.Literal.neg 37), (Sat.Literal.pos 3854)] :=
  (lex_8_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3853), (Sat.Literal.pos 73), (Sat.Literal.pos 37), (Sat.Literal.pos 3854)] :=
  (lex_8_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3854) = lexBefore s permutation8 72 := by
  exact (positive_lex_of_descriptor s 3854 permutation8 73 (by rfl)).trans ((lex_skipped s permutation8 72 73 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation8 72) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation8 72 by rw [image8_eq]; rfl))

theorem lex_8_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3855) (Sat.Literal.pos 3854) (Sat.Literal.pos 72) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation8 72 (assignment s)
    (Sat.Literal.pos 3855) (Sat.Literal.pos 3854) (Sat.Literal.pos 72) (Sat.Literal.pos 33) (positive_of_descriptor s 3855 (.lex permutation8 72) (by rfl)) (lex_8_72_prefix s) (positive_select s 72) (lex_8_72_image s)

theorem lex_8_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.pos 72), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation8 72 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3854) (Sat.Literal.pos 72) (Sat.Literal.pos 33) (lex_8_72_prefix s) (positive_select s 72) (lex_8_72_image s)

theorem lex_8_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.pos 3854)] :=
  (lex_8_72_gate s).prop _ (List.Mem.head _)

theorem lex_8_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.neg 72), (Sat.Literal.pos 33)] :=
  (lex_8_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.pos 72), (Sat.Literal.neg 33)] :=
  (lex_8_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.neg 72), (Sat.Literal.neg 33), (Sat.Literal.pos 3855)] :=
  (lex_8_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3854), (Sat.Literal.pos 72), (Sat.Literal.pos 33), (Sat.Literal.pos 3855)] :=
  (lex_8_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3855) = lexBefore s permutation8 71 := by
  exact (positive_lex_of_descriptor s 3855 permutation8 72 (by rfl)).trans ((lex_skipped s permutation8 71 72 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation8 71) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation8 71 by rw [image8_eq]; rfl))

theorem lex_8_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3856) (Sat.Literal.pos 3855) (Sat.Literal.pos 71) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation8 71 (assignment s)
    (Sat.Literal.pos 3856) (Sat.Literal.pos 3855) (Sat.Literal.pos 71) (Sat.Literal.pos 29) (positive_of_descriptor s 3856 (.lex permutation8 71) (by rfl)) (lex_8_71_prefix s) (positive_select s 71) (lex_8_71_image s)

theorem lex_8_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.pos 71), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation8 71 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3855) (Sat.Literal.pos 71) (Sat.Literal.pos 29) (lex_8_71_prefix s) (positive_select s 71) (lex_8_71_image s)

theorem lex_8_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.pos 3855)] :=
  (lex_8_71_gate s).prop _ (List.Mem.head _)

theorem lex_8_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.neg 71), (Sat.Literal.pos 29)] :=
  (lex_8_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.pos 71), (Sat.Literal.neg 29)] :=
  (lex_8_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.neg 71), (Sat.Literal.neg 29), (Sat.Literal.pos 3856)] :=
  (lex_8_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3855), (Sat.Literal.pos 71), (Sat.Literal.pos 29), (Sat.Literal.pos 3856)] :=
  (lex_8_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3856) = lexBefore s permutation8 70 := by
  exact (positive_lex_of_descriptor s 3856 permutation8 71 (by rfl)).trans ((lex_skipped s permutation8 70 71 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation8 70) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation8 70 by rw [image8_eq]; rfl))

theorem lex_8_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3857) (Sat.Literal.pos 3856) (Sat.Literal.pos 70) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation8 70 (assignment s)
    (Sat.Literal.pos 3857) (Sat.Literal.pos 3856) (Sat.Literal.pos 70) (Sat.Literal.pos 25) (positive_of_descriptor s 3857 (.lex permutation8 70) (by rfl)) (lex_8_70_prefix s) (positive_select s 70) (lex_8_70_image s)

theorem lex_8_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.pos 70), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation8 70 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3856) (Sat.Literal.pos 70) (Sat.Literal.pos 25) (lex_8_70_prefix s) (positive_select s 70) (lex_8_70_image s)

theorem lex_8_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.pos 3856)] :=
  (lex_8_70_gate s).prop _ (List.Mem.head _)

theorem lex_8_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.neg 70), (Sat.Literal.pos 25)] :=
  (lex_8_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.pos 70), (Sat.Literal.neg 25)] :=
  (lex_8_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.neg 70), (Sat.Literal.neg 25), (Sat.Literal.pos 3857)] :=
  (lex_8_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3856), (Sat.Literal.pos 70), (Sat.Literal.pos 25), (Sat.Literal.pos 3857)] :=
  (lex_8_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3857) = lexBefore s permutation8 69 := by
  exact (positive_lex_of_descriptor s 3857 permutation8 70 (by rfl)).trans ((lex_skipped s permutation8 69 70 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation8 69) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation8 69 by rw [image8_eq]; rfl))

theorem lex_8_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3858) (Sat.Literal.pos 3857) (Sat.Literal.pos 69) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation8 69 (assignment s)
    (Sat.Literal.pos 3858) (Sat.Literal.pos 3857) (Sat.Literal.pos 69) (Sat.Literal.pos 21) (positive_of_descriptor s 3858 (.lex permutation8 69) (by rfl)) (lex_8_69_prefix s) (positive_select s 69) (lex_8_69_image s)

theorem lex_8_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.pos 69), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation8 69 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3857) (Sat.Literal.pos 69) (Sat.Literal.pos 21) (lex_8_69_prefix s) (positive_select s 69) (lex_8_69_image s)

theorem lex_8_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.pos 3857)] :=
  (lex_8_69_gate s).prop _ (List.Mem.head _)

theorem lex_8_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.neg 69), (Sat.Literal.pos 21)] :=
  (lex_8_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.pos 69), (Sat.Literal.neg 21)] :=
  (lex_8_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.neg 69), (Sat.Literal.neg 21), (Sat.Literal.pos 3858)] :=
  (lex_8_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3857), (Sat.Literal.pos 69), (Sat.Literal.pos 21), (Sat.Literal.pos 3858)] :=
  (lex_8_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3858) = lexBefore s permutation8 68 := by
  exact (positive_lex_of_descriptor s 3858 permutation8 69 (by rfl)).trans ((lex_skipped s permutation8 68 69 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation8 68) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation8 68 by rw [image8_eq]; rfl))

theorem lex_8_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3859) (Sat.Literal.pos 3858) (Sat.Literal.pos 68) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation8 68 (assignment s)
    (Sat.Literal.pos 3859) (Sat.Literal.pos 3858) (Sat.Literal.pos 68) (Sat.Literal.pos 17) (positive_of_descriptor s 3859 (.lex permutation8 68) (by rfl)) (lex_8_68_prefix s) (positive_select s 68) (lex_8_68_image s)

theorem lex_8_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.pos 68), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation8 68 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3858) (Sat.Literal.pos 68) (Sat.Literal.pos 17) (lex_8_68_prefix s) (positive_select s 68) (lex_8_68_image s)

theorem lex_8_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.pos 3858)] :=
  (lex_8_68_gate s).prop _ (List.Mem.head _)

theorem lex_8_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.neg 68), (Sat.Literal.pos 17)] :=
  (lex_8_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.pos 68), (Sat.Literal.neg 17)] :=
  (lex_8_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.neg 68), (Sat.Literal.neg 17), (Sat.Literal.pos 3859)] :=
  (lex_8_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3858), (Sat.Literal.pos 68), (Sat.Literal.pos 17), (Sat.Literal.pos 3859)] :=
  (lex_8_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3859) = lexBefore s permutation8 67 := by
  exact (positive_lex_of_descriptor s 3859 permutation8 68 (by rfl)).trans ((lex_skipped s permutation8 67 68 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation8 67) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation8 67 by rw [image8_eq]; rfl))

theorem lex_8_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3860) (Sat.Literal.pos 3859) (Sat.Literal.pos 67) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation8 67 (assignment s)
    (Sat.Literal.pos 3860) (Sat.Literal.pos 3859) (Sat.Literal.pos 67) (Sat.Literal.pos 13) (positive_of_descriptor s 3860 (.lex permutation8 67) (by rfl)) (lex_8_67_prefix s) (positive_select s 67) (lex_8_67_image s)

theorem lex_8_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.pos 67), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation8 67 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3859) (Sat.Literal.pos 67) (Sat.Literal.pos 13) (lex_8_67_prefix s) (positive_select s 67) (lex_8_67_image s)

theorem lex_8_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.pos 3859)] :=
  (lex_8_67_gate s).prop _ (List.Mem.head _)

theorem lex_8_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.neg 67), (Sat.Literal.pos 13)] :=
  (lex_8_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.pos 67), (Sat.Literal.neg 13)] :=
  (lex_8_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.neg 67), (Sat.Literal.neg 13), (Sat.Literal.pos 3860)] :=
  (lex_8_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3859), (Sat.Literal.pos 67), (Sat.Literal.pos 13), (Sat.Literal.pos 3860)] :=
  (lex_8_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3860) = lexBefore s permutation8 66 := by
  exact (positive_lex_of_descriptor s 3860 permutation8 67 (by rfl)).trans ((lex_skipped s permutation8 66 67 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation8 66) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation8 66 by rw [image8_eq]; rfl))

theorem lex_8_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3861) (Sat.Literal.pos 3860) (Sat.Literal.pos 66) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation8 66 (assignment s)
    (Sat.Literal.pos 3861) (Sat.Literal.pos 3860) (Sat.Literal.pos 66) (Sat.Literal.pos 9) (positive_of_descriptor s 3861 (.lex permutation8 66) (by rfl)) (lex_8_66_prefix s) (positive_select s 66) (lex_8_66_image s)

theorem lex_8_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.pos 66), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation8 66 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3860) (Sat.Literal.pos 66) (Sat.Literal.pos 9) (lex_8_66_prefix s) (positive_select s 66) (lex_8_66_image s)

theorem lex_8_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.pos 3860)] :=
  (lex_8_66_gate s).prop _ (List.Mem.head _)

theorem lex_8_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.neg 66), (Sat.Literal.pos 9)] :=
  (lex_8_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.pos 66), (Sat.Literal.neg 9)] :=
  (lex_8_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.neg 66), (Sat.Literal.neg 9), (Sat.Literal.pos 3861)] :=
  (lex_8_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3860), (Sat.Literal.pos 66), (Sat.Literal.pos 9), (Sat.Literal.pos 3861)] :=
  (lex_8_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3861) = lexBefore s permutation8 65 := by
  exact (positive_lex_of_descriptor s 3861 permutation8 66 (by rfl)).trans ((lex_skipped s permutation8 65 66 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation8 65) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation8 65 by rw [image8_eq]; rfl))

theorem lex_8_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3862) (Sat.Literal.pos 3861) (Sat.Literal.pos 65) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation8 65 (assignment s)
    (Sat.Literal.pos 3862) (Sat.Literal.pos 3861) (Sat.Literal.pos 65) (Sat.Literal.pos 5) (positive_of_descriptor s 3862 (.lex permutation8 65) (by rfl)) (lex_8_65_prefix s) (positive_select s 65) (lex_8_65_image s)

theorem lex_8_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.pos 65), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation8 65 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3861) (Sat.Literal.pos 65) (Sat.Literal.pos 5) (lex_8_65_prefix s) (positive_select s 65) (lex_8_65_image s)

theorem lex_8_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.pos 3861)] :=
  (lex_8_65_gate s).prop _ (List.Mem.head _)

theorem lex_8_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.neg 65), (Sat.Literal.pos 5)] :=
  (lex_8_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.pos 65), (Sat.Literal.neg 5)] :=
  (lex_8_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.neg 65), (Sat.Literal.neg 5), (Sat.Literal.pos 3862)] :=
  (lex_8_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3861), (Sat.Literal.pos 65), (Sat.Literal.pos 5), (Sat.Literal.pos 3862)] :=
  (lex_8_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3862) = lexBefore s permutation8 64 := by
  exact (positive_lex_of_descriptor s 3862 permutation8 65 (by rfl)).trans ((lex_skipped s permutation8 64 65 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation8 64) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation8 64 by rw [image8_eq]; rfl))

theorem lex_8_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3863) (Sat.Literal.pos 3862) (Sat.Literal.pos 64) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation8 64 (assignment s)
    (Sat.Literal.pos 3863) (Sat.Literal.pos 3862) (Sat.Literal.pos 64) (Sat.Literal.pos 1) (positive_of_descriptor s 3863 (.lex permutation8 64) (by rfl)) (lex_8_64_prefix s) (positive_select s 64) (lex_8_64_image s)

theorem lex_8_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.pos 64), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation8 64 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3862) (Sat.Literal.pos 64) (Sat.Literal.pos 1) (lex_8_64_prefix s) (positive_select s 64) (lex_8_64_image s)

theorem lex_8_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.pos 3862)] :=
  (lex_8_64_gate s).prop _ (List.Mem.head _)

theorem lex_8_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.neg 64), (Sat.Literal.pos 1)] :=
  (lex_8_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.pos 64), (Sat.Literal.neg 1)] :=
  (lex_8_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.neg 64), (Sat.Literal.neg 1), (Sat.Literal.pos 3863)] :=
  (lex_8_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3862), (Sat.Literal.pos 64), (Sat.Literal.pos 1), (Sat.Literal.pos 3863)] :=
  (lex_8_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3863) = lexBefore s permutation8 63 := by
  exact (positive_lex_of_descriptor s 3863 permutation8 64 (by rfl)).trans ((lex_skipped s permutation8 63 64 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation8 63) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation8 63 by rw [image8_eq]; rfl))

theorem lex_8_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3864) (Sat.Literal.pos 3863) (Sat.Literal.pos 63) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation8 63 (assignment s)
    (Sat.Literal.pos 3864) (Sat.Literal.pos 3863) (Sat.Literal.pos 63) (Sat.Literal.pos 252) (positive_of_descriptor s 3864 (.lex permutation8 63) (by rfl)) (lex_8_63_prefix s) (positive_select s 63) (lex_8_63_image s)

theorem lex_8_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.pos 63), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation8 63 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3863) (Sat.Literal.pos 63) (Sat.Literal.pos 252) (lex_8_63_prefix s) (positive_select s 63) (lex_8_63_image s)

theorem lex_8_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.pos 3863)] :=
  (lex_8_63_gate s).prop _ (List.Mem.head _)

theorem lex_8_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.neg 63), (Sat.Literal.pos 252)] :=
  (lex_8_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.pos 63), (Sat.Literal.neg 252)] :=
  (lex_8_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.neg 63), (Sat.Literal.neg 252), (Sat.Literal.pos 3864)] :=
  (lex_8_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3863), (Sat.Literal.pos 63), (Sat.Literal.pos 252), (Sat.Literal.pos 3864)] :=
  (lex_8_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3864) = lexBefore s permutation8 62 := by
  exact (positive_lex_of_descriptor s 3864 permutation8 63 (by rfl)).trans ((lex_skipped s permutation8 62 63 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation8 62) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation8 62 by rw [image8_eq]; rfl))

theorem lex_8_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3865) (Sat.Literal.pos 3864) (Sat.Literal.pos 62) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation8 62 (assignment s)
    (Sat.Literal.pos 3865) (Sat.Literal.pos 3864) (Sat.Literal.pos 62) (Sat.Literal.pos 248) (positive_of_descriptor s 3865 (.lex permutation8 62) (by rfl)) (lex_8_62_prefix s) (positive_select s 62) (lex_8_62_image s)

theorem lex_8_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.pos 62), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation8 62 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3864) (Sat.Literal.pos 62) (Sat.Literal.pos 248) (lex_8_62_prefix s) (positive_select s 62) (lex_8_62_image s)

theorem lex_8_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.pos 3864)] :=
  (lex_8_62_gate s).prop _ (List.Mem.head _)

theorem lex_8_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.neg 62), (Sat.Literal.pos 248)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.pos 62), (Sat.Literal.neg 248)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.neg 62), (Sat.Literal.neg 248), (Sat.Literal.pos 3865)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3864), (Sat.Literal.pos 62), (Sat.Literal.pos 248), (Sat.Literal.pos 3865)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3865) = lexBefore s permutation8 61 := by
  exact (positive_lex_of_descriptor s 3865 permutation8 62 (by rfl)).trans ((lex_skipped s permutation8 61 62 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation8 61) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation8 61 by rw [image8_eq]; rfl))

theorem lex_8_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3866) (Sat.Literal.pos 3865) (Sat.Literal.pos 61) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation8 61 (assignment s)
    (Sat.Literal.pos 3866) (Sat.Literal.pos 3865) (Sat.Literal.pos 61) (Sat.Literal.pos 244) (positive_of_descriptor s 3866 (.lex permutation8 61) (by rfl)) (lex_8_61_prefix s) (positive_select s 61) (lex_8_61_image s)

theorem lex_8_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.pos 61), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation8 61 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3865) (Sat.Literal.pos 61) (Sat.Literal.pos 244) (lex_8_61_prefix s) (positive_select s 61) (lex_8_61_image s)

theorem lex_8_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.pos 3865)] :=
  (lex_8_61_gate s).prop _ (List.Mem.head _)

theorem lex_8_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.neg 61), (Sat.Literal.pos 244)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.pos 61), (Sat.Literal.neg 244)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.neg 61), (Sat.Literal.neg 244), (Sat.Literal.pos 3866)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3865), (Sat.Literal.pos 61), (Sat.Literal.pos 244), (Sat.Literal.pos 3866)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3866) = lexBefore s permutation8 60 := by
  exact (positive_lex_of_descriptor s 3866 permutation8 61 (by rfl)).trans ((lex_skipped s permutation8 60 61 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation8 60) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation8 60 by rw [image8_eq]; rfl))

theorem lex_8_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3867) (Sat.Literal.pos 3866) (Sat.Literal.pos 60) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation8 60 (assignment s)
    (Sat.Literal.pos 3867) (Sat.Literal.pos 3866) (Sat.Literal.pos 60) (Sat.Literal.pos 240) (positive_of_descriptor s 3867 (.lex permutation8 60) (by rfl)) (lex_8_60_prefix s) (positive_select s 60) (lex_8_60_image s)

theorem lex_8_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.pos 60), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation8 60 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3866) (Sat.Literal.pos 60) (Sat.Literal.pos 240) (lex_8_60_prefix s) (positive_select s 60) (lex_8_60_image s)

theorem lex_8_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.pos 3866)] :=
  (lex_8_60_gate s).prop _ (List.Mem.head _)

theorem lex_8_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.neg 60), (Sat.Literal.pos 240)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.pos 60), (Sat.Literal.neg 240)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.neg 60), (Sat.Literal.neg 240), (Sat.Literal.pos 3867)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3866), (Sat.Literal.pos 60), (Sat.Literal.pos 240), (Sat.Literal.pos 3867)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3867) = lexBefore s permutation8 59 := by
  exact (positive_lex_of_descriptor s 3867 permutation8 60 (by rfl)).trans ((lex_skipped s permutation8 59 60 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation8 59) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation8 59 by rw [image8_eq]; rfl))

theorem lex_8_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3868) (Sat.Literal.pos 3867) (Sat.Literal.pos 59) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation8 59 (assignment s)
    (Sat.Literal.pos 3868) (Sat.Literal.pos 3867) (Sat.Literal.pos 59) (Sat.Literal.pos 236) (positive_of_descriptor s 3868 (.lex permutation8 59) (by rfl)) (lex_8_59_prefix s) (positive_select s 59) (lex_8_59_image s)

theorem lex_8_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.pos 59), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation8 59 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3867) (Sat.Literal.pos 59) (Sat.Literal.pos 236) (lex_8_59_prefix s) (positive_select s 59) (lex_8_59_image s)

theorem lex_8_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.pos 3867)] :=
  (lex_8_59_gate s).prop _ (List.Mem.head _)

theorem lex_8_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.neg 59), (Sat.Literal.pos 236)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.pos 59), (Sat.Literal.neg 236)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.neg 59), (Sat.Literal.neg 236), (Sat.Literal.pos 3868)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3867), (Sat.Literal.pos 59), (Sat.Literal.pos 236), (Sat.Literal.pos 3868)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3868) = lexBefore s permutation8 58 := by
  exact (positive_lex_of_descriptor s 3868 permutation8 59 (by rfl)).trans ((lex_skipped s permutation8 58 59 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation8 58) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation8 58 by rw [image8_eq]; rfl))

theorem lex_8_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3869) (Sat.Literal.pos 3868) (Sat.Literal.pos 58) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation8 58 (assignment s)
    (Sat.Literal.pos 3869) (Sat.Literal.pos 3868) (Sat.Literal.pos 58) (Sat.Literal.pos 232) (positive_of_descriptor s 3869 (.lex permutation8 58) (by rfl)) (lex_8_58_prefix s) (positive_select s 58) (lex_8_58_image s)

theorem lex_8_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.pos 58), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation8 58 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3868) (Sat.Literal.pos 58) (Sat.Literal.pos 232) (lex_8_58_prefix s) (positive_select s 58) (lex_8_58_image s)

theorem lex_8_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.pos 3868)] :=
  (lex_8_58_gate s).prop _ (List.Mem.head _)

theorem lex_8_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.neg 58), (Sat.Literal.pos 232)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.pos 58), (Sat.Literal.neg 232)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.neg 58), (Sat.Literal.neg 232), (Sat.Literal.pos 3869)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3868), (Sat.Literal.pos 58), (Sat.Literal.pos 232), (Sat.Literal.pos 3869)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3869) = lexBefore s permutation8 57 := by
  exact (positive_lex_of_descriptor s 3869 permutation8 58 (by rfl)).trans ((lex_skipped s permutation8 57 58 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation8 57) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation8 57 by rw [image8_eq]; rfl))

theorem lex_8_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3870) (Sat.Literal.pos 3869) (Sat.Literal.pos 57) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation8 57 (assignment s)
    (Sat.Literal.pos 3870) (Sat.Literal.pos 3869) (Sat.Literal.pos 57) (Sat.Literal.pos 228) (positive_of_descriptor s 3870 (.lex permutation8 57) (by rfl)) (lex_8_57_prefix s) (positive_select s 57) (lex_8_57_image s)

theorem lex_8_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.pos 57), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation8 57 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3869) (Sat.Literal.pos 57) (Sat.Literal.pos 228) (lex_8_57_prefix s) (positive_select s 57) (lex_8_57_image s)

theorem lex_8_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.pos 3869)] :=
  (lex_8_57_gate s).prop _ (List.Mem.head _)

theorem lex_8_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.neg 57), (Sat.Literal.pos 228)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.pos 57), (Sat.Literal.neg 228)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.neg 57), (Sat.Literal.neg 228), (Sat.Literal.pos 3870)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3869), (Sat.Literal.pos 57), (Sat.Literal.pos 228), (Sat.Literal.pos 3870)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3870) = lexBefore s permutation8 56 := by
  exact (positive_lex_of_descriptor s 3870 permutation8 57 (by rfl)).trans ((lex_skipped s permutation8 56 57 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation8 56) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation8 56 by rw [image8_eq]; rfl))

theorem lex_8_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3871) (Sat.Literal.pos 3870) (Sat.Literal.pos 56) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation8 56 (assignment s)
    (Sat.Literal.pos 3871) (Sat.Literal.pos 3870) (Sat.Literal.pos 56) (Sat.Literal.pos 224) (positive_of_descriptor s 3871 (.lex permutation8 56) (by rfl)) (lex_8_56_prefix s) (positive_select s 56) (lex_8_56_image s)

theorem lex_8_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.pos 56), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation8 56 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3870) (Sat.Literal.pos 56) (Sat.Literal.pos 224) (lex_8_56_prefix s) (positive_select s 56) (lex_8_56_image s)

theorem lex_8_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.pos 3870)] :=
  (lex_8_56_gate s).prop _ (List.Mem.head _)

theorem lex_8_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.neg 56), (Sat.Literal.pos 224)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.pos 56), (Sat.Literal.neg 224)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.neg 56), (Sat.Literal.neg 224), (Sat.Literal.pos 3871)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3870), (Sat.Literal.pos 56), (Sat.Literal.pos 224), (Sat.Literal.pos 3871)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3871) = lexBefore s permutation8 55 := by
  exact (positive_lex_of_descriptor s 3871 permutation8 56 (by rfl)).trans ((lex_skipped s permutation8 55 56 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation8 55) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation8 55 by rw [image8_eq]; rfl))

theorem lex_8_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3872) (Sat.Literal.pos 3871) (Sat.Literal.pos 55) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation8 55 (assignment s)
    (Sat.Literal.pos 3872) (Sat.Literal.pos 3871) (Sat.Literal.pos 55) (Sat.Literal.pos 220) (positive_of_descriptor s 3872 (.lex permutation8 55) (by rfl)) (lex_8_55_prefix s) (positive_select s 55) (lex_8_55_image s)

theorem lex_8_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.pos 55), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation8 55 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3871) (Sat.Literal.pos 55) (Sat.Literal.pos 220) (lex_8_55_prefix s) (positive_select s 55) (lex_8_55_image s)

theorem lex_8_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.pos 3871)] :=
  (lex_8_55_gate s).prop _ (List.Mem.head _)

theorem lex_8_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.neg 55), (Sat.Literal.pos 220)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.pos 55), (Sat.Literal.neg 220)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.neg 55), (Sat.Literal.neg 220), (Sat.Literal.pos 3872)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3871), (Sat.Literal.pos 55), (Sat.Literal.pos 220), (Sat.Literal.pos 3872)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3872) = lexBefore s permutation8 54 := by
  exact (positive_lex_of_descriptor s 3872 permutation8 55 (by rfl)).trans ((lex_skipped s permutation8 54 55 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation8 54) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation8 54 by rw [image8_eq]; rfl))

theorem lex_8_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3873) (Sat.Literal.pos 3872) (Sat.Literal.pos 54) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation8 54 (assignment s)
    (Sat.Literal.pos 3873) (Sat.Literal.pos 3872) (Sat.Literal.pos 54) (Sat.Literal.pos 216) (positive_of_descriptor s 3873 (.lex permutation8 54) (by rfl)) (lex_8_54_prefix s) (positive_select s 54) (lex_8_54_image s)

theorem lex_8_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.pos 54), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation8 54 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3872) (Sat.Literal.pos 54) (Sat.Literal.pos 216) (lex_8_54_prefix s) (positive_select s 54) (lex_8_54_image s)

theorem lex_8_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.pos 3872)] :=
  (lex_8_54_gate s).prop _ (List.Mem.head _)

theorem lex_8_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.neg 54), (Sat.Literal.pos 216)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.pos 54), (Sat.Literal.neg 216)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.neg 54), (Sat.Literal.neg 216), (Sat.Literal.pos 3873)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3872), (Sat.Literal.pos 54), (Sat.Literal.pos 216), (Sat.Literal.pos 3873)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3873) = lexBefore s permutation8 53 := by
  exact (positive_lex_of_descriptor s 3873 permutation8 54 (by rfl)).trans ((lex_skipped s permutation8 53 54 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation8 53) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation8 53 by rw [image8_eq]; rfl))

theorem lex_8_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3874) (Sat.Literal.pos 3873) (Sat.Literal.pos 53) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation8 53 (assignment s)
    (Sat.Literal.pos 3874) (Sat.Literal.pos 3873) (Sat.Literal.pos 53) (Sat.Literal.pos 212) (positive_of_descriptor s 3874 (.lex permutation8 53) (by rfl)) (lex_8_53_prefix s) (positive_select s 53) (lex_8_53_image s)

theorem lex_8_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.pos 53), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation8 53 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3873) (Sat.Literal.pos 53) (Sat.Literal.pos 212) (lex_8_53_prefix s) (positive_select s 53) (lex_8_53_image s)

theorem lex_8_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.pos 3873)] :=
  (lex_8_53_gate s).prop _ (List.Mem.head _)

theorem lex_8_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.neg 53), (Sat.Literal.pos 212)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.pos 53), (Sat.Literal.neg 212)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.neg 53), (Sat.Literal.neg 212), (Sat.Literal.pos 3874)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3873), (Sat.Literal.pos 53), (Sat.Literal.pos 212), (Sat.Literal.pos 3874)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3874) = lexBefore s permutation8 52 := by
  exact (positive_lex_of_descriptor s 3874 permutation8 53 (by rfl)).trans ((lex_skipped s permutation8 52 53 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation8 52) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation8 52 by rw [image8_eq]; rfl))

theorem lex_8_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3875) (Sat.Literal.pos 3874) (Sat.Literal.pos 52) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation8 52 (assignment s)
    (Sat.Literal.pos 3875) (Sat.Literal.pos 3874) (Sat.Literal.pos 52) (Sat.Literal.pos 208) (positive_of_descriptor s 3875 (.lex permutation8 52) (by rfl)) (lex_8_52_prefix s) (positive_select s 52) (lex_8_52_image s)

theorem lex_8_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.pos 52), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation8 52 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3874) (Sat.Literal.pos 52) (Sat.Literal.pos 208) (lex_8_52_prefix s) (positive_select s 52) (lex_8_52_image s)

theorem lex_8_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.pos 3874)] :=
  (lex_8_52_gate s).prop _ (List.Mem.head _)

theorem lex_8_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.neg 52), (Sat.Literal.pos 208)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.pos 52), (Sat.Literal.neg 208)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.neg 52), (Sat.Literal.neg 208), (Sat.Literal.pos 3875)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3874), (Sat.Literal.pos 52), (Sat.Literal.pos 208), (Sat.Literal.pos 3875)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3875) = lexBefore s permutation8 51 := by
  exact (positive_lex_of_descriptor s 3875 permutation8 52 (by rfl)).trans ((lex_skipped s permutation8 51 52 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation8 51) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation8 51 by rw [image8_eq]; rfl))

theorem lex_8_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3876) (Sat.Literal.pos 3875) (Sat.Literal.pos 51) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation8 51 (assignment s)
    (Sat.Literal.pos 3876) (Sat.Literal.pos 3875) (Sat.Literal.pos 51) (Sat.Literal.pos 204) (positive_of_descriptor s 3876 (.lex permutation8 51) (by rfl)) (lex_8_51_prefix s) (positive_select s 51) (lex_8_51_image s)

theorem lex_8_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.pos 51), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation8 51 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3875) (Sat.Literal.pos 51) (Sat.Literal.pos 204) (lex_8_51_prefix s) (positive_select s 51) (lex_8_51_image s)

theorem lex_8_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.pos 3875)] :=
  (lex_8_51_gate s).prop _ (List.Mem.head _)

theorem lex_8_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.neg 51), (Sat.Literal.pos 204)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.pos 51), (Sat.Literal.neg 204)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.neg 51), (Sat.Literal.neg 204), (Sat.Literal.pos 3876)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3875), (Sat.Literal.pos 51), (Sat.Literal.pos 204), (Sat.Literal.pos 3876)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3876) = lexBefore s permutation8 50 := by
  exact (positive_lex_of_descriptor s 3876 permutation8 51 (by rfl)).trans ((lex_skipped s permutation8 50 51 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation8 50) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation8 50 by rw [image8_eq]; rfl))

theorem lex_8_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3877) (Sat.Literal.pos 3876) (Sat.Literal.pos 50) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation8 50 (assignment s)
    (Sat.Literal.pos 3877) (Sat.Literal.pos 3876) (Sat.Literal.pos 50) (Sat.Literal.pos 200) (positive_of_descriptor s 3877 (.lex permutation8 50) (by rfl)) (lex_8_50_prefix s) (positive_select s 50) (lex_8_50_image s)

theorem lex_8_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.pos 50), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation8 50 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3876) (Sat.Literal.pos 50) (Sat.Literal.pos 200) (lex_8_50_prefix s) (positive_select s 50) (lex_8_50_image s)

theorem lex_8_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.pos 3876)] :=
  (lex_8_50_gate s).prop _ (List.Mem.head _)

theorem lex_8_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.neg 50), (Sat.Literal.pos 200)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.pos 50), (Sat.Literal.neg 200)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.neg 50), (Sat.Literal.neg 200), (Sat.Literal.pos 3877)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3876), (Sat.Literal.pos 50), (Sat.Literal.pos 200), (Sat.Literal.pos 3877)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3877) = lexBefore s permutation8 49 := by
  exact (positive_lex_of_descriptor s 3877 permutation8 50 (by rfl)).trans ((lex_skipped s permutation8 49 50 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation8 49) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation8 49 by rw [image8_eq]; rfl))

theorem lex_8_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3878) (Sat.Literal.pos 3877) (Sat.Literal.pos 49) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation8 49 (assignment s)
    (Sat.Literal.pos 3878) (Sat.Literal.pos 3877) (Sat.Literal.pos 49) (Sat.Literal.pos 196) (positive_of_descriptor s 3878 (.lex permutation8 49) (by rfl)) (lex_8_49_prefix s) (positive_select s 49) (lex_8_49_image s)

theorem lex_8_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.pos 49), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation8 49 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3877) (Sat.Literal.pos 49) (Sat.Literal.pos 196) (lex_8_49_prefix s) (positive_select s 49) (lex_8_49_image s)

theorem lex_8_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.pos 3877)] :=
  (lex_8_49_gate s).prop _ (List.Mem.head _)

theorem lex_8_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.neg 49), (Sat.Literal.pos 196)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.pos 49), (Sat.Literal.neg 196)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.neg 49), (Sat.Literal.neg 196), (Sat.Literal.pos 3878)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3877), (Sat.Literal.pos 49), (Sat.Literal.pos 196), (Sat.Literal.pos 3878)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3878) = lexBefore s permutation8 48 := by
  exact (positive_lex_of_descriptor s 3878 permutation8 49 (by rfl)).trans ((lex_skipped s permutation8 48 49 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation8 48) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation8 48 by rw [image8_eq]; rfl))

theorem lex_8_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3879) (Sat.Literal.pos 3878) (Sat.Literal.pos 48) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation8 48 (assignment s)
    (Sat.Literal.pos 3879) (Sat.Literal.pos 3878) (Sat.Literal.pos 48) (Sat.Literal.pos 192) (positive_of_descriptor s 3879 (.lex permutation8 48) (by rfl)) (lex_8_48_prefix s) (positive_select s 48) (lex_8_48_image s)

theorem lex_8_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.pos 48), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation8 48 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3878) (Sat.Literal.pos 48) (Sat.Literal.pos 192) (lex_8_48_prefix s) (positive_select s 48) (lex_8_48_image s)

theorem lex_8_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.pos 3878)] :=
  (lex_8_48_gate s).prop _ (List.Mem.head _)

theorem lex_8_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.neg 48), (Sat.Literal.pos 192)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.pos 48), (Sat.Literal.neg 192)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.neg 48), (Sat.Literal.neg 192), (Sat.Literal.pos 3879)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3878), (Sat.Literal.pos 48), (Sat.Literal.pos 192), (Sat.Literal.pos 3879)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3879) = lexBefore s permutation8 47 := by
  exact (positive_lex_of_descriptor s 3879 permutation8 48 (by rfl)).trans ((lex_skipped s permutation8 47 48 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation8 47) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation8 47 by rw [image8_eq]; rfl))

theorem lex_8_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3880) (Sat.Literal.pos 3879) (Sat.Literal.pos 47) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation8 47 (assignment s)
    (Sat.Literal.pos 3880) (Sat.Literal.pos 3879) (Sat.Literal.pos 47) (Sat.Literal.pos 188) (positive_of_descriptor s 3880 (.lex permutation8 47) (by rfl)) (lex_8_47_prefix s) (positive_select s 47) (lex_8_47_image s)

theorem lex_8_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.pos 47), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation8 47 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3879) (Sat.Literal.pos 47) (Sat.Literal.pos 188) (lex_8_47_prefix s) (positive_select s 47) (lex_8_47_image s)

theorem lex_8_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.pos 3879)] :=
  (lex_8_47_gate s).prop _ (List.Mem.head _)

theorem lex_8_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.neg 47), (Sat.Literal.pos 188)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.pos 47), (Sat.Literal.neg 188)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.neg 47), (Sat.Literal.neg 188), (Sat.Literal.pos 3880)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3879), (Sat.Literal.pos 47), (Sat.Literal.pos 188), (Sat.Literal.pos 3880)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3880) = lexBefore s permutation8 46 := by
  exact (positive_lex_of_descriptor s 3880 permutation8 47 (by rfl)).trans ((lex_skipped s permutation8 46 47 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation8 46) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation8 46 by rw [image8_eq]; rfl))

theorem lex_8_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3881) (Sat.Literal.pos 3880) (Sat.Literal.pos 46) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation8 46 (assignment s)
    (Sat.Literal.pos 3881) (Sat.Literal.pos 3880) (Sat.Literal.pos 46) (Sat.Literal.pos 184) (positive_of_descriptor s 3881 (.lex permutation8 46) (by rfl)) (lex_8_46_prefix s) (positive_select s 46) (lex_8_46_image s)

theorem lex_8_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.pos 46), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation8 46 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3880) (Sat.Literal.pos 46) (Sat.Literal.pos 184) (lex_8_46_prefix s) (positive_select s 46) (lex_8_46_image s)

theorem lex_8_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.pos 3880)] :=
  (lex_8_46_gate s).prop _ (List.Mem.head _)

theorem lex_8_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.neg 46), (Sat.Literal.pos 184)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.pos 46), (Sat.Literal.neg 184)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.neg 46), (Sat.Literal.neg 184), (Sat.Literal.pos 3881)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3880), (Sat.Literal.pos 46), (Sat.Literal.pos 184), (Sat.Literal.pos 3881)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3881) = lexBefore s permutation8 45 := by
  exact (positive_lex_of_descriptor s 3881 permutation8 46 (by rfl)).trans ((lex_skipped s permutation8 45 46 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation8 45) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation8 45 by rw [image8_eq]; rfl))

theorem lex_8_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3882) (Sat.Literal.pos 3881) (Sat.Literal.pos 45) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation8 45 (assignment s)
    (Sat.Literal.pos 3882) (Sat.Literal.pos 3881) (Sat.Literal.pos 45) (Sat.Literal.pos 180) (positive_of_descriptor s 3882 (.lex permutation8 45) (by rfl)) (lex_8_45_prefix s) (positive_select s 45) (lex_8_45_image s)

theorem lex_8_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.pos 45), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation8 45 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3881) (Sat.Literal.pos 45) (Sat.Literal.pos 180) (lex_8_45_prefix s) (positive_select s 45) (lex_8_45_image s)

theorem lex_8_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.pos 3881)] :=
  (lex_8_45_gate s).prop _ (List.Mem.head _)

theorem lex_8_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.neg 45), (Sat.Literal.pos 180)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.pos 45), (Sat.Literal.neg 180)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.neg 45), (Sat.Literal.neg 180), (Sat.Literal.pos 3882)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3881), (Sat.Literal.pos 45), (Sat.Literal.pos 180), (Sat.Literal.pos 3882)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3882) = lexBefore s permutation8 44 := by
  exact (positive_lex_of_descriptor s 3882 permutation8 45 (by rfl)).trans ((lex_skipped s permutation8 44 45 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation8 44) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation8 44 by rw [image8_eq]; rfl))

theorem lex_8_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3883) (Sat.Literal.pos 3882) (Sat.Literal.pos 44) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation8 44 (assignment s)
    (Sat.Literal.pos 3883) (Sat.Literal.pos 3882) (Sat.Literal.pos 44) (Sat.Literal.pos 176) (positive_of_descriptor s 3883 (.lex permutation8 44) (by rfl)) (lex_8_44_prefix s) (positive_select s 44) (lex_8_44_image s)

theorem lex_8_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.pos 44), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation8 44 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3882) (Sat.Literal.pos 44) (Sat.Literal.pos 176) (lex_8_44_prefix s) (positive_select s 44) (lex_8_44_image s)

theorem lex_8_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.pos 3882)] :=
  (lex_8_44_gate s).prop _ (List.Mem.head _)

theorem lex_8_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.neg 44), (Sat.Literal.pos 176)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.pos 44), (Sat.Literal.neg 176)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.neg 44), (Sat.Literal.neg 176), (Sat.Literal.pos 3883)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3882), (Sat.Literal.pos 44), (Sat.Literal.pos 176), (Sat.Literal.pos 3883)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3883) = lexBefore s permutation8 43 := by
  exact (positive_lex_of_descriptor s 3883 permutation8 44 (by rfl)).trans ((lex_skipped s permutation8 43 44 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation8 43) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation8 43 by rw [image8_eq]; rfl))

theorem lex_8_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3884) (Sat.Literal.pos 3883) (Sat.Literal.pos 43) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation8 43 (assignment s)
    (Sat.Literal.pos 3884) (Sat.Literal.pos 3883) (Sat.Literal.pos 43) (Sat.Literal.pos 172) (positive_of_descriptor s 3884 (.lex permutation8 43) (by rfl)) (lex_8_43_prefix s) (positive_select s 43) (lex_8_43_image s)

theorem lex_8_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.pos 43), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation8 43 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3883) (Sat.Literal.pos 43) (Sat.Literal.pos 172) (lex_8_43_prefix s) (positive_select s 43) (lex_8_43_image s)

theorem lex_8_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.pos 3883)] :=
  (lex_8_43_gate s).prop _ (List.Mem.head _)

theorem lex_8_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.neg 43), (Sat.Literal.pos 172)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.pos 43), (Sat.Literal.neg 172)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.neg 43), (Sat.Literal.neg 172), (Sat.Literal.pos 3884)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3883), (Sat.Literal.pos 43), (Sat.Literal.pos 172), (Sat.Literal.pos 3884)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3884) = lexBefore s permutation8 42 := by
  exact (positive_lex_of_descriptor s 3884 permutation8 43 (by rfl)).trans ((lex_skipped s permutation8 42 43 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation8 42) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation8 42 by rw [image8_eq]; rfl))

theorem lex_8_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3885) (Sat.Literal.pos 3884) (Sat.Literal.pos 42) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation8 42 (assignment s)
    (Sat.Literal.pos 3885) (Sat.Literal.pos 3884) (Sat.Literal.pos 42) (Sat.Literal.pos 168) (positive_of_descriptor s 3885 (.lex permutation8 42) (by rfl)) (lex_8_42_prefix s) (positive_select s 42) (lex_8_42_image s)

theorem lex_8_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.pos 42), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation8 42 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3884) (Sat.Literal.pos 42) (Sat.Literal.pos 168) (lex_8_42_prefix s) (positive_select s 42) (lex_8_42_image s)

theorem lex_8_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.pos 3884)] :=
  (lex_8_42_gate s).prop _ (List.Mem.head _)

theorem lex_8_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.neg 42), (Sat.Literal.pos 168)] :=
  (lex_8_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.pos 42), (Sat.Literal.neg 168)] :=
  (lex_8_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.neg 42), (Sat.Literal.neg 168), (Sat.Literal.pos 3885)] :=
  (lex_8_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3884), (Sat.Literal.pos 42), (Sat.Literal.pos 168), (Sat.Literal.pos 3885)] :=
  (lex_8_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3885) = lexBefore s permutation8 41 := by
  exact (positive_lex_of_descriptor s 3885 permutation8 42 (by rfl)).trans ((lex_skipped s permutation8 41 42 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation8 41) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation8 41 by rw [image8_eq]; rfl))

theorem lex_8_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3886) (Sat.Literal.pos 3885) (Sat.Literal.pos 41) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation8 41 (assignment s)
    (Sat.Literal.pos 3886) (Sat.Literal.pos 3885) (Sat.Literal.pos 41) (Sat.Literal.pos 164) (positive_of_descriptor s 3886 (.lex permutation8 41) (by rfl)) (lex_8_41_prefix s) (positive_select s 41) (lex_8_41_image s)

theorem lex_8_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.pos 41), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation8 41 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3885) (Sat.Literal.pos 41) (Sat.Literal.pos 164) (lex_8_41_prefix s) (positive_select s 41) (lex_8_41_image s)

theorem lex_8_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.pos 3885)] :=
  (lex_8_41_gate s).prop _ (List.Mem.head _)

theorem lex_8_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.neg 41), (Sat.Literal.pos 164)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.pos 41), (Sat.Literal.neg 164)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.neg 41), (Sat.Literal.neg 164), (Sat.Literal.pos 3886)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3885), (Sat.Literal.pos 41), (Sat.Literal.pos 164), (Sat.Literal.pos 3886)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3886) = lexBefore s permutation8 40 := by
  exact (positive_lex_of_descriptor s 3886 permutation8 41 (by rfl)).trans ((lex_skipped s permutation8 40 41 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation8 40) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation8 40 by rw [image8_eq]; rfl))

theorem lex_8_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3887) (Sat.Literal.pos 3886) (Sat.Literal.pos 40) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation8 40 (assignment s)
    (Sat.Literal.pos 3887) (Sat.Literal.pos 3886) (Sat.Literal.pos 40) (Sat.Literal.pos 160) (positive_of_descriptor s 3887 (.lex permutation8 40) (by rfl)) (lex_8_40_prefix s) (positive_select s 40) (lex_8_40_image s)

theorem lex_8_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.pos 40), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation8 40 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3886) (Sat.Literal.pos 40) (Sat.Literal.pos 160) (lex_8_40_prefix s) (positive_select s 40) (lex_8_40_image s)

theorem lex_8_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.pos 3886)] :=
  (lex_8_40_gate s).prop _ (List.Mem.head _)

theorem lex_8_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.neg 40), (Sat.Literal.pos 160)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.pos 40), (Sat.Literal.neg 160)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.neg 40), (Sat.Literal.neg 160), (Sat.Literal.pos 3887)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3886), (Sat.Literal.pos 40), (Sat.Literal.pos 160), (Sat.Literal.pos 3887)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3887) = lexBefore s permutation8 39 := by
  exact (positive_lex_of_descriptor s 3887 permutation8 40 (by rfl)).trans ((lex_skipped s permutation8 39 40 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation8 39) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation8 39 by rw [image8_eq]; rfl))

theorem lex_8_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3888) (Sat.Literal.pos 3887) (Sat.Literal.pos 39) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation8 39 (assignment s)
    (Sat.Literal.pos 3888) (Sat.Literal.pos 3887) (Sat.Literal.pos 39) (Sat.Literal.pos 156) (positive_of_descriptor s 3888 (.lex permutation8 39) (by rfl)) (lex_8_39_prefix s) (positive_select s 39) (lex_8_39_image s)

theorem lex_8_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.pos 39), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation8 39 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3887) (Sat.Literal.pos 39) (Sat.Literal.pos 156) (lex_8_39_prefix s) (positive_select s 39) (lex_8_39_image s)

theorem lex_8_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.pos 3887)] :=
  (lex_8_39_gate s).prop _ (List.Mem.head _)

theorem lex_8_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.neg 39), (Sat.Literal.pos 156)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.pos 39), (Sat.Literal.neg 156)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.neg 39), (Sat.Literal.neg 156), (Sat.Literal.pos 3888)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3887), (Sat.Literal.pos 39), (Sat.Literal.pos 156), (Sat.Literal.pos 3888)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3888) = lexBefore s permutation8 38 := by
  exact (positive_lex_of_descriptor s 3888 permutation8 39 (by rfl)).trans ((lex_skipped s permutation8 38 39 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation8 38) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation8 38 by rw [image8_eq]; rfl))

theorem lex_8_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3889) (Sat.Literal.pos 3888) (Sat.Literal.pos 38) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation8 38 (assignment s)
    (Sat.Literal.pos 3889) (Sat.Literal.pos 3888) (Sat.Literal.pos 38) (Sat.Literal.pos 152) (positive_of_descriptor s 3889 (.lex permutation8 38) (by rfl)) (lex_8_38_prefix s) (positive_select s 38) (lex_8_38_image s)

theorem lex_8_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.pos 38), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation8 38 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3888) (Sat.Literal.pos 38) (Sat.Literal.pos 152) (lex_8_38_prefix s) (positive_select s 38) (lex_8_38_image s)

theorem lex_8_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.pos 3888)] :=
  (lex_8_38_gate s).prop _ (List.Mem.head _)

theorem lex_8_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.neg 38), (Sat.Literal.pos 152)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.pos 38), (Sat.Literal.neg 152)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.neg 38), (Sat.Literal.neg 152), (Sat.Literal.pos 3889)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3888), (Sat.Literal.pos 38), (Sat.Literal.pos 152), (Sat.Literal.pos 3889)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3889) = lexBefore s permutation8 37 := by
  exact (positive_lex_of_descriptor s 3889 permutation8 38 (by rfl)).trans ((lex_skipped s permutation8 37 38 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation8 37) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation8 37 by rw [image8_eq]; rfl))

theorem lex_8_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3890) (Sat.Literal.pos 3889) (Sat.Literal.pos 37) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation8 37 (assignment s)
    (Sat.Literal.pos 3890) (Sat.Literal.pos 3889) (Sat.Literal.pos 37) (Sat.Literal.pos 148) (positive_of_descriptor s 3890 (.lex permutation8 37) (by rfl)) (lex_8_37_prefix s) (positive_select s 37) (lex_8_37_image s)

theorem lex_8_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.pos 37), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation8 37 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3889) (Sat.Literal.pos 37) (Sat.Literal.pos 148) (lex_8_37_prefix s) (positive_select s 37) (lex_8_37_image s)

theorem lex_8_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.pos 3889)] :=
  (lex_8_37_gate s).prop _ (List.Mem.head _)

theorem lex_8_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.neg 37), (Sat.Literal.pos 148)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.pos 37), (Sat.Literal.neg 148)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.neg 37), (Sat.Literal.neg 148), (Sat.Literal.pos 3890)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3889), (Sat.Literal.pos 37), (Sat.Literal.pos 148), (Sat.Literal.pos 3890)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3890) = lexBefore s permutation8 36 := by
  exact (positive_lex_of_descriptor s 3890 permutation8 37 (by rfl)).trans ((lex_skipped s permutation8 36 37 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation8 36) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation8 36 by rw [image8_eq]; rfl))

theorem lex_8_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3891) (Sat.Literal.pos 3890) (Sat.Literal.pos 36) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation8 36 (assignment s)
    (Sat.Literal.pos 3891) (Sat.Literal.pos 3890) (Sat.Literal.pos 36) (Sat.Literal.pos 144) (positive_of_descriptor s 3891 (.lex permutation8 36) (by rfl)) (lex_8_36_prefix s) (positive_select s 36) (lex_8_36_image s)

theorem lex_8_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.pos 36), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation8 36 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3890) (Sat.Literal.pos 36) (Sat.Literal.pos 144) (lex_8_36_prefix s) (positive_select s 36) (lex_8_36_image s)

theorem lex_8_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.pos 3890)] :=
  (lex_8_36_gate s).prop _ (List.Mem.head _)

theorem lex_8_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.neg 36), (Sat.Literal.pos 144)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.pos 36), (Sat.Literal.neg 144)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.neg 36), (Sat.Literal.neg 144), (Sat.Literal.pos 3891)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3890), (Sat.Literal.pos 36), (Sat.Literal.pos 144), (Sat.Literal.pos 3891)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3891) = lexBefore s permutation8 35 := by
  exact (positive_lex_of_descriptor s 3891 permutation8 36 (by rfl)).trans ((lex_skipped s permutation8 35 36 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation8 35) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation8 35 by rw [image8_eq]; rfl))

theorem lex_8_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3892) (Sat.Literal.pos 3891) (Sat.Literal.pos 35) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation8 35 (assignment s)
    (Sat.Literal.pos 3892) (Sat.Literal.pos 3891) (Sat.Literal.pos 35) (Sat.Literal.pos 140) (positive_of_descriptor s 3892 (.lex permutation8 35) (by rfl)) (lex_8_35_prefix s) (positive_select s 35) (lex_8_35_image s)

theorem lex_8_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.pos 35), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation8 35 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3891) (Sat.Literal.pos 35) (Sat.Literal.pos 140) (lex_8_35_prefix s) (positive_select s 35) (lex_8_35_image s)

theorem lex_8_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.pos 3891)] :=
  (lex_8_35_gate s).prop _ (List.Mem.head _)

theorem lex_8_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.neg 35), (Sat.Literal.pos 140)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.pos 35), (Sat.Literal.neg 140)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.neg 35), (Sat.Literal.neg 140), (Sat.Literal.pos 3892)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3891), (Sat.Literal.pos 35), (Sat.Literal.pos 140), (Sat.Literal.pos 3892)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3892) = lexBefore s permutation8 34 := by
  exact (positive_lex_of_descriptor s 3892 permutation8 35 (by rfl)).trans ((lex_skipped s permutation8 34 35 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation8 34) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation8 34 by rw [image8_eq]; rfl))

theorem lex_8_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3893) (Sat.Literal.pos 3892) (Sat.Literal.pos 34) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation8 34 (assignment s)
    (Sat.Literal.pos 3893) (Sat.Literal.pos 3892) (Sat.Literal.pos 34) (Sat.Literal.pos 136) (positive_of_descriptor s 3893 (.lex permutation8 34) (by rfl)) (lex_8_34_prefix s) (positive_select s 34) (lex_8_34_image s)

theorem lex_8_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.pos 34), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation8 34 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3892) (Sat.Literal.pos 34) (Sat.Literal.pos 136) (lex_8_34_prefix s) (positive_select s 34) (lex_8_34_image s)

theorem lex_8_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.pos 3892)] :=
  (lex_8_34_gate s).prop _ (List.Mem.head _)

theorem lex_8_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.neg 34), (Sat.Literal.pos 136)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.pos 34), (Sat.Literal.neg 136)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.neg 34), (Sat.Literal.neg 136), (Sat.Literal.pos 3893)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3892), (Sat.Literal.pos 34), (Sat.Literal.pos 136), (Sat.Literal.pos 3893)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3893) = lexBefore s permutation8 33 := by
  exact (positive_lex_of_descriptor s 3893 permutation8 34 (by rfl)).trans ((lex_skipped s permutation8 33 34 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation8 33) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation8 33 by rw [image8_eq]; rfl))

theorem lex_8_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3894) (Sat.Literal.pos 3893) (Sat.Literal.pos 33) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation8 33 (assignment s)
    (Sat.Literal.pos 3894) (Sat.Literal.pos 3893) (Sat.Literal.pos 33) (Sat.Literal.pos 132) (positive_of_descriptor s 3894 (.lex permutation8 33) (by rfl)) (lex_8_33_prefix s) (positive_select s 33) (lex_8_33_image s)

theorem lex_8_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.pos 33), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation8 33 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3893) (Sat.Literal.pos 33) (Sat.Literal.pos 132) (lex_8_33_prefix s) (positive_select s 33) (lex_8_33_image s)

theorem lex_8_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.pos 3893)] :=
  (lex_8_33_gate s).prop _ (List.Mem.head _)

theorem lex_8_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.neg 33), (Sat.Literal.pos 132)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.pos 33), (Sat.Literal.neg 132)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.neg 33), (Sat.Literal.neg 132), (Sat.Literal.pos 3894)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3893), (Sat.Literal.pos 33), (Sat.Literal.pos 132), (Sat.Literal.pos 3894)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3894) = lexBefore s permutation8 32 := by
  exact (positive_lex_of_descriptor s 3894 permutation8 33 (by rfl)).trans ((lex_skipped s permutation8 32 33 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation8 32) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation8 32 by rw [image8_eq]; rfl))

theorem lex_8_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3895) (Sat.Literal.pos 3894) (Sat.Literal.pos 32) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation8 32 (assignment s)
    (Sat.Literal.pos 3895) (Sat.Literal.pos 3894) (Sat.Literal.pos 32) (Sat.Literal.pos 128) (positive_of_descriptor s 3895 (.lex permutation8 32) (by rfl)) (lex_8_32_prefix s) (positive_select s 32) (lex_8_32_image s)

theorem lex_8_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.pos 32), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation8 32 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3894) (Sat.Literal.pos 32) (Sat.Literal.pos 128) (lex_8_32_prefix s) (positive_select s 32) (lex_8_32_image s)

theorem lex_8_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.pos 3894)] :=
  (lex_8_32_gate s).prop _ (List.Mem.head _)

theorem lex_8_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.neg 32), (Sat.Literal.pos 128)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.pos 32), (Sat.Literal.neg 128)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.neg 32), (Sat.Literal.neg 128), (Sat.Literal.pos 3895)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3894), (Sat.Literal.pos 32), (Sat.Literal.pos 128), (Sat.Literal.pos 3895)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3895) = lexBefore s permutation8 31 := by
  exact (positive_lex_of_descriptor s 3895 permutation8 32 (by rfl)).trans ((lex_skipped s permutation8 31 32 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation8 31) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation8 31 by rw [image8_eq]; rfl))

theorem lex_8_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3896) (Sat.Literal.pos 3895) (Sat.Literal.pos 31) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation8 31 (assignment s)
    (Sat.Literal.pos 3896) (Sat.Literal.pos 3895) (Sat.Literal.pos 31) (Sat.Literal.pos 124) (positive_of_descriptor s 3896 (.lex permutation8 31) (by rfl)) (lex_8_31_prefix s) (positive_select s 31) (lex_8_31_image s)

theorem lex_8_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.pos 31), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation8 31 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3895) (Sat.Literal.pos 31) (Sat.Literal.pos 124) (lex_8_31_prefix s) (positive_select s 31) (lex_8_31_image s)

theorem lex_8_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.pos 3895)] :=
  (lex_8_31_gate s).prop _ (List.Mem.head _)

theorem lex_8_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.neg 31), (Sat.Literal.pos 124)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.pos 31), (Sat.Literal.neg 124)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.neg 31), (Sat.Literal.neg 124), (Sat.Literal.pos 3896)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3895), (Sat.Literal.pos 31), (Sat.Literal.pos 124), (Sat.Literal.pos 3896)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3896) = lexBefore s permutation8 30 := by
  exact (positive_lex_of_descriptor s 3896 permutation8 31 (by rfl)).trans ((lex_skipped s permutation8 30 31 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation8 30) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation8 30 by rw [image8_eq]; rfl))

theorem lex_8_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3897) (Sat.Literal.pos 3896) (Sat.Literal.pos 30) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation8 30 (assignment s)
    (Sat.Literal.pos 3897) (Sat.Literal.pos 3896) (Sat.Literal.pos 30) (Sat.Literal.pos 120) (positive_of_descriptor s 3897 (.lex permutation8 30) (by rfl)) (lex_8_30_prefix s) (positive_select s 30) (lex_8_30_image s)

theorem lex_8_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.pos 30), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation8 30 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3896) (Sat.Literal.pos 30) (Sat.Literal.pos 120) (lex_8_30_prefix s) (positive_select s 30) (lex_8_30_image s)

theorem lex_8_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.pos 3896)] :=
  (lex_8_30_gate s).prop _ (List.Mem.head _)

theorem lex_8_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.neg 30), (Sat.Literal.pos 120)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.pos 30), (Sat.Literal.neg 120)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.neg 30), (Sat.Literal.neg 120), (Sat.Literal.pos 3897)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3896), (Sat.Literal.pos 30), (Sat.Literal.pos 120), (Sat.Literal.pos 3897)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3897) = lexBefore s permutation8 29 := by
  exact (positive_lex_of_descriptor s 3897 permutation8 30 (by rfl)).trans ((lex_skipped s permutation8 29 30 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation8 29) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation8 29 by rw [image8_eq]; rfl))

theorem lex_8_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3898) (Sat.Literal.pos 3897) (Sat.Literal.pos 29) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation8 29 (assignment s)
    (Sat.Literal.pos 3898) (Sat.Literal.pos 3897) (Sat.Literal.pos 29) (Sat.Literal.pos 116) (positive_of_descriptor s 3898 (.lex permutation8 29) (by rfl)) (lex_8_29_prefix s) (positive_select s 29) (lex_8_29_image s)

theorem lex_8_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.pos 29), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation8 29 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3897) (Sat.Literal.pos 29) (Sat.Literal.pos 116) (lex_8_29_prefix s) (positive_select s 29) (lex_8_29_image s)

theorem lex_8_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.pos 3897)] :=
  (lex_8_29_gate s).prop _ (List.Mem.head _)

theorem lex_8_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.neg 29), (Sat.Literal.pos 116)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.pos 29), (Sat.Literal.neg 116)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.neg 29), (Sat.Literal.neg 116), (Sat.Literal.pos 3898)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3897), (Sat.Literal.pos 29), (Sat.Literal.pos 116), (Sat.Literal.pos 3898)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3898) = lexBefore s permutation8 28 := by
  exact (positive_lex_of_descriptor s 3898 permutation8 29 (by rfl)).trans ((lex_skipped s permutation8 28 29 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation8 28) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation8 28 by rw [image8_eq]; rfl))

theorem lex_8_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3899) (Sat.Literal.pos 3898) (Sat.Literal.pos 28) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation8 28 (assignment s)
    (Sat.Literal.pos 3899) (Sat.Literal.pos 3898) (Sat.Literal.pos 28) (Sat.Literal.pos 112) (positive_of_descriptor s 3899 (.lex permutation8 28) (by rfl)) (lex_8_28_prefix s) (positive_select s 28) (lex_8_28_image s)

theorem lex_8_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.pos 28), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation8 28 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3898) (Sat.Literal.pos 28) (Sat.Literal.pos 112) (lex_8_28_prefix s) (positive_select s 28) (lex_8_28_image s)

theorem lex_8_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.pos 3898)] :=
  (lex_8_28_gate s).prop _ (List.Mem.head _)

theorem lex_8_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.neg 28), (Sat.Literal.pos 112)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.pos 28), (Sat.Literal.neg 112)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.neg 28), (Sat.Literal.neg 112), (Sat.Literal.pos 3899)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3898), (Sat.Literal.pos 28), (Sat.Literal.pos 112), (Sat.Literal.pos 3899)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3899) = lexBefore s permutation8 27 := by
  exact (positive_lex_of_descriptor s 3899 permutation8 28 (by rfl)).trans ((lex_skipped s permutation8 27 28 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation8 27) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation8 27 by rw [image8_eq]; rfl))

theorem lex_8_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3900) (Sat.Literal.pos 3899) (Sat.Literal.pos 27) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation8 27 (assignment s)
    (Sat.Literal.pos 3900) (Sat.Literal.pos 3899) (Sat.Literal.pos 27) (Sat.Literal.pos 108) (positive_of_descriptor s 3900 (.lex permutation8 27) (by rfl)) (lex_8_27_prefix s) (positive_select s 27) (lex_8_27_image s)

theorem lex_8_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.pos 27), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation8 27 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3899) (Sat.Literal.pos 27) (Sat.Literal.pos 108) (lex_8_27_prefix s) (positive_select s 27) (lex_8_27_image s)

theorem lex_8_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.pos 3899)] :=
  (lex_8_27_gate s).prop _ (List.Mem.head _)

theorem lex_8_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.neg 27), (Sat.Literal.pos 108)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.pos 27), (Sat.Literal.neg 108)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.neg 27), (Sat.Literal.neg 108), (Sat.Literal.pos 3900)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3899), (Sat.Literal.pos 27), (Sat.Literal.pos 108), (Sat.Literal.pos 3900)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3900) = lexBefore s permutation8 26 := by
  exact (positive_lex_of_descriptor s 3900 permutation8 27 (by rfl)).trans ((lex_skipped s permutation8 26 27 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation8 26) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation8 26 by rw [image8_eq]; rfl))

theorem lex_8_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3901) (Sat.Literal.pos 3900) (Sat.Literal.pos 26) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation8 26 (assignment s)
    (Sat.Literal.pos 3901) (Sat.Literal.pos 3900) (Sat.Literal.pos 26) (Sat.Literal.pos 104) (positive_of_descriptor s 3901 (.lex permutation8 26) (by rfl)) (lex_8_26_prefix s) (positive_select s 26) (lex_8_26_image s)

theorem lex_8_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.pos 26), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation8 26 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3900) (Sat.Literal.pos 26) (Sat.Literal.pos 104) (lex_8_26_prefix s) (positive_select s 26) (lex_8_26_image s)

theorem lex_8_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.pos 3900)] :=
  (lex_8_26_gate s).prop _ (List.Mem.head _)

theorem lex_8_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.neg 26), (Sat.Literal.pos 104)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.pos 26), (Sat.Literal.neg 104)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.neg 26), (Sat.Literal.neg 104), (Sat.Literal.pos 3901)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3900), (Sat.Literal.pos 26), (Sat.Literal.pos 104), (Sat.Literal.pos 3901)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3901) = lexBefore s permutation8 25 := by
  exact (positive_lex_of_descriptor s 3901 permutation8 26 (by rfl)).trans ((lex_skipped s permutation8 25 26 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation8 25) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation8 25 by rw [image8_eq]; rfl))

theorem lex_8_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3902) (Sat.Literal.pos 3901) (Sat.Literal.pos 25) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation8 25 (assignment s)
    (Sat.Literal.pos 3902) (Sat.Literal.pos 3901) (Sat.Literal.pos 25) (Sat.Literal.pos 100) (positive_of_descriptor s 3902 (.lex permutation8 25) (by rfl)) (lex_8_25_prefix s) (positive_select s 25) (lex_8_25_image s)

theorem lex_8_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.pos 25), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation8 25 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3901) (Sat.Literal.pos 25) (Sat.Literal.pos 100) (lex_8_25_prefix s) (positive_select s 25) (lex_8_25_image s)

theorem lex_8_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.pos 3901)] :=
  (lex_8_25_gate s).prop _ (List.Mem.head _)

theorem lex_8_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.neg 25), (Sat.Literal.pos 100)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.pos 25), (Sat.Literal.neg 100)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.neg 25), (Sat.Literal.neg 100), (Sat.Literal.pos 3902)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3901), (Sat.Literal.pos 25), (Sat.Literal.pos 100), (Sat.Literal.pos 3902)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3902) = lexBefore s permutation8 24 := by
  exact (positive_lex_of_descriptor s 3902 permutation8 25 (by rfl)).trans ((lex_skipped s permutation8 24 25 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation8 24) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation8 24 by rw [image8_eq]; rfl))

theorem lex_8_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3903) (Sat.Literal.pos 3902) (Sat.Literal.pos 24) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation8 24 (assignment s)
    (Sat.Literal.pos 3903) (Sat.Literal.pos 3902) (Sat.Literal.pos 24) (Sat.Literal.pos 96) (positive_of_descriptor s 3903 (.lex permutation8 24) (by rfl)) (lex_8_24_prefix s) (positive_select s 24) (lex_8_24_image s)

theorem lex_8_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.pos 24), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation8 24 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3902) (Sat.Literal.pos 24) (Sat.Literal.pos 96) (lex_8_24_prefix s) (positive_select s 24) (lex_8_24_image s)

theorem lex_8_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.pos 3902)] :=
  (lex_8_24_gate s).prop _ (List.Mem.head _)

theorem lex_8_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.neg 24), (Sat.Literal.pos 96)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.pos 24), (Sat.Literal.neg 96)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.neg 24), (Sat.Literal.neg 96), (Sat.Literal.pos 3903)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3902), (Sat.Literal.pos 24), (Sat.Literal.pos 96), (Sat.Literal.pos 3903)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3903) = lexBefore s permutation8 23 := by
  exact (positive_lex_of_descriptor s 3903 permutation8 24 (by rfl)).trans ((lex_skipped s permutation8 23 24 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation8 23) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation8 23 by rw [image8_eq]; rfl))

theorem lex_8_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3904) (Sat.Literal.pos 3903) (Sat.Literal.pos 23) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation8 23 (assignment s)
    (Sat.Literal.pos 3904) (Sat.Literal.pos 3903) (Sat.Literal.pos 23) (Sat.Literal.pos 92) (positive_of_descriptor s 3904 (.lex permutation8 23) (by rfl)) (lex_8_23_prefix s) (positive_select s 23) (lex_8_23_image s)

theorem lex_8_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.pos 23), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation8 23 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3903) (Sat.Literal.pos 23) (Sat.Literal.pos 92) (lex_8_23_prefix s) (positive_select s 23) (lex_8_23_image s)

theorem lex_8_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.pos 3903)] :=
  (lex_8_23_gate s).prop _ (List.Mem.head _)

theorem lex_8_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.neg 23), (Sat.Literal.pos 92)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.pos 23), (Sat.Literal.neg 92)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.neg 23), (Sat.Literal.neg 92), (Sat.Literal.pos 3904)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3903), (Sat.Literal.pos 23), (Sat.Literal.pos 92), (Sat.Literal.pos 3904)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3904) = lexBefore s permutation8 22 := by
  exact (positive_lex_of_descriptor s 3904 permutation8 23 (by rfl)).trans ((lex_skipped s permutation8 22 23 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation8 22) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation8 22 by rw [image8_eq]; rfl))

theorem lex_8_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3905) (Sat.Literal.pos 3904) (Sat.Literal.pos 22) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation8 22 (assignment s)
    (Sat.Literal.pos 3905) (Sat.Literal.pos 3904) (Sat.Literal.pos 22) (Sat.Literal.pos 88) (positive_of_descriptor s 3905 (.lex permutation8 22) (by rfl)) (lex_8_22_prefix s) (positive_select s 22) (lex_8_22_image s)

theorem lex_8_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.pos 22), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation8 22 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3904) (Sat.Literal.pos 22) (Sat.Literal.pos 88) (lex_8_22_prefix s) (positive_select s 22) (lex_8_22_image s)

theorem lex_8_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.pos 3904)] :=
  (lex_8_22_gate s).prop _ (List.Mem.head _)

theorem lex_8_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.neg 22), (Sat.Literal.pos 88)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.pos 22), (Sat.Literal.neg 88)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.neg 22), (Sat.Literal.neg 88), (Sat.Literal.pos 3905)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3904), (Sat.Literal.pos 22), (Sat.Literal.pos 88), (Sat.Literal.pos 3905)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3905) = lexBefore s permutation8 21 := by
  exact (positive_lex_of_descriptor s 3905 permutation8 22 (by rfl)).trans ((lex_skipped s permutation8 21 22 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation8 21) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation8 21 by rw [image8_eq]; rfl))

theorem lex_8_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3906) (Sat.Literal.pos 3905) (Sat.Literal.pos 21) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation8 21 (assignment s)
    (Sat.Literal.pos 3906) (Sat.Literal.pos 3905) (Sat.Literal.pos 21) (Sat.Literal.pos 84) (positive_of_descriptor s 3906 (.lex permutation8 21) (by rfl)) (lex_8_21_prefix s) (positive_select s 21) (lex_8_21_image s)

theorem lex_8_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.pos 21), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation8 21 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3905) (Sat.Literal.pos 21) (Sat.Literal.pos 84) (lex_8_21_prefix s) (positive_select s 21) (lex_8_21_image s)

theorem lex_8_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.pos 3905)] :=
  (lex_8_21_gate s).prop _ (List.Mem.head _)

theorem lex_8_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.neg 21), (Sat.Literal.pos 84)] :=
  (lex_8_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.pos 21), (Sat.Literal.neg 84)] :=
  (lex_8_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.neg 21), (Sat.Literal.neg 84), (Sat.Literal.pos 3906)] :=
  (lex_8_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3905), (Sat.Literal.pos 21), (Sat.Literal.pos 84), (Sat.Literal.pos 3906)] :=
  (lex_8_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3906) = lexBefore s permutation8 20 := by
  exact (positive_lex_of_descriptor s 3906 permutation8 21 (by rfl)).trans ((lex_skipped s permutation8 20 21 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation8 20) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation8 20 by rw [image8_eq]; rfl))

theorem lex_8_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3907) (Sat.Literal.pos 3906) (Sat.Literal.pos 20) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation8 20 (assignment s)
    (Sat.Literal.pos 3907) (Sat.Literal.pos 3906) (Sat.Literal.pos 20) (Sat.Literal.pos 80) (positive_of_descriptor s 3907 (.lex permutation8 20) (by rfl)) (lex_8_20_prefix s) (positive_select s 20) (lex_8_20_image s)

theorem lex_8_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.pos 20), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation8 20 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3906) (Sat.Literal.pos 20) (Sat.Literal.pos 80) (lex_8_20_prefix s) (positive_select s 20) (lex_8_20_image s)

theorem lex_8_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.pos 3906)] :=
  (lex_8_20_gate s).prop _ (List.Mem.head _)

theorem lex_8_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.neg 20), (Sat.Literal.pos 80)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.pos 20), (Sat.Literal.neg 80)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.neg 20), (Sat.Literal.neg 80), (Sat.Literal.pos 3907)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3906), (Sat.Literal.pos 20), (Sat.Literal.pos 80), (Sat.Literal.pos 3907)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3907) = lexBefore s permutation8 19 := by
  exact (positive_lex_of_descriptor s 3907 permutation8 20 (by rfl)).trans ((lex_skipped s permutation8 19 20 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation8 19) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation8 19 by rw [image8_eq]; rfl))

theorem lex_8_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3908) (Sat.Literal.pos 3907) (Sat.Literal.pos 19) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation8 19 (assignment s)
    (Sat.Literal.pos 3908) (Sat.Literal.pos 3907) (Sat.Literal.pos 19) (Sat.Literal.pos 76) (positive_of_descriptor s 3908 (.lex permutation8 19) (by rfl)) (lex_8_19_prefix s) (positive_select s 19) (lex_8_19_image s)

theorem lex_8_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.pos 19), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation8 19 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3907) (Sat.Literal.pos 19) (Sat.Literal.pos 76) (lex_8_19_prefix s) (positive_select s 19) (lex_8_19_image s)

theorem lex_8_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.pos 3907)] :=
  (lex_8_19_gate s).prop _ (List.Mem.head _)

theorem lex_8_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.neg 19), (Sat.Literal.pos 76)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.pos 19), (Sat.Literal.neg 76)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.neg 19), (Sat.Literal.neg 76), (Sat.Literal.pos 3908)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3907), (Sat.Literal.pos 19), (Sat.Literal.pos 76), (Sat.Literal.pos 3908)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3908) = lexBefore s permutation8 18 := by
  exact (positive_lex_of_descriptor s 3908 permutation8 19 (by rfl)).trans ((lex_skipped s permutation8 18 19 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation8 18) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation8 18 by rw [image8_eq]; rfl))

theorem lex_8_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3909) (Sat.Literal.pos 3908) (Sat.Literal.pos 18) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation8 18 (assignment s)
    (Sat.Literal.pos 3909) (Sat.Literal.pos 3908) (Sat.Literal.pos 18) (Sat.Literal.pos 72) (positive_of_descriptor s 3909 (.lex permutation8 18) (by rfl)) (lex_8_18_prefix s) (positive_select s 18) (lex_8_18_image s)

theorem lex_8_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.pos 18), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation8 18 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3908) (Sat.Literal.pos 18) (Sat.Literal.pos 72) (lex_8_18_prefix s) (positive_select s 18) (lex_8_18_image s)

theorem lex_8_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.pos 3908)] :=
  (lex_8_18_gate s).prop _ (List.Mem.head _)

theorem lex_8_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.neg 18), (Sat.Literal.pos 72)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.pos 18), (Sat.Literal.neg 72)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.neg 18), (Sat.Literal.neg 72), (Sat.Literal.pos 3909)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3908), (Sat.Literal.pos 18), (Sat.Literal.pos 72), (Sat.Literal.pos 3909)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3909) = lexBefore s permutation8 17 := by
  exact (positive_lex_of_descriptor s 3909 permutation8 18 (by rfl)).trans ((lex_skipped s permutation8 17 18 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation8 17) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation8 17 by rw [image8_eq]; rfl))

theorem lex_8_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3910) (Sat.Literal.pos 3909) (Sat.Literal.pos 17) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation8 17 (assignment s)
    (Sat.Literal.pos 3910) (Sat.Literal.pos 3909) (Sat.Literal.pos 17) (Sat.Literal.pos 68) (positive_of_descriptor s 3910 (.lex permutation8 17) (by rfl)) (lex_8_17_prefix s) (positive_select s 17) (lex_8_17_image s)

theorem lex_8_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.pos 17), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation8 17 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3909) (Sat.Literal.pos 17) (Sat.Literal.pos 68) (lex_8_17_prefix s) (positive_select s 17) (lex_8_17_image s)

theorem lex_8_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.pos 3909)] :=
  (lex_8_17_gate s).prop _ (List.Mem.head _)

theorem lex_8_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.neg 17), (Sat.Literal.pos 68)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.pos 17), (Sat.Literal.neg 68)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.neg 17), (Sat.Literal.neg 68), (Sat.Literal.pos 3910)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3909), (Sat.Literal.pos 17), (Sat.Literal.pos 68), (Sat.Literal.pos 3910)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3910) = lexBefore s permutation8 16 := by
  exact (positive_lex_of_descriptor s 3910 permutation8 17 (by rfl)).trans ((lex_skipped s permutation8 16 17 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation8 16) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation8 16 by rw [image8_eq]; rfl))

theorem lex_8_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3911) (Sat.Literal.pos 3910) (Sat.Literal.pos 16) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation8 16 (assignment s)
    (Sat.Literal.pos 3911) (Sat.Literal.pos 3910) (Sat.Literal.pos 16) (Sat.Literal.pos 64) (positive_of_descriptor s 3911 (.lex permutation8 16) (by rfl)) (lex_8_16_prefix s) (positive_select s 16) (lex_8_16_image s)

theorem lex_8_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.pos 16), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation8 16 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3910) (Sat.Literal.pos 16) (Sat.Literal.pos 64) (lex_8_16_prefix s) (positive_select s 16) (lex_8_16_image s)

theorem lex_8_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.pos 3910)] :=
  (lex_8_16_gate s).prop _ (List.Mem.head _)

theorem lex_8_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.neg 16), (Sat.Literal.pos 64)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.pos 16), (Sat.Literal.neg 64)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.neg 16), (Sat.Literal.neg 64), (Sat.Literal.pos 3911)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3910), (Sat.Literal.pos 16), (Sat.Literal.pos 64), (Sat.Literal.pos 3911)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3911) = lexBefore s permutation8 15 := by
  exact (positive_lex_of_descriptor s 3911 permutation8 16 (by rfl)).trans ((lex_skipped s permutation8 15 16 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation8 15) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation8 15 by rw [image8_eq]; rfl))

theorem lex_8_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3912) (Sat.Literal.pos 3911) (Sat.Literal.pos 15) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation8 15 (assignment s)
    (Sat.Literal.pos 3912) (Sat.Literal.pos 3911) (Sat.Literal.pos 15) (Sat.Literal.pos 60) (positive_of_descriptor s 3912 (.lex permutation8 15) (by rfl)) (lex_8_15_prefix s) (positive_select s 15) (lex_8_15_image s)

theorem lex_8_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.pos 15), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation8 15 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3911) (Sat.Literal.pos 15) (Sat.Literal.pos 60) (lex_8_15_prefix s) (positive_select s 15) (lex_8_15_image s)

theorem lex_8_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.pos 3911)] :=
  (lex_8_15_gate s).prop _ (List.Mem.head _)

theorem lex_8_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.neg 15), (Sat.Literal.pos 60)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.pos 15), (Sat.Literal.neg 60)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.neg 15), (Sat.Literal.neg 60), (Sat.Literal.pos 3912)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3911), (Sat.Literal.pos 15), (Sat.Literal.pos 60), (Sat.Literal.pos 3912)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3912) = lexBefore s permutation8 14 := by
  exact (positive_lex_of_descriptor s 3912 permutation8 15 (by rfl)).trans ((lex_skipped s permutation8 14 15 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation8 14) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation8 14 by rw [image8_eq]; rfl))

theorem lex_8_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3913) (Sat.Literal.pos 3912) (Sat.Literal.pos 14) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation8 14 (assignment s)
    (Sat.Literal.pos 3913) (Sat.Literal.pos 3912) (Sat.Literal.pos 14) (Sat.Literal.pos 56) (positive_of_descriptor s 3913 (.lex permutation8 14) (by rfl)) (lex_8_14_prefix s) (positive_select s 14) (lex_8_14_image s)

theorem lex_8_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.pos 14), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation8 14 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3912) (Sat.Literal.pos 14) (Sat.Literal.pos 56) (lex_8_14_prefix s) (positive_select s 14) (lex_8_14_image s)

theorem lex_8_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.pos 3912)] :=
  (lex_8_14_gate s).prop _ (List.Mem.head _)

theorem lex_8_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.neg 14), (Sat.Literal.pos 56)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.pos 14), (Sat.Literal.neg 56)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.neg 14), (Sat.Literal.neg 56), (Sat.Literal.pos 3913)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3912), (Sat.Literal.pos 14), (Sat.Literal.pos 56), (Sat.Literal.pos 3913)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3913) = lexBefore s permutation8 13 := by
  exact (positive_lex_of_descriptor s 3913 permutation8 14 (by rfl)).trans ((lex_skipped s permutation8 13 14 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation8 13) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation8 13 by rw [image8_eq]; rfl))

theorem lex_8_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3914) (Sat.Literal.pos 3913) (Sat.Literal.pos 13) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation8 13 (assignment s)
    (Sat.Literal.pos 3914) (Sat.Literal.pos 3913) (Sat.Literal.pos 13) (Sat.Literal.pos 52) (positive_of_descriptor s 3914 (.lex permutation8 13) (by rfl)) (lex_8_13_prefix s) (positive_select s 13) (lex_8_13_image s)

theorem lex_8_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.pos 13), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation8 13 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3913) (Sat.Literal.pos 13) (Sat.Literal.pos 52) (lex_8_13_prefix s) (positive_select s 13) (lex_8_13_image s)

theorem lex_8_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.pos 3913)] :=
  (lex_8_13_gate s).prop _ (List.Mem.head _)

theorem lex_8_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.neg 13), (Sat.Literal.pos 52)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.pos 13), (Sat.Literal.neg 52)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.neg 13), (Sat.Literal.neg 52), (Sat.Literal.pos 3914)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3913), (Sat.Literal.pos 13), (Sat.Literal.pos 52), (Sat.Literal.pos 3914)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3914) = lexBefore s permutation8 12 := by
  exact (positive_lex_of_descriptor s 3914 permutation8 13 (by rfl)).trans ((lex_skipped s permutation8 12 13 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation8 12) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation8 12 by rw [image8_eq]; rfl))

theorem lex_8_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3915) (Sat.Literal.pos 3914) (Sat.Literal.pos 12) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation8 12 (assignment s)
    (Sat.Literal.pos 3915) (Sat.Literal.pos 3914) (Sat.Literal.pos 12) (Sat.Literal.pos 48) (positive_of_descriptor s 3915 (.lex permutation8 12) (by rfl)) (lex_8_12_prefix s) (positive_select s 12) (lex_8_12_image s)

theorem lex_8_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.pos 12), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation8 12 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3914) (Sat.Literal.pos 12) (Sat.Literal.pos 48) (lex_8_12_prefix s) (positive_select s 12) (lex_8_12_image s)

theorem lex_8_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.pos 3914)] :=
  (lex_8_12_gate s).prop _ (List.Mem.head _)

theorem lex_8_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.neg 12), (Sat.Literal.pos 48)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.pos 12), (Sat.Literal.neg 48)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.neg 12), (Sat.Literal.neg 48), (Sat.Literal.pos 3915)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3914), (Sat.Literal.pos 12), (Sat.Literal.pos 48), (Sat.Literal.pos 3915)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3915) = lexBefore s permutation8 11 := by
  exact (positive_lex_of_descriptor s 3915 permutation8 12 (by rfl)).trans ((lex_skipped s permutation8 11 12 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation8 11) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation8 11 by rw [image8_eq]; rfl))

theorem lex_8_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3916) (Sat.Literal.pos 3915) (Sat.Literal.pos 11) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation8 11 (assignment s)
    (Sat.Literal.pos 3916) (Sat.Literal.pos 3915) (Sat.Literal.pos 11) (Sat.Literal.pos 44) (positive_of_descriptor s 3916 (.lex permutation8 11) (by rfl)) (lex_8_11_prefix s) (positive_select s 11) (lex_8_11_image s)

theorem lex_8_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.pos 11), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation8 11 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3915) (Sat.Literal.pos 11) (Sat.Literal.pos 44) (lex_8_11_prefix s) (positive_select s 11) (lex_8_11_image s)

theorem lex_8_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.pos 3915)] :=
  (lex_8_11_gate s).prop _ (List.Mem.head _)

theorem lex_8_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.neg 11), (Sat.Literal.pos 44)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.pos 11), (Sat.Literal.neg 44)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.neg 11), (Sat.Literal.neg 44), (Sat.Literal.pos 3916)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3915), (Sat.Literal.pos 11), (Sat.Literal.pos 44), (Sat.Literal.pos 3916)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3916) = lexBefore s permutation8 10 := by
  exact (positive_lex_of_descriptor s 3916 permutation8 11 (by rfl)).trans ((lex_skipped s permutation8 10 11 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation8 10) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation8 10 by rw [image8_eq]; rfl))

theorem lex_8_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3917) (Sat.Literal.pos 3916) (Sat.Literal.pos 10) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation8 10 (assignment s)
    (Sat.Literal.pos 3917) (Sat.Literal.pos 3916) (Sat.Literal.pos 10) (Sat.Literal.pos 40) (positive_of_descriptor s 3917 (.lex permutation8 10) (by rfl)) (lex_8_10_prefix s) (positive_select s 10) (lex_8_10_image s)

theorem lex_8_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.pos 10), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation8 10 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3916) (Sat.Literal.pos 10) (Sat.Literal.pos 40) (lex_8_10_prefix s) (positive_select s 10) (lex_8_10_image s)

theorem lex_8_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.pos 3916)] :=
  (lex_8_10_gate s).prop _ (List.Mem.head _)

theorem lex_8_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.neg 10), (Sat.Literal.pos 40)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.pos 10), (Sat.Literal.neg 40)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.neg 10), (Sat.Literal.neg 40), (Sat.Literal.pos 3917)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3916), (Sat.Literal.pos 10), (Sat.Literal.pos 40), (Sat.Literal.pos 3917)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3917) = lexBefore s permutation8 9 := by
  exact (positive_lex_of_descriptor s 3917 permutation8 10 (by rfl)).trans ((lex_skipped s permutation8 9 10 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation8 9) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation8 9 by rw [image8_eq]; rfl))

theorem lex_8_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3918) (Sat.Literal.pos 3917) (Sat.Literal.pos 9) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation8 9 (assignment s)
    (Sat.Literal.pos 3918) (Sat.Literal.pos 3917) (Sat.Literal.pos 9) (Sat.Literal.pos 36) (positive_of_descriptor s 3918 (.lex permutation8 9) (by rfl)) (lex_8_9_prefix s) (positive_select s 9) (lex_8_9_image s)

theorem lex_8_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.pos 9), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation8 9 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3917) (Sat.Literal.pos 9) (Sat.Literal.pos 36) (lex_8_9_prefix s) (positive_select s 9) (lex_8_9_image s)

theorem lex_8_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.pos 3917)] :=
  (lex_8_9_gate s).prop _ (List.Mem.head _)

theorem lex_8_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.neg 9), (Sat.Literal.pos 36)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.pos 9), (Sat.Literal.neg 36)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.neg 9), (Sat.Literal.neg 36), (Sat.Literal.pos 3918)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3917), (Sat.Literal.pos 9), (Sat.Literal.pos 36), (Sat.Literal.pos 3918)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3918) = lexBefore s permutation8 8 := by
  exact (positive_lex_of_descriptor s 3918 permutation8 9 (by rfl)).trans ((lex_skipped s permutation8 8 9 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation8 8) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation8 8 by rw [image8_eq]; rfl))

theorem lex_8_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3919) (Sat.Literal.pos 3918) (Sat.Literal.pos 8) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation8 8 (assignment s)
    (Sat.Literal.pos 3919) (Sat.Literal.pos 3918) (Sat.Literal.pos 8) (Sat.Literal.pos 32) (positive_of_descriptor s 3919 (.lex permutation8 8) (by rfl)) (lex_8_8_prefix s) (positive_select s 8) (lex_8_8_image s)

theorem lex_8_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.pos 8), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation8 8 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3918) (Sat.Literal.pos 8) (Sat.Literal.pos 32) (lex_8_8_prefix s) (positive_select s 8) (lex_8_8_image s)

theorem lex_8_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.pos 3918)] :=
  (lex_8_8_gate s).prop _ (List.Mem.head _)

theorem lex_8_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.neg 8), (Sat.Literal.pos 32)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.pos 8), (Sat.Literal.neg 32)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.neg 8), (Sat.Literal.neg 32), (Sat.Literal.pos 3919)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3918), (Sat.Literal.pos 8), (Sat.Literal.pos 32), (Sat.Literal.pos 3919)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3919) = lexBefore s permutation8 7 := by
  exact (positive_lex_of_descriptor s 3919 permutation8 8 (by rfl)).trans ((lex_skipped s permutation8 7 8 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation8 7) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation8 7 by rw [image8_eq]; rfl))

theorem lex_8_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3920) (Sat.Literal.pos 3919) (Sat.Literal.pos 7) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation8 7 (assignment s)
    (Sat.Literal.pos 3920) (Sat.Literal.pos 3919) (Sat.Literal.pos 7) (Sat.Literal.pos 28) (positive_of_descriptor s 3920 (.lex permutation8 7) (by rfl)) (lex_8_7_prefix s) (positive_select s 7) (lex_8_7_image s)

theorem lex_8_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.pos 7), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation8 7 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3919) (Sat.Literal.pos 7) (Sat.Literal.pos 28) (lex_8_7_prefix s) (positive_select s 7) (lex_8_7_image s)

theorem lex_8_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.pos 3919)] :=
  (lex_8_7_gate s).prop _ (List.Mem.head _)

theorem lex_8_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.neg 7), (Sat.Literal.pos 28)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.pos 7), (Sat.Literal.neg 28)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.neg 7), (Sat.Literal.neg 28), (Sat.Literal.pos 3920)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3919), (Sat.Literal.pos 7), (Sat.Literal.pos 28), (Sat.Literal.pos 3920)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3920) = lexBefore s permutation8 6 := by
  exact (positive_lex_of_descriptor s 3920 permutation8 7 (by rfl)).trans ((lex_skipped s permutation8 6 7 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation8 6) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation8 6 by rw [image8_eq]; rfl))

theorem lex_8_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3921) (Sat.Literal.pos 3920) (Sat.Literal.pos 6) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation8 6 (assignment s)
    (Sat.Literal.pos 3921) (Sat.Literal.pos 3920) (Sat.Literal.pos 6) (Sat.Literal.pos 24) (positive_of_descriptor s 3921 (.lex permutation8 6) (by rfl)) (lex_8_6_prefix s) (positive_select s 6) (lex_8_6_image s)

theorem lex_8_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.pos 6), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation8 6 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3920) (Sat.Literal.pos 6) (Sat.Literal.pos 24) (lex_8_6_prefix s) (positive_select s 6) (lex_8_6_image s)

theorem lex_8_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.pos 3920)] :=
  (lex_8_6_gate s).prop _ (List.Mem.head _)

theorem lex_8_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.neg 6), (Sat.Literal.pos 24)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.pos 6), (Sat.Literal.neg 24)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.neg 6), (Sat.Literal.neg 24), (Sat.Literal.pos 3921)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3920), (Sat.Literal.pos 6), (Sat.Literal.pos 24), (Sat.Literal.pos 3921)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3921) = lexBefore s permutation8 5 := by
  exact (positive_lex_of_descriptor s 3921 permutation8 6 (by rfl)).trans ((lex_skipped s permutation8 5 6 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation8 5) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation8 5 by rw [image8_eq]; rfl))

theorem lex_8_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3922) (Sat.Literal.pos 3921) (Sat.Literal.pos 5) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation8 5 (assignment s)
    (Sat.Literal.pos 3922) (Sat.Literal.pos 3921) (Sat.Literal.pos 5) (Sat.Literal.pos 20) (positive_of_descriptor s 3922 (.lex permutation8 5) (by rfl)) (lex_8_5_prefix s) (positive_select s 5) (lex_8_5_image s)

theorem lex_8_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.pos 5), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation8 5 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3921) (Sat.Literal.pos 5) (Sat.Literal.pos 20) (lex_8_5_prefix s) (positive_select s 5) (lex_8_5_image s)

theorem lex_8_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.pos 3921)] :=
  (lex_8_5_gate s).prop _ (List.Mem.head _)

theorem lex_8_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.neg 5), (Sat.Literal.pos 20)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.pos 5), (Sat.Literal.neg 20)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.neg 5), (Sat.Literal.neg 20), (Sat.Literal.pos 3922)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3921), (Sat.Literal.pos 5), (Sat.Literal.pos 20), (Sat.Literal.pos 3922)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3922) = lexBefore s permutation8 4 := by
  exact (positive_lex_of_descriptor s 3922 permutation8 5 (by rfl)).trans ((lex_skipped s permutation8 4 5 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation8 4) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation8 4 by rw [image8_eq]; rfl))

theorem lex_8_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3923) (Sat.Literal.pos 3922) (Sat.Literal.pos 4) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation8 4 (assignment s)
    (Sat.Literal.pos 3923) (Sat.Literal.pos 3922) (Sat.Literal.pos 4) (Sat.Literal.pos 16) (positive_of_descriptor s 3923 (.lex permutation8 4) (by rfl)) (lex_8_4_prefix s) (positive_select s 4) (lex_8_4_image s)

theorem lex_8_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.pos 4), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation8 4 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3922) (Sat.Literal.pos 4) (Sat.Literal.pos 16) (lex_8_4_prefix s) (positive_select s 4) (lex_8_4_image s)

theorem lex_8_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.pos 3922)] :=
  (lex_8_4_gate s).prop _ (List.Mem.head _)

theorem lex_8_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.neg 4), (Sat.Literal.pos 16)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.pos 4), (Sat.Literal.neg 16)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.neg 4), (Sat.Literal.neg 16), (Sat.Literal.pos 3923)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3922), (Sat.Literal.pos 4), (Sat.Literal.pos 16), (Sat.Literal.pos 3923)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3923) = lexBefore s permutation8 3 := by
  exact (positive_lex_of_descriptor s 3923 permutation8 4 (by rfl)).trans ((lex_skipped s permutation8 3 4 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation8 3) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation8 3 by rw [image8_eq]; rfl))

theorem lex_8_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3924) (Sat.Literal.pos 3923) (Sat.Literal.pos 3) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation8 3 (assignment s)
    (Sat.Literal.pos 3924) (Sat.Literal.pos 3923) (Sat.Literal.pos 3) (Sat.Literal.pos 12) (positive_of_descriptor s 3924 (.lex permutation8 3) (by rfl)) (lex_8_3_prefix s) (positive_select s 3) (lex_8_3_image s)

theorem lex_8_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.pos 3), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation8 3 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3923) (Sat.Literal.pos 3) (Sat.Literal.pos 12) (lex_8_3_prefix s) (positive_select s 3) (lex_8_3_image s)

theorem lex_8_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.pos 3923)] :=
  (lex_8_3_gate s).prop _ (List.Mem.head _)

theorem lex_8_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.neg 3), (Sat.Literal.pos 12)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.pos 3), (Sat.Literal.neg 12)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.neg 3), (Sat.Literal.neg 12), (Sat.Literal.pos 3924)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3923), (Sat.Literal.pos 3), (Sat.Literal.pos 12), (Sat.Literal.pos 3924)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_8_103_gate

end Crown.CertificateData
