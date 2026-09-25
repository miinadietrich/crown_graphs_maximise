import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_12_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4824) = lexBefore s permutation12 103 := by
  exact (positive_lex_of_descriptor s 4824 permutation12 104 (by rfl)).trans ((lex_skipped s permutation12 103 104 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation12 103) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation12 103 by rw [image12_eq]; rfl))

theorem lex_12_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4825) (Sat.Literal.pos 4824) (Sat.Literal.pos 103) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation12 103 (assignment s)
    (Sat.Literal.pos 4825) (Sat.Literal.pos 4824) (Sat.Literal.pos 103) (Sat.Literal.pos 217) (positive_of_descriptor s 4825 (.lex permutation12 103) (by rfl)) (lex_12_103_prefix s) (positive_select s 103) (lex_12_103_image s)

theorem lex_12_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.pos 103), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation12 103 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4824) (Sat.Literal.pos 103) (Sat.Literal.pos 217) (lex_12_103_prefix s) (positive_select s 103) (lex_12_103_image s)

theorem lex_12_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.pos 4824)] :=
  (lex_12_103_gate s).prop _ (List.Mem.head _)

theorem lex_12_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.neg 103), (Sat.Literal.pos 217)] :=
  (lex_12_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.pos 103), (Sat.Literal.neg 217)] :=
  (lex_12_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.neg 103), (Sat.Literal.neg 217), (Sat.Literal.pos 4825)] :=
  (lex_12_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4824), (Sat.Literal.pos 103), (Sat.Literal.pos 217), (Sat.Literal.pos 4825)] :=
  (lex_12_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4825) = lexBefore s permutation12 102 := by
  exact (positive_lex_of_descriptor s 4825 permutation12 103 (by rfl)).trans ((lex_skipped s permutation12 102 103 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation12 102) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation12 102 by rw [image12_eq]; rfl))

theorem lex_12_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4826) (Sat.Literal.pos 4825) (Sat.Literal.pos 102) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation12 102 (assignment s)
    (Sat.Literal.pos 4826) (Sat.Literal.pos 4825) (Sat.Literal.pos 102) (Sat.Literal.pos 153) (positive_of_descriptor s 4826 (.lex permutation12 102) (by rfl)) (lex_12_102_prefix s) (positive_select s 102) (lex_12_102_image s)

theorem lex_12_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.pos 102), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation12 102 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4825) (Sat.Literal.pos 102) (Sat.Literal.pos 153) (lex_12_102_prefix s) (positive_select s 102) (lex_12_102_image s)

theorem lex_12_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.pos 4825)] :=
  (lex_12_102_gate s).prop _ (List.Mem.head _)

theorem lex_12_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.neg 102), (Sat.Literal.pos 153)] :=
  (lex_12_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.pos 102), (Sat.Literal.neg 153)] :=
  (lex_12_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.neg 102), (Sat.Literal.neg 153), (Sat.Literal.pos 4826)] :=
  (lex_12_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4825), (Sat.Literal.pos 102), (Sat.Literal.pos 153), (Sat.Literal.pos 4826)] :=
  (lex_12_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4826) = lexBefore s permutation12 101 := by
  exact (positive_lex_of_descriptor s 4826 permutation12 102 (by rfl)).trans ((lex_skipped s permutation12 101 102 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation12 101) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation12 101 by rw [image12_eq]; rfl))

theorem lex_12_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4827) (Sat.Literal.pos 4826) (Sat.Literal.pos 101) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation12 101 (assignment s)
    (Sat.Literal.pos 4827) (Sat.Literal.pos 4826) (Sat.Literal.pos 101) (Sat.Literal.pos 89) (positive_of_descriptor s 4827 (.lex permutation12 101) (by rfl)) (lex_12_101_prefix s) (positive_select s 101) (lex_12_101_image s)

theorem lex_12_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.pos 101), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation12 101 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4826) (Sat.Literal.pos 101) (Sat.Literal.pos 89) (lex_12_101_prefix s) (positive_select s 101) (lex_12_101_image s)

theorem lex_12_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.pos 4826)] :=
  (lex_12_101_gate s).prop _ (List.Mem.head _)

theorem lex_12_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.neg 101), (Sat.Literal.pos 89)] :=
  (lex_12_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.pos 101), (Sat.Literal.neg 89)] :=
  (lex_12_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.neg 101), (Sat.Literal.neg 89), (Sat.Literal.pos 4827)] :=
  (lex_12_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4826), (Sat.Literal.pos 101), (Sat.Literal.pos 89), (Sat.Literal.pos 4827)] :=
  (lex_12_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4827) = lexBefore s permutation12 100 := by
  exact (positive_lex_of_descriptor s 4827 permutation12 101 (by rfl)).trans ((lex_skipped s permutation12 100 101 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation12 100) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation12 100 by rw [image12_eq]; rfl))

theorem lex_12_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4828) (Sat.Literal.pos 4827) (Sat.Literal.pos 100) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation12 100 (assignment s)
    (Sat.Literal.pos 4828) (Sat.Literal.pos 4827) (Sat.Literal.pos 100) (Sat.Literal.pos 25) (positive_of_descriptor s 4828 (.lex permutation12 100) (by rfl)) (lex_12_100_prefix s) (positive_select s 100) (lex_12_100_image s)

theorem lex_12_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.pos 100), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation12 100 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4827) (Sat.Literal.pos 100) (Sat.Literal.pos 25) (lex_12_100_prefix s) (positive_select s 100) (lex_12_100_image s)

theorem lex_12_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.pos 4827)] :=
  (lex_12_100_gate s).prop _ (List.Mem.head _)

theorem lex_12_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.neg 100), (Sat.Literal.pos 25)] :=
  (lex_12_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.pos 100), (Sat.Literal.neg 25)] :=
  (lex_12_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.neg 100), (Sat.Literal.neg 25), (Sat.Literal.pos 4828)] :=
  (lex_12_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4827), (Sat.Literal.pos 100), (Sat.Literal.pos 25), (Sat.Literal.pos 4828)] :=
  (lex_12_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4828) = lexBefore s permutation12 99 := by
  exact (positive_lex_of_descriptor s 4828 permutation12 100 (by rfl)).trans ((lex_skipped s permutation12 99 100 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation12 99) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation12 99 by rw [image12_eq]; rfl))

theorem lex_12_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4829) (Sat.Literal.pos 4828) (Sat.Literal.pos 99) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation12 99 (assignment s)
    (Sat.Literal.pos 4829) (Sat.Literal.pos 4828) (Sat.Literal.pos 99) (Sat.Literal.pos 216) (positive_of_descriptor s 4829 (.lex permutation12 99) (by rfl)) (lex_12_99_prefix s) (positive_select s 99) (lex_12_99_image s)

theorem lex_12_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.pos 99), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation12 99 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4828) (Sat.Literal.pos 99) (Sat.Literal.pos 216) (lex_12_99_prefix s) (positive_select s 99) (lex_12_99_image s)

theorem lex_12_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.pos 4828)] :=
  (lex_12_99_gate s).prop _ (List.Mem.head _)

theorem lex_12_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.neg 99), (Sat.Literal.pos 216)] :=
  (lex_12_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.pos 99), (Sat.Literal.neg 216)] :=
  (lex_12_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.neg 99), (Sat.Literal.neg 216), (Sat.Literal.pos 4829)] :=
  (lex_12_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4828), (Sat.Literal.pos 99), (Sat.Literal.pos 216), (Sat.Literal.pos 4829)] :=
  (lex_12_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4829) = lexBefore s permutation12 98 := by
  exact (positive_lex_of_descriptor s 4829 permutation12 99 (by rfl)).trans ((lex_skipped s permutation12 98 99 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation12 98) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation12 98 by rw [image12_eq]; rfl))

theorem lex_12_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4830) (Sat.Literal.pos 4829) (Sat.Literal.pos 98) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation12 98 (assignment s)
    (Sat.Literal.pos 4830) (Sat.Literal.pos 4829) (Sat.Literal.pos 98) (Sat.Literal.pos 152) (positive_of_descriptor s 4830 (.lex permutation12 98) (by rfl)) (lex_12_98_prefix s) (positive_select s 98) (lex_12_98_image s)

theorem lex_12_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.pos 98), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation12 98 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4829) (Sat.Literal.pos 98) (Sat.Literal.pos 152) (lex_12_98_prefix s) (positive_select s 98) (lex_12_98_image s)

theorem lex_12_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.pos 4829)] :=
  (lex_12_98_gate s).prop _ (List.Mem.head _)

theorem lex_12_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.neg 98), (Sat.Literal.pos 152)] :=
  (lex_12_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.pos 98), (Sat.Literal.neg 152)] :=
  (lex_12_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.neg 98), (Sat.Literal.neg 152), (Sat.Literal.pos 4830)] :=
  (lex_12_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4829), (Sat.Literal.pos 98), (Sat.Literal.pos 152), (Sat.Literal.pos 4830)] :=
  (lex_12_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4830) = lexBefore s permutation12 97 := by
  exact (positive_lex_of_descriptor s 4830 permutation12 98 (by rfl)).trans ((lex_skipped s permutation12 97 98 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation12 97) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation12 97 by rw [image12_eq]; rfl))

theorem lex_12_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4831) (Sat.Literal.pos 4830) (Sat.Literal.pos 97) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation12 97 (assignment s)
    (Sat.Literal.pos 4831) (Sat.Literal.pos 4830) (Sat.Literal.pos 97) (Sat.Literal.pos 88) (positive_of_descriptor s 4831 (.lex permutation12 97) (by rfl)) (lex_12_97_prefix s) (positive_select s 97) (lex_12_97_image s)

theorem lex_12_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.pos 97), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation12 97 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4830) (Sat.Literal.pos 97) (Sat.Literal.pos 88) (lex_12_97_prefix s) (positive_select s 97) (lex_12_97_image s)

theorem lex_12_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.pos 4830)] :=
  (lex_12_97_gate s).prop _ (List.Mem.head _)

theorem lex_12_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.neg 97), (Sat.Literal.pos 88)] :=
  (lex_12_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.pos 97), (Sat.Literal.neg 88)] :=
  (lex_12_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.neg 97), (Sat.Literal.neg 88), (Sat.Literal.pos 4831)] :=
  (lex_12_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4830), (Sat.Literal.pos 97), (Sat.Literal.pos 88), (Sat.Literal.pos 4831)] :=
  (lex_12_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4831) = lexBefore s permutation12 96 := by
  exact (positive_lex_of_descriptor s 4831 permutation12 97 (by rfl)).trans ((lex_skipped s permutation12 96 97 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation12 96) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation12 96 by rw [image12_eq]; rfl))

theorem lex_12_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4832) (Sat.Literal.pos 4831) (Sat.Literal.pos 96) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation12 96 (assignment s)
    (Sat.Literal.pos 4832) (Sat.Literal.pos 4831) (Sat.Literal.pos 96) (Sat.Literal.pos 24) (positive_of_descriptor s 4832 (.lex permutation12 96) (by rfl)) (lex_12_96_prefix s) (positive_select s 96) (lex_12_96_image s)

theorem lex_12_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.pos 96), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation12 96 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4831) (Sat.Literal.pos 96) (Sat.Literal.pos 24) (lex_12_96_prefix s) (positive_select s 96) (lex_12_96_image s)

theorem lex_12_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.pos 4831)] :=
  (lex_12_96_gate s).prop _ (List.Mem.head _)

theorem lex_12_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.neg 96), (Sat.Literal.pos 24)] :=
  (lex_12_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.pos 96), (Sat.Literal.neg 24)] :=
  (lex_12_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.neg 96), (Sat.Literal.neg 24), (Sat.Literal.pos 4832)] :=
  (lex_12_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4831), (Sat.Literal.pos 96), (Sat.Literal.pos 24), (Sat.Literal.pos 4832)] :=
  (lex_12_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4832) = lexBefore s permutation12 95 := by
  exact (positive_lex_of_descriptor s 4832 permutation12 96 (by rfl)).trans ((lex_skipped s permutation12 95 96 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation12 95) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation12 95 by rw [image12_eq]; rfl))

theorem lex_12_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4833) (Sat.Literal.pos 4832) (Sat.Literal.pos 95) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation12 95 (assignment s)
    (Sat.Literal.pos 4833) (Sat.Literal.pos 4832) (Sat.Literal.pos 95) (Sat.Literal.pos 215) (positive_of_descriptor s 4833 (.lex permutation12 95) (by rfl)) (lex_12_95_prefix s) (positive_select s 95) (lex_12_95_image s)

theorem lex_12_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.pos 95), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation12 95 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4832) (Sat.Literal.pos 95) (Sat.Literal.pos 215) (lex_12_95_prefix s) (positive_select s 95) (lex_12_95_image s)

theorem lex_12_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.pos 4832)] :=
  (lex_12_95_gate s).prop _ (List.Mem.head _)

theorem lex_12_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.neg 95), (Sat.Literal.pos 215)] :=
  (lex_12_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.pos 95), (Sat.Literal.neg 215)] :=
  (lex_12_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.neg 95), (Sat.Literal.neg 215), (Sat.Literal.pos 4833)] :=
  (lex_12_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4832), (Sat.Literal.pos 95), (Sat.Literal.pos 215), (Sat.Literal.pos 4833)] :=
  (lex_12_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4833) = lexBefore s permutation12 94 := by
  exact (positive_lex_of_descriptor s 4833 permutation12 95 (by rfl)).trans ((lex_skipped s permutation12 94 95 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation12 94) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation12 94 by rw [image12_eq]; rfl))

theorem lex_12_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4834) (Sat.Literal.pos 4833) (Sat.Literal.pos 94) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation12 94 (assignment s)
    (Sat.Literal.pos 4834) (Sat.Literal.pos 4833) (Sat.Literal.pos 94) (Sat.Literal.pos 151) (positive_of_descriptor s 4834 (.lex permutation12 94) (by rfl)) (lex_12_94_prefix s) (positive_select s 94) (lex_12_94_image s)

theorem lex_12_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.pos 94), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation12 94 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4833) (Sat.Literal.pos 94) (Sat.Literal.pos 151) (lex_12_94_prefix s) (positive_select s 94) (lex_12_94_image s)

theorem lex_12_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.pos 4833)] :=
  (lex_12_94_gate s).prop _ (List.Mem.head _)

theorem lex_12_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.neg 94), (Sat.Literal.pos 151)] :=
  (lex_12_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.pos 94), (Sat.Literal.neg 151)] :=
  (lex_12_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.neg 94), (Sat.Literal.neg 151), (Sat.Literal.pos 4834)] :=
  (lex_12_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4833), (Sat.Literal.pos 94), (Sat.Literal.pos 151), (Sat.Literal.pos 4834)] :=
  (lex_12_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4834) = lexBefore s permutation12 93 := by
  exact (positive_lex_of_descriptor s 4834 permutation12 94 (by rfl)).trans ((lex_skipped s permutation12 93 94 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation12 93) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation12 93 by rw [image12_eq]; rfl))

theorem lex_12_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4835) (Sat.Literal.pos 4834) (Sat.Literal.pos 93) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation12 93 (assignment s)
    (Sat.Literal.pos 4835) (Sat.Literal.pos 4834) (Sat.Literal.pos 93) (Sat.Literal.pos 87) (positive_of_descriptor s 4835 (.lex permutation12 93) (by rfl)) (lex_12_93_prefix s) (positive_select s 93) (lex_12_93_image s)

theorem lex_12_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.pos 93), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation12 93 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4834) (Sat.Literal.pos 93) (Sat.Literal.pos 87) (lex_12_93_prefix s) (positive_select s 93) (lex_12_93_image s)

theorem lex_12_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.pos 4834)] :=
  (lex_12_93_gate s).prop _ (List.Mem.head _)

theorem lex_12_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.neg 93), (Sat.Literal.pos 87)] :=
  (lex_12_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.pos 93), (Sat.Literal.neg 87)] :=
  (lex_12_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.neg 93), (Sat.Literal.neg 87), (Sat.Literal.pos 4835)] :=
  (lex_12_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4834), (Sat.Literal.pos 93), (Sat.Literal.pos 87), (Sat.Literal.pos 4835)] :=
  (lex_12_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4835) = lexBefore s permutation12 92 := by
  exact (positive_lex_of_descriptor s 4835 permutation12 93 (by rfl)).trans ((lex_skipped s permutation12 92 93 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation12 92) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation12 92 by rw [image12_eq]; rfl))

theorem lex_12_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4836) (Sat.Literal.pos 4835) (Sat.Literal.pos 92) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation12 92 (assignment s)
    (Sat.Literal.pos 4836) (Sat.Literal.pos 4835) (Sat.Literal.pos 92) (Sat.Literal.pos 23) (positive_of_descriptor s 4836 (.lex permutation12 92) (by rfl)) (lex_12_92_prefix s) (positive_select s 92) (lex_12_92_image s)

theorem lex_12_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.pos 92), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation12 92 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4835) (Sat.Literal.pos 92) (Sat.Literal.pos 23) (lex_12_92_prefix s) (positive_select s 92) (lex_12_92_image s)

theorem lex_12_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.pos 4835)] :=
  (lex_12_92_gate s).prop _ (List.Mem.head _)

theorem lex_12_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.neg 92), (Sat.Literal.pos 23)] :=
  (lex_12_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.pos 92), (Sat.Literal.neg 23)] :=
  (lex_12_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.neg 92), (Sat.Literal.neg 23), (Sat.Literal.pos 4836)] :=
  (lex_12_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4835), (Sat.Literal.pos 92), (Sat.Literal.pos 23), (Sat.Literal.pos 4836)] :=
  (lex_12_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4836) = lexBefore s permutation12 91 := by
  exact (positive_lex_of_descriptor s 4836 permutation12 92 (by rfl)).trans ((lex_skipped s permutation12 91 92 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation12 91) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation12 91 by rw [image12_eq]; rfl))

theorem lex_12_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4837) (Sat.Literal.pos 4836) (Sat.Literal.pos 91) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation12 91 (assignment s)
    (Sat.Literal.pos 4837) (Sat.Literal.pos 4836) (Sat.Literal.pos 91) (Sat.Literal.pos 214) (positive_of_descriptor s 4837 (.lex permutation12 91) (by rfl)) (lex_12_91_prefix s) (positive_select s 91) (lex_12_91_image s)

theorem lex_12_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.pos 91), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation12 91 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4836) (Sat.Literal.pos 91) (Sat.Literal.pos 214) (lex_12_91_prefix s) (positive_select s 91) (lex_12_91_image s)

theorem lex_12_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.pos 4836)] :=
  (lex_12_91_gate s).prop _ (List.Mem.head _)

theorem lex_12_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.neg 91), (Sat.Literal.pos 214)] :=
  (lex_12_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.pos 91), (Sat.Literal.neg 214)] :=
  (lex_12_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.neg 91), (Sat.Literal.neg 214), (Sat.Literal.pos 4837)] :=
  (lex_12_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4836), (Sat.Literal.pos 91), (Sat.Literal.pos 214), (Sat.Literal.pos 4837)] :=
  (lex_12_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4837) = lexBefore s permutation12 90 := by
  exact (positive_lex_of_descriptor s 4837 permutation12 91 (by rfl)).trans ((lex_skipped s permutation12 90 91 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation12 90) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation12 90 by rw [image12_eq]; rfl))

theorem lex_12_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4838) (Sat.Literal.pos 4837) (Sat.Literal.pos 90) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation12 90 (assignment s)
    (Sat.Literal.pos 4838) (Sat.Literal.pos 4837) (Sat.Literal.pos 90) (Sat.Literal.pos 150) (positive_of_descriptor s 4838 (.lex permutation12 90) (by rfl)) (lex_12_90_prefix s) (positive_select s 90) (lex_12_90_image s)

theorem lex_12_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.pos 90), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation12 90 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4837) (Sat.Literal.pos 90) (Sat.Literal.pos 150) (lex_12_90_prefix s) (positive_select s 90) (lex_12_90_image s)

theorem lex_12_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.pos 4837)] :=
  (lex_12_90_gate s).prop _ (List.Mem.head _)

theorem lex_12_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.neg 90), (Sat.Literal.pos 150)] :=
  (lex_12_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.pos 90), (Sat.Literal.neg 150)] :=
  (lex_12_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.neg 90), (Sat.Literal.neg 150), (Sat.Literal.pos 4838)] :=
  (lex_12_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4837), (Sat.Literal.pos 90), (Sat.Literal.pos 150), (Sat.Literal.pos 4838)] :=
  (lex_12_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4838) = lexBefore s permutation12 89 := by
  exact (positive_lex_of_descriptor s 4838 permutation12 90 (by rfl)).trans ((lex_skipped s permutation12 89 90 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation12 89) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation12 89 by rw [image12_eq]; rfl))

theorem lex_12_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4839) (Sat.Literal.pos 4838) (Sat.Literal.pos 89) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation12 89 (assignment s)
    (Sat.Literal.pos 4839) (Sat.Literal.pos 4838) (Sat.Literal.pos 89) (Sat.Literal.pos 86) (positive_of_descriptor s 4839 (.lex permutation12 89) (by rfl)) (lex_12_89_prefix s) (positive_select s 89) (lex_12_89_image s)

theorem lex_12_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.pos 89), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation12 89 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4838) (Sat.Literal.pos 89) (Sat.Literal.pos 86) (lex_12_89_prefix s) (positive_select s 89) (lex_12_89_image s)

theorem lex_12_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.pos 4838)] :=
  (lex_12_89_gate s).prop _ (List.Mem.head _)

theorem lex_12_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.neg 89), (Sat.Literal.pos 86)] :=
  (lex_12_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.pos 89), (Sat.Literal.neg 86)] :=
  (lex_12_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.neg 89), (Sat.Literal.neg 86), (Sat.Literal.pos 4839)] :=
  (lex_12_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4838), (Sat.Literal.pos 89), (Sat.Literal.pos 86), (Sat.Literal.pos 4839)] :=
  (lex_12_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4839) = lexBefore s permutation12 88 := by
  exact (positive_lex_of_descriptor s 4839 permutation12 89 (by rfl)).trans ((lex_skipped s permutation12 88 89 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation12 88) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation12 88 by rw [image12_eq]; rfl))

theorem lex_12_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4840) (Sat.Literal.pos 4839) (Sat.Literal.pos 88) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation12 88 (assignment s)
    (Sat.Literal.pos 4840) (Sat.Literal.pos 4839) (Sat.Literal.pos 88) (Sat.Literal.pos 22) (positive_of_descriptor s 4840 (.lex permutation12 88) (by rfl)) (lex_12_88_prefix s) (positive_select s 88) (lex_12_88_image s)

theorem lex_12_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.pos 88), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation12 88 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4839) (Sat.Literal.pos 88) (Sat.Literal.pos 22) (lex_12_88_prefix s) (positive_select s 88) (lex_12_88_image s)

theorem lex_12_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.pos 4839)] :=
  (lex_12_88_gate s).prop _ (List.Mem.head _)

theorem lex_12_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.neg 88), (Sat.Literal.pos 22)] :=
  (lex_12_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.pos 88), (Sat.Literal.neg 22)] :=
  (lex_12_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.neg 88), (Sat.Literal.neg 22), (Sat.Literal.pos 4840)] :=
  (lex_12_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4839), (Sat.Literal.pos 88), (Sat.Literal.pos 22), (Sat.Literal.pos 4840)] :=
  (lex_12_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4840) = lexBefore s permutation12 87 := by
  exact (positive_lex_of_descriptor s 4840 permutation12 88 (by rfl)).trans ((lex_skipped s permutation12 87 88 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation12 87) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation12 87 by rw [image12_eq]; rfl))

theorem lex_12_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4841) (Sat.Literal.pos 4840) (Sat.Literal.pos 87) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation12 87 (assignment s)
    (Sat.Literal.pos 4841) (Sat.Literal.pos 4840) (Sat.Literal.pos 87) (Sat.Literal.pos 213) (positive_of_descriptor s 4841 (.lex permutation12 87) (by rfl)) (lex_12_87_prefix s) (positive_select s 87) (lex_12_87_image s)

theorem lex_12_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.pos 87), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation12 87 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4840) (Sat.Literal.pos 87) (Sat.Literal.pos 213) (lex_12_87_prefix s) (positive_select s 87) (lex_12_87_image s)

theorem lex_12_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.pos 4840)] :=
  (lex_12_87_gate s).prop _ (List.Mem.head _)

theorem lex_12_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.neg 87), (Sat.Literal.pos 213)] :=
  (lex_12_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.pos 87), (Sat.Literal.neg 213)] :=
  (lex_12_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.neg 87), (Sat.Literal.neg 213), (Sat.Literal.pos 4841)] :=
  (lex_12_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4840), (Sat.Literal.pos 87), (Sat.Literal.pos 213), (Sat.Literal.pos 4841)] :=
  (lex_12_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4841) = lexBefore s permutation12 86 := by
  exact (positive_lex_of_descriptor s 4841 permutation12 87 (by rfl)).trans ((lex_skipped s permutation12 86 87 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation12 86) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation12 86 by rw [image12_eq]; rfl))

theorem lex_12_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4842) (Sat.Literal.pos 4841) (Sat.Literal.pos 86) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation12 86 (assignment s)
    (Sat.Literal.pos 4842) (Sat.Literal.pos 4841) (Sat.Literal.pos 86) (Sat.Literal.pos 149) (positive_of_descriptor s 4842 (.lex permutation12 86) (by rfl)) (lex_12_86_prefix s) (positive_select s 86) (lex_12_86_image s)

theorem lex_12_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.pos 86), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation12 86 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4841) (Sat.Literal.pos 86) (Sat.Literal.pos 149) (lex_12_86_prefix s) (positive_select s 86) (lex_12_86_image s)

theorem lex_12_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.pos 4841)] :=
  (lex_12_86_gate s).prop _ (List.Mem.head _)

theorem lex_12_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.neg 86), (Sat.Literal.pos 149)] :=
  (lex_12_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.pos 86), (Sat.Literal.neg 149)] :=
  (lex_12_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.neg 86), (Sat.Literal.neg 149), (Sat.Literal.pos 4842)] :=
  (lex_12_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4841), (Sat.Literal.pos 86), (Sat.Literal.pos 149), (Sat.Literal.pos 4842)] :=
  (lex_12_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4842) = lexBefore s permutation12 84 := by
  exact (positive_lex_of_descriptor s 4842 permutation12 86 (by rfl)).trans ((lex_skipped s permutation12 84 86 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 85 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation12 84) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation12 84 by rw [image12_eq]; rfl))

theorem lex_12_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4843) (Sat.Literal.pos 4842) (Sat.Literal.pos 84) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation12 84 (assignment s)
    (Sat.Literal.pos 4843) (Sat.Literal.pos 4842) (Sat.Literal.pos 84) (Sat.Literal.pos 21) (positive_of_descriptor s 4843 (.lex permutation12 84) (by rfl)) (lex_12_84_prefix s) (positive_select s 84) (lex_12_84_image s)

theorem lex_12_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.pos 84), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation12 84 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4842) (Sat.Literal.pos 84) (Sat.Literal.pos 21) (lex_12_84_prefix s) (positive_select s 84) (lex_12_84_image s)

theorem lex_12_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.pos 4842)] :=
  (lex_12_84_gate s).prop _ (List.Mem.head _)

theorem lex_12_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.neg 84), (Sat.Literal.pos 21)] :=
  (lex_12_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.pos 84), (Sat.Literal.neg 21)] :=
  (lex_12_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.neg 84), (Sat.Literal.neg 21), (Sat.Literal.pos 4843)] :=
  (lex_12_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4842), (Sat.Literal.pos 84), (Sat.Literal.pos 21), (Sat.Literal.pos 4843)] :=
  (lex_12_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4843) = lexBefore s permutation12 83 := by
  exact (positive_lex_of_descriptor s 4843 permutation12 84 (by rfl)).trans ((lex_skipped s permutation12 83 84 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation12 83) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation12 83 by rw [image12_eq]; rfl))

theorem lex_12_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4844) (Sat.Literal.pos 4843) (Sat.Literal.pos 83) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation12 83 (assignment s)
    (Sat.Literal.pos 4844) (Sat.Literal.pos 4843) (Sat.Literal.pos 83) (Sat.Literal.pos 212) (positive_of_descriptor s 4844 (.lex permutation12 83) (by rfl)) (lex_12_83_prefix s) (positive_select s 83) (lex_12_83_image s)

theorem lex_12_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.pos 83), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation12 83 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4843) (Sat.Literal.pos 83) (Sat.Literal.pos 212) (lex_12_83_prefix s) (positive_select s 83) (lex_12_83_image s)

theorem lex_12_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.pos 4843)] :=
  (lex_12_83_gate s).prop _ (List.Mem.head _)

theorem lex_12_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.neg 83), (Sat.Literal.pos 212)] :=
  (lex_12_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.pos 83), (Sat.Literal.neg 212)] :=
  (lex_12_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.neg 83), (Sat.Literal.neg 212), (Sat.Literal.pos 4844)] :=
  (lex_12_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4843), (Sat.Literal.pos 83), (Sat.Literal.pos 212), (Sat.Literal.pos 4844)] :=
  (lex_12_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4844) = lexBefore s permutation12 82 := by
  exact (positive_lex_of_descriptor s 4844 permutation12 83 (by rfl)).trans ((lex_skipped s permutation12 82 83 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation12 82) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation12 82 by rw [image12_eq]; rfl))

theorem lex_12_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4845) (Sat.Literal.pos 4844) (Sat.Literal.pos 82) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation12 82 (assignment s)
    (Sat.Literal.pos 4845) (Sat.Literal.pos 4844) (Sat.Literal.pos 82) (Sat.Literal.pos 148) (positive_of_descriptor s 4845 (.lex permutation12 82) (by rfl)) (lex_12_82_prefix s) (positive_select s 82) (lex_12_82_image s)

theorem lex_12_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.pos 82), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation12 82 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4844) (Sat.Literal.pos 82) (Sat.Literal.pos 148) (lex_12_82_prefix s) (positive_select s 82) (lex_12_82_image s)

theorem lex_12_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.pos 4844)] :=
  (lex_12_82_gate s).prop _ (List.Mem.head _)

theorem lex_12_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.neg 82), (Sat.Literal.pos 148)] :=
  (lex_12_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.pos 82), (Sat.Literal.neg 148)] :=
  (lex_12_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.neg 82), (Sat.Literal.neg 148), (Sat.Literal.pos 4845)] :=
  (lex_12_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4844), (Sat.Literal.pos 82), (Sat.Literal.pos 148), (Sat.Literal.pos 4845)] :=
  (lex_12_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4845) = lexBefore s permutation12 81 := by
  exact (positive_lex_of_descriptor s 4845 permutation12 82 (by rfl)).trans ((lex_skipped s permutation12 81 82 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation12 81) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation12 81 by rw [image12_eq]; rfl))

theorem lex_12_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4846) (Sat.Literal.pos 4845) (Sat.Literal.pos 81) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation12 81 (assignment s)
    (Sat.Literal.pos 4846) (Sat.Literal.pos 4845) (Sat.Literal.pos 81) (Sat.Literal.pos 84) (positive_of_descriptor s 4846 (.lex permutation12 81) (by rfl)) (lex_12_81_prefix s) (positive_select s 81) (lex_12_81_image s)

theorem lex_12_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.pos 81), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation12 81 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4845) (Sat.Literal.pos 81) (Sat.Literal.pos 84) (lex_12_81_prefix s) (positive_select s 81) (lex_12_81_image s)

theorem lex_12_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.pos 4845)] :=
  (lex_12_81_gate s).prop _ (List.Mem.head _)

theorem lex_12_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.neg 81), (Sat.Literal.pos 84)] :=
  (lex_12_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.pos 81), (Sat.Literal.neg 84)] :=
  (lex_12_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.neg 81), (Sat.Literal.neg 84), (Sat.Literal.pos 4846)] :=
  (lex_12_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4845), (Sat.Literal.pos 81), (Sat.Literal.pos 84), (Sat.Literal.pos 4846)] :=
  (lex_12_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4846) = lexBefore s permutation12 80 := by
  exact (positive_lex_of_descriptor s 4846 permutation12 81 (by rfl)).trans ((lex_skipped s permutation12 80 81 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation12 80) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation12 80 by rw [image12_eq]; rfl))

theorem lex_12_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4847) (Sat.Literal.pos 4846) (Sat.Literal.pos 80) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation12 80 (assignment s)
    (Sat.Literal.pos 4847) (Sat.Literal.pos 4846) (Sat.Literal.pos 80) (Sat.Literal.pos 20) (positive_of_descriptor s 4847 (.lex permutation12 80) (by rfl)) (lex_12_80_prefix s) (positive_select s 80) (lex_12_80_image s)

theorem lex_12_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.pos 80), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation12 80 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4846) (Sat.Literal.pos 80) (Sat.Literal.pos 20) (lex_12_80_prefix s) (positive_select s 80) (lex_12_80_image s)

theorem lex_12_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.pos 4846)] :=
  (lex_12_80_gate s).prop _ (List.Mem.head _)

theorem lex_12_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.neg 80), (Sat.Literal.pos 20)] :=
  (lex_12_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.pos 80), (Sat.Literal.neg 20)] :=
  (lex_12_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.neg 80), (Sat.Literal.neg 20), (Sat.Literal.pos 4847)] :=
  (lex_12_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4846), (Sat.Literal.pos 80), (Sat.Literal.pos 20), (Sat.Literal.pos 4847)] :=
  (lex_12_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4847) = lexBefore s permutation12 79 := by
  exact (positive_lex_of_descriptor s 4847 permutation12 80 (by rfl)).trans ((lex_skipped s permutation12 79 80 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation12 79) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation12 79 by rw [image12_eq]; rfl))

theorem lex_12_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4848) (Sat.Literal.pos 4847) (Sat.Literal.pos 79) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation12 79 (assignment s)
    (Sat.Literal.pos 4848) (Sat.Literal.pos 4847) (Sat.Literal.pos 79) (Sat.Literal.pos 211) (positive_of_descriptor s 4848 (.lex permutation12 79) (by rfl)) (lex_12_79_prefix s) (positive_select s 79) (lex_12_79_image s)

theorem lex_12_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.pos 79), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation12 79 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4847) (Sat.Literal.pos 79) (Sat.Literal.pos 211) (lex_12_79_prefix s) (positive_select s 79) (lex_12_79_image s)

theorem lex_12_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.pos 4847)] :=
  (lex_12_79_gate s).prop _ (List.Mem.head _)

theorem lex_12_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.neg 79), (Sat.Literal.pos 211)] :=
  (lex_12_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.pos 79), (Sat.Literal.neg 211)] :=
  (lex_12_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.neg 79), (Sat.Literal.neg 211), (Sat.Literal.pos 4848)] :=
  (lex_12_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4847), (Sat.Literal.pos 79), (Sat.Literal.pos 211), (Sat.Literal.pos 4848)] :=
  (lex_12_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4848) = lexBefore s permutation12 78 := by
  exact (positive_lex_of_descriptor s 4848 permutation12 79 (by rfl)).trans ((lex_skipped s permutation12 78 79 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation12 78) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation12 78 by rw [image12_eq]; rfl))

theorem lex_12_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4849) (Sat.Literal.pos 4848) (Sat.Literal.pos 78) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation12 78 (assignment s)
    (Sat.Literal.pos 4849) (Sat.Literal.pos 4848) (Sat.Literal.pos 78) (Sat.Literal.pos 147) (positive_of_descriptor s 4849 (.lex permutation12 78) (by rfl)) (lex_12_78_prefix s) (positive_select s 78) (lex_12_78_image s)

theorem lex_12_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.pos 78), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation12 78 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4848) (Sat.Literal.pos 78) (Sat.Literal.pos 147) (lex_12_78_prefix s) (positive_select s 78) (lex_12_78_image s)

theorem lex_12_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.pos 4848)] :=
  (lex_12_78_gate s).prop _ (List.Mem.head _)

theorem lex_12_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.neg 78), (Sat.Literal.pos 147)] :=
  (lex_12_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.pos 78), (Sat.Literal.neg 147)] :=
  (lex_12_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.neg 78), (Sat.Literal.neg 147), (Sat.Literal.pos 4849)] :=
  (lex_12_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4848), (Sat.Literal.pos 78), (Sat.Literal.pos 147), (Sat.Literal.pos 4849)] :=
  (lex_12_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4849) = lexBefore s permutation12 77 := by
  exact (positive_lex_of_descriptor s 4849 permutation12 78 (by rfl)).trans ((lex_skipped s permutation12 77 78 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation12 77) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation12 77 by rw [image12_eq]; rfl))

theorem lex_12_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4850) (Sat.Literal.pos 4849) (Sat.Literal.pos 77) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation12 77 (assignment s)
    (Sat.Literal.pos 4850) (Sat.Literal.pos 4849) (Sat.Literal.pos 77) (Sat.Literal.pos 83) (positive_of_descriptor s 4850 (.lex permutation12 77) (by rfl)) (lex_12_77_prefix s) (positive_select s 77) (lex_12_77_image s)

theorem lex_12_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.pos 77), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation12 77 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4849) (Sat.Literal.pos 77) (Sat.Literal.pos 83) (lex_12_77_prefix s) (positive_select s 77) (lex_12_77_image s)

theorem lex_12_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.pos 4849)] :=
  (lex_12_77_gate s).prop _ (List.Mem.head _)

theorem lex_12_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.neg 77), (Sat.Literal.pos 83)] :=
  (lex_12_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.pos 77), (Sat.Literal.neg 83)] :=
  (lex_12_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.neg 77), (Sat.Literal.neg 83), (Sat.Literal.pos 4850)] :=
  (lex_12_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4849), (Sat.Literal.pos 77), (Sat.Literal.pos 83), (Sat.Literal.pos 4850)] :=
  (lex_12_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4850) = lexBefore s permutation12 76 := by
  exact (positive_lex_of_descriptor s 4850 permutation12 77 (by rfl)).trans ((lex_skipped s permutation12 76 77 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation12 76) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation12 76 by rw [image12_eq]; rfl))

theorem lex_12_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4851) (Sat.Literal.pos 4850) (Sat.Literal.pos 76) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation12 76 (assignment s)
    (Sat.Literal.pos 4851) (Sat.Literal.pos 4850) (Sat.Literal.pos 76) (Sat.Literal.pos 19) (positive_of_descriptor s 4851 (.lex permutation12 76) (by rfl)) (lex_12_76_prefix s) (positive_select s 76) (lex_12_76_image s)

theorem lex_12_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.pos 76), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation12 76 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4850) (Sat.Literal.pos 76) (Sat.Literal.pos 19) (lex_12_76_prefix s) (positive_select s 76) (lex_12_76_image s)

theorem lex_12_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.pos 4850)] :=
  (lex_12_76_gate s).prop _ (List.Mem.head _)

theorem lex_12_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.neg 76), (Sat.Literal.pos 19)] :=
  (lex_12_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.pos 76), (Sat.Literal.neg 19)] :=
  (lex_12_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.neg 76), (Sat.Literal.neg 19), (Sat.Literal.pos 4851)] :=
  (lex_12_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4850), (Sat.Literal.pos 76), (Sat.Literal.pos 19), (Sat.Literal.pos 4851)] :=
  (lex_12_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4851) = lexBefore s permutation12 75 := by
  exact (positive_lex_of_descriptor s 4851 permutation12 76 (by rfl)).trans ((lex_skipped s permutation12 75 76 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation12 75) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation12 75 by rw [image12_eq]; rfl))

theorem lex_12_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4852) (Sat.Literal.pos 4851) (Sat.Literal.pos 75) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation12 75 (assignment s)
    (Sat.Literal.pos 4852) (Sat.Literal.pos 4851) (Sat.Literal.pos 75) (Sat.Literal.pos 210) (positive_of_descriptor s 4852 (.lex permutation12 75) (by rfl)) (lex_12_75_prefix s) (positive_select s 75) (lex_12_75_image s)

theorem lex_12_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.pos 75), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation12 75 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4851) (Sat.Literal.pos 75) (Sat.Literal.pos 210) (lex_12_75_prefix s) (positive_select s 75) (lex_12_75_image s)

theorem lex_12_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.pos 4851)] :=
  (lex_12_75_gate s).prop _ (List.Mem.head _)

theorem lex_12_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.neg 75), (Sat.Literal.pos 210)] :=
  (lex_12_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.pos 75), (Sat.Literal.neg 210)] :=
  (lex_12_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.neg 75), (Sat.Literal.neg 210), (Sat.Literal.pos 4852)] :=
  (lex_12_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4851), (Sat.Literal.pos 75), (Sat.Literal.pos 210), (Sat.Literal.pos 4852)] :=
  (lex_12_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4852) = lexBefore s permutation12 74 := by
  exact (positive_lex_of_descriptor s 4852 permutation12 75 (by rfl)).trans ((lex_skipped s permutation12 74 75 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation12 74) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation12 74 by rw [image12_eq]; rfl))

theorem lex_12_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4853) (Sat.Literal.pos 4852) (Sat.Literal.pos 74) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation12 74 (assignment s)
    (Sat.Literal.pos 4853) (Sat.Literal.pos 4852) (Sat.Literal.pos 74) (Sat.Literal.pos 146) (positive_of_descriptor s 4853 (.lex permutation12 74) (by rfl)) (lex_12_74_prefix s) (positive_select s 74) (lex_12_74_image s)

theorem lex_12_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.pos 74), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation12 74 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4852) (Sat.Literal.pos 74) (Sat.Literal.pos 146) (lex_12_74_prefix s) (positive_select s 74) (lex_12_74_image s)

theorem lex_12_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.pos 4852)] :=
  (lex_12_74_gate s).prop _ (List.Mem.head _)

theorem lex_12_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.neg 74), (Sat.Literal.pos 146)] :=
  (lex_12_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.pos 74), (Sat.Literal.neg 146)] :=
  (lex_12_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.neg 74), (Sat.Literal.neg 146), (Sat.Literal.pos 4853)] :=
  (lex_12_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4852), (Sat.Literal.pos 74), (Sat.Literal.pos 146), (Sat.Literal.pos 4853)] :=
  (lex_12_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4853) = lexBefore s permutation12 73 := by
  exact (positive_lex_of_descriptor s 4853 permutation12 74 (by rfl)).trans ((lex_skipped s permutation12 73 74 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation12 73) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation12 73 by rw [image12_eq]; rfl))

theorem lex_12_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4854) (Sat.Literal.pos 4853) (Sat.Literal.pos 73) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation12 73 (assignment s)
    (Sat.Literal.pos 4854) (Sat.Literal.pos 4853) (Sat.Literal.pos 73) (Sat.Literal.pos 82) (positive_of_descriptor s 4854 (.lex permutation12 73) (by rfl)) (lex_12_73_prefix s) (positive_select s 73) (lex_12_73_image s)

theorem lex_12_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.pos 73), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation12 73 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4853) (Sat.Literal.pos 73) (Sat.Literal.pos 82) (lex_12_73_prefix s) (positive_select s 73) (lex_12_73_image s)

theorem lex_12_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.pos 4853)] :=
  (lex_12_73_gate s).prop _ (List.Mem.head _)

theorem lex_12_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.neg 73), (Sat.Literal.pos 82)] :=
  (lex_12_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.pos 73), (Sat.Literal.neg 82)] :=
  (lex_12_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.neg 73), (Sat.Literal.neg 82), (Sat.Literal.pos 4854)] :=
  (lex_12_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4853), (Sat.Literal.pos 73), (Sat.Literal.pos 82), (Sat.Literal.pos 4854)] :=
  (lex_12_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4854) = lexBefore s permutation12 72 := by
  exact (positive_lex_of_descriptor s 4854 permutation12 73 (by rfl)).trans ((lex_skipped s permutation12 72 73 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation12 72) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation12 72 by rw [image12_eq]; rfl))

theorem lex_12_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4855) (Sat.Literal.pos 4854) (Sat.Literal.pos 72) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation12 72 (assignment s)
    (Sat.Literal.pos 4855) (Sat.Literal.pos 4854) (Sat.Literal.pos 72) (Sat.Literal.pos 18) (positive_of_descriptor s 4855 (.lex permutation12 72) (by rfl)) (lex_12_72_prefix s) (positive_select s 72) (lex_12_72_image s)

theorem lex_12_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.pos 72), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation12 72 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4854) (Sat.Literal.pos 72) (Sat.Literal.pos 18) (lex_12_72_prefix s) (positive_select s 72) (lex_12_72_image s)

theorem lex_12_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.pos 4854)] :=
  (lex_12_72_gate s).prop _ (List.Mem.head _)

theorem lex_12_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.neg 72), (Sat.Literal.pos 18)] :=
  (lex_12_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.pos 72), (Sat.Literal.neg 18)] :=
  (lex_12_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.neg 72), (Sat.Literal.neg 18), (Sat.Literal.pos 4855)] :=
  (lex_12_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4854), (Sat.Literal.pos 72), (Sat.Literal.pos 18), (Sat.Literal.pos 4855)] :=
  (lex_12_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4855) = lexBefore s permutation12 71 := by
  exact (positive_lex_of_descriptor s 4855 permutation12 72 (by rfl)).trans ((lex_skipped s permutation12 71 72 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation12 71) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation12 71 by rw [image12_eq]; rfl))

theorem lex_12_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4856) (Sat.Literal.pos 4855) (Sat.Literal.pos 71) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation12 71 (assignment s)
    (Sat.Literal.pos 4856) (Sat.Literal.pos 4855) (Sat.Literal.pos 71) (Sat.Literal.pos 209) (positive_of_descriptor s 4856 (.lex permutation12 71) (by rfl)) (lex_12_71_prefix s) (positive_select s 71) (lex_12_71_image s)

theorem lex_12_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.pos 71), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation12 71 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4855) (Sat.Literal.pos 71) (Sat.Literal.pos 209) (lex_12_71_prefix s) (positive_select s 71) (lex_12_71_image s)

theorem lex_12_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.pos 4855)] :=
  (lex_12_71_gate s).prop _ (List.Mem.head _)

theorem lex_12_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.neg 71), (Sat.Literal.pos 209)] :=
  (lex_12_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.pos 71), (Sat.Literal.neg 209)] :=
  (lex_12_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.neg 71), (Sat.Literal.neg 209), (Sat.Literal.pos 4856)] :=
  (lex_12_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4855), (Sat.Literal.pos 71), (Sat.Literal.pos 209), (Sat.Literal.pos 4856)] :=
  (lex_12_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4856) = lexBefore s permutation12 70 := by
  exact (positive_lex_of_descriptor s 4856 permutation12 71 (by rfl)).trans ((lex_skipped s permutation12 70 71 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation12 70) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation12 70 by rw [image12_eq]; rfl))

theorem lex_12_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4857) (Sat.Literal.pos 4856) (Sat.Literal.pos 70) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation12 70 (assignment s)
    (Sat.Literal.pos 4857) (Sat.Literal.pos 4856) (Sat.Literal.pos 70) (Sat.Literal.pos 145) (positive_of_descriptor s 4857 (.lex permutation12 70) (by rfl)) (lex_12_70_prefix s) (positive_select s 70) (lex_12_70_image s)

theorem lex_12_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.pos 70), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation12 70 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4856) (Sat.Literal.pos 70) (Sat.Literal.pos 145) (lex_12_70_prefix s) (positive_select s 70) (lex_12_70_image s)

theorem lex_12_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.pos 4856)] :=
  (lex_12_70_gate s).prop _ (List.Mem.head _)

theorem lex_12_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.neg 70), (Sat.Literal.pos 145)] :=
  (lex_12_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.pos 70), (Sat.Literal.neg 145)] :=
  (lex_12_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.neg 70), (Sat.Literal.neg 145), (Sat.Literal.pos 4857)] :=
  (lex_12_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4856), (Sat.Literal.pos 70), (Sat.Literal.pos 145), (Sat.Literal.pos 4857)] :=
  (lex_12_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4857) = lexBefore s permutation12 69 := by
  exact (positive_lex_of_descriptor s 4857 permutation12 70 (by rfl)).trans ((lex_skipped s permutation12 69 70 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation12 69) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation12 69 by rw [image12_eq]; rfl))

theorem lex_12_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4858) (Sat.Literal.pos 4857) (Sat.Literal.pos 69) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation12 69 (assignment s)
    (Sat.Literal.pos 4858) (Sat.Literal.pos 4857) (Sat.Literal.pos 69) (Sat.Literal.pos 81) (positive_of_descriptor s 4858 (.lex permutation12 69) (by rfl)) (lex_12_69_prefix s) (positive_select s 69) (lex_12_69_image s)

theorem lex_12_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.pos 69), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation12 69 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4857) (Sat.Literal.pos 69) (Sat.Literal.pos 81) (lex_12_69_prefix s) (positive_select s 69) (lex_12_69_image s)

theorem lex_12_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.pos 4857)] :=
  (lex_12_69_gate s).prop _ (List.Mem.head _)

theorem lex_12_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.neg 69), (Sat.Literal.pos 81)] :=
  (lex_12_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.pos 69), (Sat.Literal.neg 81)] :=
  (lex_12_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.neg 69), (Sat.Literal.neg 81), (Sat.Literal.pos 4858)] :=
  (lex_12_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4857), (Sat.Literal.pos 69), (Sat.Literal.pos 81), (Sat.Literal.pos 4858)] :=
  (lex_12_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4858) = lexBefore s permutation12 68 := by
  exact (positive_lex_of_descriptor s 4858 permutation12 69 (by rfl)).trans ((lex_skipped s permutation12 68 69 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation12 68) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation12 68 by rw [image12_eq]; rfl))

theorem lex_12_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4859) (Sat.Literal.pos 4858) (Sat.Literal.pos 68) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation12 68 (assignment s)
    (Sat.Literal.pos 4859) (Sat.Literal.pos 4858) (Sat.Literal.pos 68) (Sat.Literal.pos 17) (positive_of_descriptor s 4859 (.lex permutation12 68) (by rfl)) (lex_12_68_prefix s) (positive_select s 68) (lex_12_68_image s)

theorem lex_12_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.pos 68), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation12 68 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4858) (Sat.Literal.pos 68) (Sat.Literal.pos 17) (lex_12_68_prefix s) (positive_select s 68) (lex_12_68_image s)

theorem lex_12_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.pos 4858)] :=
  (lex_12_68_gate s).prop _ (List.Mem.head _)

theorem lex_12_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.neg 68), (Sat.Literal.pos 17)] :=
  (lex_12_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.pos 68), (Sat.Literal.neg 17)] :=
  (lex_12_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.neg 68), (Sat.Literal.neg 17), (Sat.Literal.pos 4859)] :=
  (lex_12_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4858), (Sat.Literal.pos 68), (Sat.Literal.pos 17), (Sat.Literal.pos 4859)] :=
  (lex_12_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4859) = lexBefore s permutation12 67 := by
  exact (positive_lex_of_descriptor s 4859 permutation12 68 (by rfl)).trans ((lex_skipped s permutation12 67 68 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation12 67) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation12 67 by rw [image12_eq]; rfl))

theorem lex_12_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4860) (Sat.Literal.pos 4859) (Sat.Literal.pos 67) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation12 67 (assignment s)
    (Sat.Literal.pos 4860) (Sat.Literal.pos 4859) (Sat.Literal.pos 67) (Sat.Literal.pos 208) (positive_of_descriptor s 4860 (.lex permutation12 67) (by rfl)) (lex_12_67_prefix s) (positive_select s 67) (lex_12_67_image s)

theorem lex_12_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.pos 67), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation12 67 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4859) (Sat.Literal.pos 67) (Sat.Literal.pos 208) (lex_12_67_prefix s) (positive_select s 67) (lex_12_67_image s)

theorem lex_12_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.pos 4859)] :=
  (lex_12_67_gate s).prop _ (List.Mem.head _)

theorem lex_12_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.neg 67), (Sat.Literal.pos 208)] :=
  (lex_12_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.pos 67), (Sat.Literal.neg 208)] :=
  (lex_12_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.neg 67), (Sat.Literal.neg 208), (Sat.Literal.pos 4860)] :=
  (lex_12_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4859), (Sat.Literal.pos 67), (Sat.Literal.pos 208), (Sat.Literal.pos 4860)] :=
  (lex_12_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4860) = lexBefore s permutation12 66 := by
  exact (positive_lex_of_descriptor s 4860 permutation12 67 (by rfl)).trans ((lex_skipped s permutation12 66 67 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation12 66) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation12 66 by rw [image12_eq]; rfl))

theorem lex_12_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4861) (Sat.Literal.pos 4860) (Sat.Literal.pos 66) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation12 66 (assignment s)
    (Sat.Literal.pos 4861) (Sat.Literal.pos 4860) (Sat.Literal.pos 66) (Sat.Literal.pos 144) (positive_of_descriptor s 4861 (.lex permutation12 66) (by rfl)) (lex_12_66_prefix s) (positive_select s 66) (lex_12_66_image s)

theorem lex_12_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.pos 66), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation12 66 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4860) (Sat.Literal.pos 66) (Sat.Literal.pos 144) (lex_12_66_prefix s) (positive_select s 66) (lex_12_66_image s)

theorem lex_12_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.pos 4860)] :=
  (lex_12_66_gate s).prop _ (List.Mem.head _)

theorem lex_12_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.neg 66), (Sat.Literal.pos 144)] :=
  (lex_12_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.pos 66), (Sat.Literal.neg 144)] :=
  (lex_12_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.neg 66), (Sat.Literal.neg 144), (Sat.Literal.pos 4861)] :=
  (lex_12_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4860), (Sat.Literal.pos 66), (Sat.Literal.pos 144), (Sat.Literal.pos 4861)] :=
  (lex_12_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4861) = lexBefore s permutation12 65 := by
  exact (positive_lex_of_descriptor s 4861 permutation12 66 (by rfl)).trans ((lex_skipped s permutation12 65 66 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation12 65) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation12 65 by rw [image12_eq]; rfl))

theorem lex_12_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4862) (Sat.Literal.pos 4861) (Sat.Literal.pos 65) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation12 65 (assignment s)
    (Sat.Literal.pos 4862) (Sat.Literal.pos 4861) (Sat.Literal.pos 65) (Sat.Literal.pos 80) (positive_of_descriptor s 4862 (.lex permutation12 65) (by rfl)) (lex_12_65_prefix s) (positive_select s 65) (lex_12_65_image s)

theorem lex_12_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.pos 65), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation12 65 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4861) (Sat.Literal.pos 65) (Sat.Literal.pos 80) (lex_12_65_prefix s) (positive_select s 65) (lex_12_65_image s)

theorem lex_12_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.pos 4861)] :=
  (lex_12_65_gate s).prop _ (List.Mem.head _)

theorem lex_12_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.neg 65), (Sat.Literal.pos 80)] :=
  (lex_12_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.pos 65), (Sat.Literal.neg 80)] :=
  (lex_12_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.neg 65), (Sat.Literal.neg 80), (Sat.Literal.pos 4862)] :=
  (lex_12_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4861), (Sat.Literal.pos 65), (Sat.Literal.pos 80), (Sat.Literal.pos 4862)] :=
  (lex_12_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4862) = lexBefore s permutation12 64 := by
  exact (positive_lex_of_descriptor s 4862 permutation12 65 (by rfl)).trans ((lex_skipped s permutation12 64 65 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation12 64) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation12 64 by rw [image12_eq]; rfl))

theorem lex_12_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4863) (Sat.Literal.pos 4862) (Sat.Literal.pos 64) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation12 64 (assignment s)
    (Sat.Literal.pos 4863) (Sat.Literal.pos 4862) (Sat.Literal.pos 64) (Sat.Literal.pos 16) (positive_of_descriptor s 4863 (.lex permutation12 64) (by rfl)) (lex_12_64_prefix s) (positive_select s 64) (lex_12_64_image s)

theorem lex_12_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.pos 64), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation12 64 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4862) (Sat.Literal.pos 64) (Sat.Literal.pos 16) (lex_12_64_prefix s) (positive_select s 64) (lex_12_64_image s)

theorem lex_12_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.pos 4862)] :=
  (lex_12_64_gate s).prop _ (List.Mem.head _)

theorem lex_12_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.neg 64), (Sat.Literal.pos 16)] :=
  (lex_12_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.pos 64), (Sat.Literal.neg 16)] :=
  (lex_12_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.neg 64), (Sat.Literal.neg 16), (Sat.Literal.pos 4863)] :=
  (lex_12_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4862), (Sat.Literal.pos 64), (Sat.Literal.pos 16), (Sat.Literal.pos 4863)] :=
  (lex_12_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4863) = lexBefore s permutation12 63 := by
  exact (positive_lex_of_descriptor s 4863 permutation12 64 (by rfl)).trans ((lex_skipped s permutation12 63 64 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation12 63) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation12 63 by rw [image12_eq]; rfl))

theorem lex_12_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4864) (Sat.Literal.pos 4863) (Sat.Literal.pos 63) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation12 63 (assignment s)
    (Sat.Literal.pos 4864) (Sat.Literal.pos 4863) (Sat.Literal.pos 63) (Sat.Literal.pos 207) (positive_of_descriptor s 4864 (.lex permutation12 63) (by rfl)) (lex_12_63_prefix s) (positive_select s 63) (lex_12_63_image s)

theorem lex_12_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.pos 63), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation12 63 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4863) (Sat.Literal.pos 63) (Sat.Literal.pos 207) (lex_12_63_prefix s) (positive_select s 63) (lex_12_63_image s)

theorem lex_12_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.pos 4863)] :=
  (lex_12_63_gate s).prop _ (List.Mem.head _)

theorem lex_12_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.neg 63), (Sat.Literal.pos 207)] :=
  (lex_12_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.pos 63), (Sat.Literal.neg 207)] :=
  (lex_12_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.neg 63), (Sat.Literal.neg 207), (Sat.Literal.pos 4864)] :=
  (lex_12_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4863), (Sat.Literal.pos 63), (Sat.Literal.pos 207), (Sat.Literal.pos 4864)] :=
  (lex_12_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4864) = lexBefore s permutation12 62 := by
  exact (positive_lex_of_descriptor s 4864 permutation12 63 (by rfl)).trans ((lex_skipped s permutation12 62 63 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation12 62) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation12 62 by rw [image12_eq]; rfl))

theorem lex_12_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4865) (Sat.Literal.pos 4864) (Sat.Literal.pos 62) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation12 62 (assignment s)
    (Sat.Literal.pos 4865) (Sat.Literal.pos 4864) (Sat.Literal.pos 62) (Sat.Literal.pos 143) (positive_of_descriptor s 4865 (.lex permutation12 62) (by rfl)) (lex_12_62_prefix s) (positive_select s 62) (lex_12_62_image s)

theorem lex_12_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.pos 62), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation12 62 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4864) (Sat.Literal.pos 62) (Sat.Literal.pos 143) (lex_12_62_prefix s) (positive_select s 62) (lex_12_62_image s)

theorem lex_12_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.pos 4864)] :=
  (lex_12_62_gate s).prop _ (List.Mem.head _)

theorem lex_12_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.neg 62), (Sat.Literal.pos 143)] :=
  (lex_12_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.pos 62), (Sat.Literal.neg 143)] :=
  (lex_12_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.neg 62), (Sat.Literal.neg 143), (Sat.Literal.pos 4865)] :=
  (lex_12_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4864), (Sat.Literal.pos 62), (Sat.Literal.pos 143), (Sat.Literal.pos 4865)] :=
  (lex_12_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4865) = lexBefore s permutation12 61 := by
  exact (positive_lex_of_descriptor s 4865 permutation12 62 (by rfl)).trans ((lex_skipped s permutation12 61 62 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation12 61) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation12 61 by rw [image12_eq]; rfl))

theorem lex_12_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4866) (Sat.Literal.pos 4865) (Sat.Literal.pos 61) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation12 61 (assignment s)
    (Sat.Literal.pos 4866) (Sat.Literal.pos 4865) (Sat.Literal.pos 61) (Sat.Literal.pos 79) (positive_of_descriptor s 4866 (.lex permutation12 61) (by rfl)) (lex_12_61_prefix s) (positive_select s 61) (lex_12_61_image s)

theorem lex_12_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.pos 61), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation12 61 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4865) (Sat.Literal.pos 61) (Sat.Literal.pos 79) (lex_12_61_prefix s) (positive_select s 61) (lex_12_61_image s)

theorem lex_12_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.pos 4865)] :=
  (lex_12_61_gate s).prop _ (List.Mem.head _)

theorem lex_12_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.neg 61), (Sat.Literal.pos 79)] :=
  (lex_12_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.pos 61), (Sat.Literal.neg 79)] :=
  (lex_12_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.neg 61), (Sat.Literal.neg 79), (Sat.Literal.pos 4866)] :=
  (lex_12_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4865), (Sat.Literal.pos 61), (Sat.Literal.pos 79), (Sat.Literal.pos 4866)] :=
  (lex_12_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4866) = lexBefore s permutation12 60 := by
  exact (positive_lex_of_descriptor s 4866 permutation12 61 (by rfl)).trans ((lex_skipped s permutation12 60 61 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation12 60) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation12 60 by rw [image12_eq]; rfl))

theorem lex_12_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4867) (Sat.Literal.pos 4866) (Sat.Literal.pos 60) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation12 60 (assignment s)
    (Sat.Literal.pos 4867) (Sat.Literal.pos 4866) (Sat.Literal.pos 60) (Sat.Literal.pos 15) (positive_of_descriptor s 4867 (.lex permutation12 60) (by rfl)) (lex_12_60_prefix s) (positive_select s 60) (lex_12_60_image s)

theorem lex_12_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.pos 60), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation12 60 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4866) (Sat.Literal.pos 60) (Sat.Literal.pos 15) (lex_12_60_prefix s) (positive_select s 60) (lex_12_60_image s)

theorem lex_12_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.pos 4866)] :=
  (lex_12_60_gate s).prop _ (List.Mem.head _)

theorem lex_12_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.neg 60), (Sat.Literal.pos 15)] :=
  (lex_12_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.pos 60), (Sat.Literal.neg 15)] :=
  (lex_12_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.neg 60), (Sat.Literal.neg 15), (Sat.Literal.pos 4867)] :=
  (lex_12_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4866), (Sat.Literal.pos 60), (Sat.Literal.pos 15), (Sat.Literal.pos 4867)] :=
  (lex_12_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4867) = lexBefore s permutation12 59 := by
  exact (positive_lex_of_descriptor s 4867 permutation12 60 (by rfl)).trans ((lex_skipped s permutation12 59 60 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation12 59) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation12 59 by rw [image12_eq]; rfl))

theorem lex_12_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4868) (Sat.Literal.pos 4867) (Sat.Literal.pos 59) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation12 59 (assignment s)
    (Sat.Literal.pos 4868) (Sat.Literal.pos 4867) (Sat.Literal.pos 59) (Sat.Literal.pos 206) (positive_of_descriptor s 4868 (.lex permutation12 59) (by rfl)) (lex_12_59_prefix s) (positive_select s 59) (lex_12_59_image s)

theorem lex_12_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.pos 59), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation12 59 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4867) (Sat.Literal.pos 59) (Sat.Literal.pos 206) (lex_12_59_prefix s) (positive_select s 59) (lex_12_59_image s)

theorem lex_12_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.pos 4867)] :=
  (lex_12_59_gate s).prop _ (List.Mem.head _)

theorem lex_12_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.neg 59), (Sat.Literal.pos 206)] :=
  (lex_12_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.pos 59), (Sat.Literal.neg 206)] :=
  (lex_12_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.neg 59), (Sat.Literal.neg 206), (Sat.Literal.pos 4868)] :=
  (lex_12_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4867), (Sat.Literal.pos 59), (Sat.Literal.pos 206), (Sat.Literal.pos 4868)] :=
  (lex_12_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4868) = lexBefore s permutation12 58 := by
  exact (positive_lex_of_descriptor s 4868 permutation12 59 (by rfl)).trans ((lex_skipped s permutation12 58 59 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation12 58) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation12 58 by rw [image12_eq]; rfl))

theorem lex_12_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4869) (Sat.Literal.pos 4868) (Sat.Literal.pos 58) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation12 58 (assignment s)
    (Sat.Literal.pos 4869) (Sat.Literal.pos 4868) (Sat.Literal.pos 58) (Sat.Literal.pos 142) (positive_of_descriptor s 4869 (.lex permutation12 58) (by rfl)) (lex_12_58_prefix s) (positive_select s 58) (lex_12_58_image s)

theorem lex_12_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.pos 58), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation12 58 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4868) (Sat.Literal.pos 58) (Sat.Literal.pos 142) (lex_12_58_prefix s) (positive_select s 58) (lex_12_58_image s)

theorem lex_12_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.pos 4868)] :=
  (lex_12_58_gate s).prop _ (List.Mem.head _)

theorem lex_12_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.neg 58), (Sat.Literal.pos 142)] :=
  (lex_12_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.pos 58), (Sat.Literal.neg 142)] :=
  (lex_12_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.neg 58), (Sat.Literal.neg 142), (Sat.Literal.pos 4869)] :=
  (lex_12_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4868), (Sat.Literal.pos 58), (Sat.Literal.pos 142), (Sat.Literal.pos 4869)] :=
  (lex_12_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4869) = lexBefore s permutation12 57 := by
  exact (positive_lex_of_descriptor s 4869 permutation12 58 (by rfl)).trans ((lex_skipped s permutation12 57 58 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation12 57) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation12 57 by rw [image12_eq]; rfl))

theorem lex_12_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4870) (Sat.Literal.pos 4869) (Sat.Literal.pos 57) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation12 57 (assignment s)
    (Sat.Literal.pos 4870) (Sat.Literal.pos 4869) (Sat.Literal.pos 57) (Sat.Literal.pos 78) (positive_of_descriptor s 4870 (.lex permutation12 57) (by rfl)) (lex_12_57_prefix s) (positive_select s 57) (lex_12_57_image s)

theorem lex_12_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.pos 57), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation12 57 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4869) (Sat.Literal.pos 57) (Sat.Literal.pos 78) (lex_12_57_prefix s) (positive_select s 57) (lex_12_57_image s)

theorem lex_12_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.pos 4869)] :=
  (lex_12_57_gate s).prop _ (List.Mem.head _)

theorem lex_12_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.neg 57), (Sat.Literal.pos 78)] :=
  (lex_12_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.pos 57), (Sat.Literal.neg 78)] :=
  (lex_12_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.neg 57), (Sat.Literal.neg 78), (Sat.Literal.pos 4870)] :=
  (lex_12_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4869), (Sat.Literal.pos 57), (Sat.Literal.pos 78), (Sat.Literal.pos 4870)] :=
  (lex_12_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4870) = lexBefore s permutation12 56 := by
  exact (positive_lex_of_descriptor s 4870 permutation12 57 (by rfl)).trans ((lex_skipped s permutation12 56 57 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation12 56) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation12 56 by rw [image12_eq]; rfl))

theorem lex_12_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4871) (Sat.Literal.pos 4870) (Sat.Literal.pos 56) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation12 56 (assignment s)
    (Sat.Literal.pos 4871) (Sat.Literal.pos 4870) (Sat.Literal.pos 56) (Sat.Literal.pos 14) (positive_of_descriptor s 4871 (.lex permutation12 56) (by rfl)) (lex_12_56_prefix s) (positive_select s 56) (lex_12_56_image s)

theorem lex_12_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.pos 56), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation12 56 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4870) (Sat.Literal.pos 56) (Sat.Literal.pos 14) (lex_12_56_prefix s) (positive_select s 56) (lex_12_56_image s)

theorem lex_12_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.pos 4870)] :=
  (lex_12_56_gate s).prop _ (List.Mem.head _)

theorem lex_12_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.neg 56), (Sat.Literal.pos 14)] :=
  (lex_12_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.pos 56), (Sat.Literal.neg 14)] :=
  (lex_12_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.neg 56), (Sat.Literal.neg 14), (Sat.Literal.pos 4871)] :=
  (lex_12_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4870), (Sat.Literal.pos 56), (Sat.Literal.pos 14), (Sat.Literal.pos 4871)] :=
  (lex_12_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4871) = lexBefore s permutation12 55 := by
  exact (positive_lex_of_descriptor s 4871 permutation12 56 (by rfl)).trans ((lex_skipped s permutation12 55 56 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation12 55) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation12 55 by rw [image12_eq]; rfl))

theorem lex_12_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4872) (Sat.Literal.pos 4871) (Sat.Literal.pos 55) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation12 55 (assignment s)
    (Sat.Literal.pos 4872) (Sat.Literal.pos 4871) (Sat.Literal.pos 55) (Sat.Literal.pos 205) (positive_of_descriptor s 4872 (.lex permutation12 55) (by rfl)) (lex_12_55_prefix s) (positive_select s 55) (lex_12_55_image s)

theorem lex_12_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.pos 55), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation12 55 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4871) (Sat.Literal.pos 55) (Sat.Literal.pos 205) (lex_12_55_prefix s) (positive_select s 55) (lex_12_55_image s)

theorem lex_12_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.pos 4871)] :=
  (lex_12_55_gate s).prop _ (List.Mem.head _)

theorem lex_12_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.neg 55), (Sat.Literal.pos 205)] :=
  (lex_12_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.pos 55), (Sat.Literal.neg 205)] :=
  (lex_12_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.neg 55), (Sat.Literal.neg 205), (Sat.Literal.pos 4872)] :=
  (lex_12_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4871), (Sat.Literal.pos 55), (Sat.Literal.pos 205), (Sat.Literal.pos 4872)] :=
  (lex_12_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4872) = lexBefore s permutation12 54 := by
  exact (positive_lex_of_descriptor s 4872 permutation12 55 (by rfl)).trans ((lex_skipped s permutation12 54 55 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation12 54) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation12 54 by rw [image12_eq]; rfl))

theorem lex_12_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4873) (Sat.Literal.pos 4872) (Sat.Literal.pos 54) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation12 54 (assignment s)
    (Sat.Literal.pos 4873) (Sat.Literal.pos 4872) (Sat.Literal.pos 54) (Sat.Literal.pos 141) (positive_of_descriptor s 4873 (.lex permutation12 54) (by rfl)) (lex_12_54_prefix s) (positive_select s 54) (lex_12_54_image s)

theorem lex_12_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.pos 54), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation12 54 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4872) (Sat.Literal.pos 54) (Sat.Literal.pos 141) (lex_12_54_prefix s) (positive_select s 54) (lex_12_54_image s)

theorem lex_12_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.pos 4872)] :=
  (lex_12_54_gate s).prop _ (List.Mem.head _)

theorem lex_12_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.neg 54), (Sat.Literal.pos 141)] :=
  (lex_12_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.pos 54), (Sat.Literal.neg 141)] :=
  (lex_12_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.neg 54), (Sat.Literal.neg 141), (Sat.Literal.pos 4873)] :=
  (lex_12_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4872), (Sat.Literal.pos 54), (Sat.Literal.pos 141), (Sat.Literal.pos 4873)] :=
  (lex_12_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4873) = lexBefore s permutation12 53 := by
  exact (positive_lex_of_descriptor s 4873 permutation12 54 (by rfl)).trans ((lex_skipped s permutation12 53 54 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation12 53) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation12 53 by rw [image12_eq]; rfl))

theorem lex_12_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4874) (Sat.Literal.pos 4873) (Sat.Literal.pos 53) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation12 53 (assignment s)
    (Sat.Literal.pos 4874) (Sat.Literal.pos 4873) (Sat.Literal.pos 53) (Sat.Literal.pos 77) (positive_of_descriptor s 4874 (.lex permutation12 53) (by rfl)) (lex_12_53_prefix s) (positive_select s 53) (lex_12_53_image s)

theorem lex_12_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.pos 53), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation12 53 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4873) (Sat.Literal.pos 53) (Sat.Literal.pos 77) (lex_12_53_prefix s) (positive_select s 53) (lex_12_53_image s)

theorem lex_12_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.pos 4873)] :=
  (lex_12_53_gate s).prop _ (List.Mem.head _)

theorem lex_12_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.neg 53), (Sat.Literal.pos 77)] :=
  (lex_12_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.pos 53), (Sat.Literal.neg 77)] :=
  (lex_12_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.neg 53), (Sat.Literal.neg 77), (Sat.Literal.pos 4874)] :=
  (lex_12_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4873), (Sat.Literal.pos 53), (Sat.Literal.pos 77), (Sat.Literal.pos 4874)] :=
  (lex_12_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4874) = lexBefore s permutation12 52 := by
  exact (positive_lex_of_descriptor s 4874 permutation12 53 (by rfl)).trans ((lex_skipped s permutation12 52 53 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation12 52) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation12 52 by rw [image12_eq]; rfl))

theorem lex_12_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4875) (Sat.Literal.pos 4874) (Sat.Literal.pos 52) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation12 52 (assignment s)
    (Sat.Literal.pos 4875) (Sat.Literal.pos 4874) (Sat.Literal.pos 52) (Sat.Literal.pos 13) (positive_of_descriptor s 4875 (.lex permutation12 52) (by rfl)) (lex_12_52_prefix s) (positive_select s 52) (lex_12_52_image s)

theorem lex_12_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.pos 52), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation12 52 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4874) (Sat.Literal.pos 52) (Sat.Literal.pos 13) (lex_12_52_prefix s) (positive_select s 52) (lex_12_52_image s)

theorem lex_12_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.pos 4874)] :=
  (lex_12_52_gate s).prop _ (List.Mem.head _)

theorem lex_12_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.neg 52), (Sat.Literal.pos 13)] :=
  (lex_12_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.pos 52), (Sat.Literal.neg 13)] :=
  (lex_12_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.neg 52), (Sat.Literal.neg 13), (Sat.Literal.pos 4875)] :=
  (lex_12_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4874), (Sat.Literal.pos 52), (Sat.Literal.pos 13), (Sat.Literal.pos 4875)] :=
  (lex_12_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4875) = lexBefore s permutation12 51 := by
  exact (positive_lex_of_descriptor s 4875 permutation12 52 (by rfl)).trans ((lex_skipped s permutation12 51 52 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation12 51) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation12 51 by rw [image12_eq]; rfl))

theorem lex_12_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4876) (Sat.Literal.pos 4875) (Sat.Literal.pos 51) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation12 51 (assignment s)
    (Sat.Literal.pos 4876) (Sat.Literal.pos 4875) (Sat.Literal.pos 51) (Sat.Literal.pos 204) (positive_of_descriptor s 4876 (.lex permutation12 51) (by rfl)) (lex_12_51_prefix s) (positive_select s 51) (lex_12_51_image s)

theorem lex_12_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.pos 51), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation12 51 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4875) (Sat.Literal.pos 51) (Sat.Literal.pos 204) (lex_12_51_prefix s) (positive_select s 51) (lex_12_51_image s)

theorem lex_12_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.pos 4875)] :=
  (lex_12_51_gate s).prop _ (List.Mem.head _)

theorem lex_12_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.neg 51), (Sat.Literal.pos 204)] :=
  (lex_12_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.pos 51), (Sat.Literal.neg 204)] :=
  (lex_12_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.neg 51), (Sat.Literal.neg 204), (Sat.Literal.pos 4876)] :=
  (lex_12_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4875), (Sat.Literal.pos 51), (Sat.Literal.pos 204), (Sat.Literal.pos 4876)] :=
  (lex_12_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4876) = lexBefore s permutation12 50 := by
  exact (positive_lex_of_descriptor s 4876 permutation12 51 (by rfl)).trans ((lex_skipped s permutation12 50 51 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation12 50) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation12 50 by rw [image12_eq]; rfl))

theorem lex_12_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4877) (Sat.Literal.pos 4876) (Sat.Literal.pos 50) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation12 50 (assignment s)
    (Sat.Literal.pos 4877) (Sat.Literal.pos 4876) (Sat.Literal.pos 50) (Sat.Literal.pos 140) (positive_of_descriptor s 4877 (.lex permutation12 50) (by rfl)) (lex_12_50_prefix s) (positive_select s 50) (lex_12_50_image s)

theorem lex_12_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.pos 50), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation12 50 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4876) (Sat.Literal.pos 50) (Sat.Literal.pos 140) (lex_12_50_prefix s) (positive_select s 50) (lex_12_50_image s)

theorem lex_12_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.pos 4876)] :=
  (lex_12_50_gate s).prop _ (List.Mem.head _)

theorem lex_12_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.neg 50), (Sat.Literal.pos 140)] :=
  (lex_12_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.pos 50), (Sat.Literal.neg 140)] :=
  (lex_12_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.neg 50), (Sat.Literal.neg 140), (Sat.Literal.pos 4877)] :=
  (lex_12_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4876), (Sat.Literal.pos 50), (Sat.Literal.pos 140), (Sat.Literal.pos 4877)] :=
  (lex_12_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4877) = lexBefore s permutation12 49 := by
  exact (positive_lex_of_descriptor s 4877 permutation12 50 (by rfl)).trans ((lex_skipped s permutation12 49 50 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation12 49) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation12 49 by rw [image12_eq]; rfl))

theorem lex_12_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4878) (Sat.Literal.pos 4877) (Sat.Literal.pos 49) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation12 49 (assignment s)
    (Sat.Literal.pos 4878) (Sat.Literal.pos 4877) (Sat.Literal.pos 49) (Sat.Literal.pos 76) (positive_of_descriptor s 4878 (.lex permutation12 49) (by rfl)) (lex_12_49_prefix s) (positive_select s 49) (lex_12_49_image s)

theorem lex_12_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.pos 49), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation12 49 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4877) (Sat.Literal.pos 49) (Sat.Literal.pos 76) (lex_12_49_prefix s) (positive_select s 49) (lex_12_49_image s)

theorem lex_12_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.pos 4877)] :=
  (lex_12_49_gate s).prop _ (List.Mem.head _)

theorem lex_12_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.neg 49), (Sat.Literal.pos 76)] :=
  (lex_12_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.pos 49), (Sat.Literal.neg 76)] :=
  (lex_12_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.neg 49), (Sat.Literal.neg 76), (Sat.Literal.pos 4878)] :=
  (lex_12_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4877), (Sat.Literal.pos 49), (Sat.Literal.pos 76), (Sat.Literal.pos 4878)] :=
  (lex_12_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4878) = lexBefore s permutation12 48 := by
  exact (positive_lex_of_descriptor s 4878 permutation12 49 (by rfl)).trans ((lex_skipped s permutation12 48 49 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation12 48) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation12 48 by rw [image12_eq]; rfl))

theorem lex_12_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4879) (Sat.Literal.pos 4878) (Sat.Literal.pos 48) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation12 48 (assignment s)
    (Sat.Literal.pos 4879) (Sat.Literal.pos 4878) (Sat.Literal.pos 48) (Sat.Literal.pos 12) (positive_of_descriptor s 4879 (.lex permutation12 48) (by rfl)) (lex_12_48_prefix s) (positive_select s 48) (lex_12_48_image s)

theorem lex_12_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.pos 48), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation12 48 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4878) (Sat.Literal.pos 48) (Sat.Literal.pos 12) (lex_12_48_prefix s) (positive_select s 48) (lex_12_48_image s)

theorem lex_12_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.pos 4878)] :=
  (lex_12_48_gate s).prop _ (List.Mem.head _)

theorem lex_12_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.neg 48), (Sat.Literal.pos 12)] :=
  (lex_12_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.pos 48), (Sat.Literal.neg 12)] :=
  (lex_12_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.neg 48), (Sat.Literal.neg 12), (Sat.Literal.pos 4879)] :=
  (lex_12_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4878), (Sat.Literal.pos 48), (Sat.Literal.pos 12), (Sat.Literal.pos 4879)] :=
  (lex_12_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4879) = lexBefore s permutation12 47 := by
  exact (positive_lex_of_descriptor s 4879 permutation12 48 (by rfl)).trans ((lex_skipped s permutation12 47 48 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation12 47) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation12 47 by rw [image12_eq]; rfl))

theorem lex_12_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4880) (Sat.Literal.pos 4879) (Sat.Literal.pos 47) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation12 47 (assignment s)
    (Sat.Literal.pos 4880) (Sat.Literal.pos 4879) (Sat.Literal.pos 47) (Sat.Literal.pos 203) (positive_of_descriptor s 4880 (.lex permutation12 47) (by rfl)) (lex_12_47_prefix s) (positive_select s 47) (lex_12_47_image s)

theorem lex_12_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.pos 47), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation12 47 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4879) (Sat.Literal.pos 47) (Sat.Literal.pos 203) (lex_12_47_prefix s) (positive_select s 47) (lex_12_47_image s)

theorem lex_12_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.pos 4879)] :=
  (lex_12_47_gate s).prop _ (List.Mem.head _)

theorem lex_12_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.neg 47), (Sat.Literal.pos 203)] :=
  (lex_12_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.pos 47), (Sat.Literal.neg 203)] :=
  (lex_12_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.neg 47), (Sat.Literal.neg 203), (Sat.Literal.pos 4880)] :=
  (lex_12_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4879), (Sat.Literal.pos 47), (Sat.Literal.pos 203), (Sat.Literal.pos 4880)] :=
  (lex_12_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4880) = lexBefore s permutation12 46 := by
  exact (positive_lex_of_descriptor s 4880 permutation12 47 (by rfl)).trans ((lex_skipped s permutation12 46 47 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation12 46) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation12 46 by rw [image12_eq]; rfl))

theorem lex_12_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4881) (Sat.Literal.pos 4880) (Sat.Literal.pos 46) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation12 46 (assignment s)
    (Sat.Literal.pos 4881) (Sat.Literal.pos 4880) (Sat.Literal.pos 46) (Sat.Literal.pos 139) (positive_of_descriptor s 4881 (.lex permutation12 46) (by rfl)) (lex_12_46_prefix s) (positive_select s 46) (lex_12_46_image s)

theorem lex_12_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.pos 46), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation12 46 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4880) (Sat.Literal.pos 46) (Sat.Literal.pos 139) (lex_12_46_prefix s) (positive_select s 46) (lex_12_46_image s)

theorem lex_12_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.pos 4880)] :=
  (lex_12_46_gate s).prop _ (List.Mem.head _)

theorem lex_12_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.neg 46), (Sat.Literal.pos 139)] :=
  (lex_12_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.pos 46), (Sat.Literal.neg 139)] :=
  (lex_12_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.neg 46), (Sat.Literal.neg 139), (Sat.Literal.pos 4881)] :=
  (lex_12_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4880), (Sat.Literal.pos 46), (Sat.Literal.pos 139), (Sat.Literal.pos 4881)] :=
  (lex_12_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4881) = lexBefore s permutation12 45 := by
  exact (positive_lex_of_descriptor s 4881 permutation12 46 (by rfl)).trans ((lex_skipped s permutation12 45 46 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation12 45) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation12 45 by rw [image12_eq]; rfl))

theorem lex_12_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4882) (Sat.Literal.pos 4881) (Sat.Literal.pos 45) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation12 45 (assignment s)
    (Sat.Literal.pos 4882) (Sat.Literal.pos 4881) (Sat.Literal.pos 45) (Sat.Literal.pos 75) (positive_of_descriptor s 4882 (.lex permutation12 45) (by rfl)) (lex_12_45_prefix s) (positive_select s 45) (lex_12_45_image s)

theorem lex_12_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.pos 45), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation12 45 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4881) (Sat.Literal.pos 45) (Sat.Literal.pos 75) (lex_12_45_prefix s) (positive_select s 45) (lex_12_45_image s)

theorem lex_12_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.pos 4881)] :=
  (lex_12_45_gate s).prop _ (List.Mem.head _)

theorem lex_12_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.neg 45), (Sat.Literal.pos 75)] :=
  (lex_12_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.pos 45), (Sat.Literal.neg 75)] :=
  (lex_12_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.neg 45), (Sat.Literal.neg 75), (Sat.Literal.pos 4882)] :=
  (lex_12_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4881), (Sat.Literal.pos 45), (Sat.Literal.pos 75), (Sat.Literal.pos 4882)] :=
  (lex_12_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4882) = lexBefore s permutation12 44 := by
  exact (positive_lex_of_descriptor s 4882 permutation12 45 (by rfl)).trans ((lex_skipped s permutation12 44 45 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation12 44) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation12 44 by rw [image12_eq]; rfl))

theorem lex_12_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4883) (Sat.Literal.pos 4882) (Sat.Literal.pos 44) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation12 44 (assignment s)
    (Sat.Literal.pos 4883) (Sat.Literal.pos 4882) (Sat.Literal.pos 44) (Sat.Literal.pos 11) (positive_of_descriptor s 4883 (.lex permutation12 44) (by rfl)) (lex_12_44_prefix s) (positive_select s 44) (lex_12_44_image s)

theorem lex_12_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.pos 44), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation12 44 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4882) (Sat.Literal.pos 44) (Sat.Literal.pos 11) (lex_12_44_prefix s) (positive_select s 44) (lex_12_44_image s)

theorem lex_12_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.pos 4882)] :=
  (lex_12_44_gate s).prop _ (List.Mem.head _)

theorem lex_12_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.neg 44), (Sat.Literal.pos 11)] :=
  (lex_12_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.pos 44), (Sat.Literal.neg 11)] :=
  (lex_12_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.neg 44), (Sat.Literal.neg 11), (Sat.Literal.pos 4883)] :=
  (lex_12_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4882), (Sat.Literal.pos 44), (Sat.Literal.pos 11), (Sat.Literal.pos 4883)] :=
  (lex_12_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4883) = lexBefore s permutation12 43 := by
  exact (positive_lex_of_descriptor s 4883 permutation12 44 (by rfl)).trans ((lex_skipped s permutation12 43 44 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation12 43) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation12 43 by rw [image12_eq]; rfl))

theorem lex_12_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4884) (Sat.Literal.pos 4883) (Sat.Literal.pos 43) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation12 43 (assignment s)
    (Sat.Literal.pos 4884) (Sat.Literal.pos 4883) (Sat.Literal.pos 43) (Sat.Literal.pos 202) (positive_of_descriptor s 4884 (.lex permutation12 43) (by rfl)) (lex_12_43_prefix s) (positive_select s 43) (lex_12_43_image s)

theorem lex_12_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.pos 43), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation12 43 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4883) (Sat.Literal.pos 43) (Sat.Literal.pos 202) (lex_12_43_prefix s) (positive_select s 43) (lex_12_43_image s)

theorem lex_12_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.pos 4883)] :=
  (lex_12_43_gate s).prop _ (List.Mem.head _)

theorem lex_12_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.neg 43), (Sat.Literal.pos 202)] :=
  (lex_12_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.pos 43), (Sat.Literal.neg 202)] :=
  (lex_12_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.neg 43), (Sat.Literal.neg 202), (Sat.Literal.pos 4884)] :=
  (lex_12_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4883), (Sat.Literal.pos 43), (Sat.Literal.pos 202), (Sat.Literal.pos 4884)] :=
  (lex_12_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4884) = lexBefore s permutation12 42 := by
  exact (positive_lex_of_descriptor s 4884 permutation12 43 (by rfl)).trans ((lex_skipped s permutation12 42 43 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation12 42) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation12 42 by rw [image12_eq]; rfl))

theorem lex_12_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4885) (Sat.Literal.pos 4884) (Sat.Literal.pos 42) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation12 42 (assignment s)
    (Sat.Literal.pos 4885) (Sat.Literal.pos 4884) (Sat.Literal.pos 42) (Sat.Literal.pos 138) (positive_of_descriptor s 4885 (.lex permutation12 42) (by rfl)) (lex_12_42_prefix s) (positive_select s 42) (lex_12_42_image s)

theorem lex_12_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.pos 42), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation12 42 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4884) (Sat.Literal.pos 42) (Sat.Literal.pos 138) (lex_12_42_prefix s) (positive_select s 42) (lex_12_42_image s)

theorem lex_12_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.pos 4884)] :=
  (lex_12_42_gate s).prop _ (List.Mem.head _)

theorem lex_12_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.neg 42), (Sat.Literal.pos 138)] :=
  (lex_12_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.pos 42), (Sat.Literal.neg 138)] :=
  (lex_12_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.neg 42), (Sat.Literal.neg 138), (Sat.Literal.pos 4885)] :=
  (lex_12_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4884), (Sat.Literal.pos 42), (Sat.Literal.pos 138), (Sat.Literal.pos 4885)] :=
  (lex_12_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4885) = lexBefore s permutation12 41 := by
  exact (positive_lex_of_descriptor s 4885 permutation12 42 (by rfl)).trans ((lex_skipped s permutation12 41 42 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation12 41) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation12 41 by rw [image12_eq]; rfl))

theorem lex_12_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4886) (Sat.Literal.pos 4885) (Sat.Literal.pos 41) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation12 41 (assignment s)
    (Sat.Literal.pos 4886) (Sat.Literal.pos 4885) (Sat.Literal.pos 41) (Sat.Literal.pos 74) (positive_of_descriptor s 4886 (.lex permutation12 41) (by rfl)) (lex_12_41_prefix s) (positive_select s 41) (lex_12_41_image s)

theorem lex_12_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.pos 41), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation12 41 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4885) (Sat.Literal.pos 41) (Sat.Literal.pos 74) (lex_12_41_prefix s) (positive_select s 41) (lex_12_41_image s)

theorem lex_12_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.pos 4885)] :=
  (lex_12_41_gate s).prop _ (List.Mem.head _)

theorem lex_12_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.neg 41), (Sat.Literal.pos 74)] :=
  (lex_12_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.pos 41), (Sat.Literal.neg 74)] :=
  (lex_12_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.neg 41), (Sat.Literal.neg 74), (Sat.Literal.pos 4886)] :=
  (lex_12_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4885), (Sat.Literal.pos 41), (Sat.Literal.pos 74), (Sat.Literal.pos 4886)] :=
  (lex_12_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4886) = lexBefore s permutation12 40 := by
  exact (positive_lex_of_descriptor s 4886 permutation12 41 (by rfl)).trans ((lex_skipped s permutation12 40 41 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation12 40) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation12 40 by rw [image12_eq]; rfl))

theorem lex_12_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4887) (Sat.Literal.pos 4886) (Sat.Literal.pos 40) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation12 40 (assignment s)
    (Sat.Literal.pos 4887) (Sat.Literal.pos 4886) (Sat.Literal.pos 40) (Sat.Literal.pos 10) (positive_of_descriptor s 4887 (.lex permutation12 40) (by rfl)) (lex_12_40_prefix s) (positive_select s 40) (lex_12_40_image s)

theorem lex_12_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.pos 40), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation12 40 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4886) (Sat.Literal.pos 40) (Sat.Literal.pos 10) (lex_12_40_prefix s) (positive_select s 40) (lex_12_40_image s)

theorem lex_12_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.pos 4886)] :=
  (lex_12_40_gate s).prop _ (List.Mem.head _)

theorem lex_12_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.neg 40), (Sat.Literal.pos 10)] :=
  (lex_12_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.pos 40), (Sat.Literal.neg 10)] :=
  (lex_12_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.neg 40), (Sat.Literal.neg 10), (Sat.Literal.pos 4887)] :=
  (lex_12_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4886), (Sat.Literal.pos 40), (Sat.Literal.pos 10), (Sat.Literal.pos 4887)] :=
  (lex_12_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4887) = lexBefore s permutation12 39 := by
  exact (positive_lex_of_descriptor s 4887 permutation12 40 (by rfl)).trans ((lex_skipped s permutation12 39 40 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation12 39) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation12 39 by rw [image12_eq]; rfl))

theorem lex_12_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4888) (Sat.Literal.pos 4887) (Sat.Literal.pos 39) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation12 39 (assignment s)
    (Sat.Literal.pos 4888) (Sat.Literal.pos 4887) (Sat.Literal.pos 39) (Sat.Literal.pos 201) (positive_of_descriptor s 4888 (.lex permutation12 39) (by rfl)) (lex_12_39_prefix s) (positive_select s 39) (lex_12_39_image s)

theorem lex_12_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.pos 39), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation12 39 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4887) (Sat.Literal.pos 39) (Sat.Literal.pos 201) (lex_12_39_prefix s) (positive_select s 39) (lex_12_39_image s)

theorem lex_12_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.pos 4887)] :=
  (lex_12_39_gate s).prop _ (List.Mem.head _)

theorem lex_12_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.neg 39), (Sat.Literal.pos 201)] :=
  (lex_12_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.pos 39), (Sat.Literal.neg 201)] :=
  (lex_12_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.neg 39), (Sat.Literal.neg 201), (Sat.Literal.pos 4888)] :=
  (lex_12_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4887), (Sat.Literal.pos 39), (Sat.Literal.pos 201), (Sat.Literal.pos 4888)] :=
  (lex_12_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4888) = lexBefore s permutation12 38 := by
  exact (positive_lex_of_descriptor s 4888 permutation12 39 (by rfl)).trans ((lex_skipped s permutation12 38 39 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation12 38) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation12 38 by rw [image12_eq]; rfl))

theorem lex_12_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4889) (Sat.Literal.pos 4888) (Sat.Literal.pos 38) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation12 38 (assignment s)
    (Sat.Literal.pos 4889) (Sat.Literal.pos 4888) (Sat.Literal.pos 38) (Sat.Literal.pos 137) (positive_of_descriptor s 4889 (.lex permutation12 38) (by rfl)) (lex_12_38_prefix s) (positive_select s 38) (lex_12_38_image s)

theorem lex_12_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.pos 38), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation12 38 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4888) (Sat.Literal.pos 38) (Sat.Literal.pos 137) (lex_12_38_prefix s) (positive_select s 38) (lex_12_38_image s)

theorem lex_12_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.pos 4888)] :=
  (lex_12_38_gate s).prop _ (List.Mem.head _)

theorem lex_12_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.neg 38), (Sat.Literal.pos 137)] :=
  (lex_12_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.pos 38), (Sat.Literal.neg 137)] :=
  (lex_12_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.neg 38), (Sat.Literal.neg 137), (Sat.Literal.pos 4889)] :=
  (lex_12_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4888), (Sat.Literal.pos 38), (Sat.Literal.pos 137), (Sat.Literal.pos 4889)] :=
  (lex_12_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4889) = lexBefore s permutation12 37 := by
  exact (positive_lex_of_descriptor s 4889 permutation12 38 (by rfl)).trans ((lex_skipped s permutation12 37 38 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation12 37) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation12 37 by rw [image12_eq]; rfl))

theorem lex_12_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4890) (Sat.Literal.pos 4889) (Sat.Literal.pos 37) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation12 37 (assignment s)
    (Sat.Literal.pos 4890) (Sat.Literal.pos 4889) (Sat.Literal.pos 37) (Sat.Literal.pos 73) (positive_of_descriptor s 4890 (.lex permutation12 37) (by rfl)) (lex_12_37_prefix s) (positive_select s 37) (lex_12_37_image s)

theorem lex_12_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.pos 37), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation12 37 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4889) (Sat.Literal.pos 37) (Sat.Literal.pos 73) (lex_12_37_prefix s) (positive_select s 37) (lex_12_37_image s)

theorem lex_12_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.pos 4889)] :=
  (lex_12_37_gate s).prop _ (List.Mem.head _)

theorem lex_12_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.neg 37), (Sat.Literal.pos 73)] :=
  (lex_12_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.pos 37), (Sat.Literal.neg 73)] :=
  (lex_12_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.neg 37), (Sat.Literal.neg 73), (Sat.Literal.pos 4890)] :=
  (lex_12_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4889), (Sat.Literal.pos 37), (Sat.Literal.pos 73), (Sat.Literal.pos 4890)] :=
  (lex_12_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4890) = lexBefore s permutation12 36 := by
  exact (positive_lex_of_descriptor s 4890 permutation12 37 (by rfl)).trans ((lex_skipped s permutation12 36 37 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation12 36) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation12 36 by rw [image12_eq]; rfl))

theorem lex_12_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4891) (Sat.Literal.pos 4890) (Sat.Literal.pos 36) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation12 36 (assignment s)
    (Sat.Literal.pos 4891) (Sat.Literal.pos 4890) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (positive_of_descriptor s 4891 (.lex permutation12 36) (by rfl)) (lex_12_36_prefix s) (positive_select s 36) (lex_12_36_image s)

theorem lex_12_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation12 36 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4890) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (lex_12_36_prefix s) (positive_select s 36) (lex_12_36_image s)

theorem lex_12_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.pos 4890)] :=
  (lex_12_36_gate s).prop _ (List.Mem.head _)

theorem lex_12_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.neg 36), (Sat.Literal.pos 9)] :=
  (lex_12_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] :=
  (lex_12_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.neg 36), (Sat.Literal.neg 9), (Sat.Literal.pos 4891)] :=
  (lex_12_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4890), (Sat.Literal.pos 36), (Sat.Literal.pos 9), (Sat.Literal.pos 4891)] :=
  (lex_12_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4891) = lexBefore s permutation12 35 := by
  exact (positive_lex_of_descriptor s 4891 permutation12 36 (by rfl)).trans ((lex_skipped s permutation12 35 36 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation12 35) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation12 35 by rw [image12_eq]; rfl))

theorem lex_12_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4892) (Sat.Literal.pos 4891) (Sat.Literal.pos 35) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation12 35 (assignment s)
    (Sat.Literal.pos 4892) (Sat.Literal.pos 4891) (Sat.Literal.pos 35) (Sat.Literal.pos 200) (positive_of_descriptor s 4892 (.lex permutation12 35) (by rfl)) (lex_12_35_prefix s) (positive_select s 35) (lex_12_35_image s)

theorem lex_12_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.pos 35), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation12 35 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4891) (Sat.Literal.pos 35) (Sat.Literal.pos 200) (lex_12_35_prefix s) (positive_select s 35) (lex_12_35_image s)

theorem lex_12_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.pos 4891)] :=
  (lex_12_35_gate s).prop _ (List.Mem.head _)

theorem lex_12_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.neg 35), (Sat.Literal.pos 200)] :=
  (lex_12_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.pos 35), (Sat.Literal.neg 200)] :=
  (lex_12_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.neg 35), (Sat.Literal.neg 200), (Sat.Literal.pos 4892)] :=
  (lex_12_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4891), (Sat.Literal.pos 35), (Sat.Literal.pos 200), (Sat.Literal.pos 4892)] :=
  (lex_12_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4892) = lexBefore s permutation12 34 := by
  exact (positive_lex_of_descriptor s 4892 permutation12 35 (by rfl)).trans ((lex_skipped s permutation12 34 35 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation12 34) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation12 34 by rw [image12_eq]; rfl))

theorem lex_12_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4893) (Sat.Literal.pos 4892) (Sat.Literal.pos 34) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation12 34 (assignment s)
    (Sat.Literal.pos 4893) (Sat.Literal.pos 4892) (Sat.Literal.pos 34) (Sat.Literal.pos 136) (positive_of_descriptor s 4893 (.lex permutation12 34) (by rfl)) (lex_12_34_prefix s) (positive_select s 34) (lex_12_34_image s)

theorem lex_12_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.pos 34), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation12 34 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4892) (Sat.Literal.pos 34) (Sat.Literal.pos 136) (lex_12_34_prefix s) (positive_select s 34) (lex_12_34_image s)

theorem lex_12_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.pos 4892)] :=
  (lex_12_34_gate s).prop _ (List.Mem.head _)

theorem lex_12_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.neg 34), (Sat.Literal.pos 136)] :=
  (lex_12_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.pos 34), (Sat.Literal.neg 136)] :=
  (lex_12_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.neg 34), (Sat.Literal.neg 136), (Sat.Literal.pos 4893)] :=
  (lex_12_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4892), (Sat.Literal.pos 34), (Sat.Literal.pos 136), (Sat.Literal.pos 4893)] :=
  (lex_12_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4893) = lexBefore s permutation12 33 := by
  exact (positive_lex_of_descriptor s 4893 permutation12 34 (by rfl)).trans ((lex_skipped s permutation12 33 34 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation12 33) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation12 33 by rw [image12_eq]; rfl))

theorem lex_12_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4894) (Sat.Literal.pos 4893) (Sat.Literal.pos 33) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation12 33 (assignment s)
    (Sat.Literal.pos 4894) (Sat.Literal.pos 4893) (Sat.Literal.pos 33) (Sat.Literal.pos 72) (positive_of_descriptor s 4894 (.lex permutation12 33) (by rfl)) (lex_12_33_prefix s) (positive_select s 33) (lex_12_33_image s)

theorem lex_12_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.pos 33), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation12 33 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4893) (Sat.Literal.pos 33) (Sat.Literal.pos 72) (lex_12_33_prefix s) (positive_select s 33) (lex_12_33_image s)

theorem lex_12_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.pos 4893)] :=
  (lex_12_33_gate s).prop _ (List.Mem.head _)

theorem lex_12_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.neg 33), (Sat.Literal.pos 72)] :=
  (lex_12_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.pos 33), (Sat.Literal.neg 72)] :=
  (lex_12_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.neg 33), (Sat.Literal.neg 72), (Sat.Literal.pos 4894)] :=
  (lex_12_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4893), (Sat.Literal.pos 33), (Sat.Literal.pos 72), (Sat.Literal.pos 4894)] :=
  (lex_12_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4894) = lexBefore s permutation12 32 := by
  exact (positive_lex_of_descriptor s 4894 permutation12 33 (by rfl)).trans ((lex_skipped s permutation12 32 33 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation12 32) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation12 32 by rw [image12_eq]; rfl))

theorem lex_12_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4895) (Sat.Literal.pos 4894) (Sat.Literal.pos 32) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation12 32 (assignment s)
    (Sat.Literal.pos 4895) (Sat.Literal.pos 4894) (Sat.Literal.pos 32) (Sat.Literal.pos 8) (positive_of_descriptor s 4895 (.lex permutation12 32) (by rfl)) (lex_12_32_prefix s) (positive_select s 32) (lex_12_32_image s)

theorem lex_12_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.pos 32), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation12 32 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4894) (Sat.Literal.pos 32) (Sat.Literal.pos 8) (lex_12_32_prefix s) (positive_select s 32) (lex_12_32_image s)

theorem lex_12_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.pos 4894)] :=
  (lex_12_32_gate s).prop _ (List.Mem.head _)

theorem lex_12_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.neg 32), (Sat.Literal.pos 8)] :=
  (lex_12_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.pos 32), (Sat.Literal.neg 8)] :=
  (lex_12_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.neg 32), (Sat.Literal.neg 8), (Sat.Literal.pos 4895)] :=
  (lex_12_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4894), (Sat.Literal.pos 32), (Sat.Literal.pos 8), (Sat.Literal.pos 4895)] :=
  (lex_12_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4895) = lexBefore s permutation12 31 := by
  exact (positive_lex_of_descriptor s 4895 permutation12 32 (by rfl)).trans ((lex_skipped s permutation12 31 32 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation12 31) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation12 31 by rw [image12_eq]; rfl))

theorem lex_12_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4896) (Sat.Literal.pos 4895) (Sat.Literal.pos 31) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation12 31 (assignment s)
    (Sat.Literal.pos 4896) (Sat.Literal.pos 4895) (Sat.Literal.pos 31) (Sat.Literal.pos 199) (positive_of_descriptor s 4896 (.lex permutation12 31) (by rfl)) (lex_12_31_prefix s) (positive_select s 31) (lex_12_31_image s)

theorem lex_12_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.pos 31), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation12 31 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4895) (Sat.Literal.pos 31) (Sat.Literal.pos 199) (lex_12_31_prefix s) (positive_select s 31) (lex_12_31_image s)

theorem lex_12_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.pos 4895)] :=
  (lex_12_31_gate s).prop _ (List.Mem.head _)

theorem lex_12_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.neg 31), (Sat.Literal.pos 199)] :=
  (lex_12_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.pos 31), (Sat.Literal.neg 199)] :=
  (lex_12_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.neg 31), (Sat.Literal.neg 199), (Sat.Literal.pos 4896)] :=
  (lex_12_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4895), (Sat.Literal.pos 31), (Sat.Literal.pos 199), (Sat.Literal.pos 4896)] :=
  (lex_12_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4896) = lexBefore s permutation12 30 := by
  exact (positive_lex_of_descriptor s 4896 permutation12 31 (by rfl)).trans ((lex_skipped s permutation12 30 31 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation12 30) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation12 30 by rw [image12_eq]; rfl))

theorem lex_12_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4897) (Sat.Literal.pos 4896) (Sat.Literal.pos 30) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation12 30 (assignment s)
    (Sat.Literal.pos 4897) (Sat.Literal.pos 4896) (Sat.Literal.pos 30) (Sat.Literal.pos 135) (positive_of_descriptor s 4897 (.lex permutation12 30) (by rfl)) (lex_12_30_prefix s) (positive_select s 30) (lex_12_30_image s)

theorem lex_12_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.pos 30), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation12 30 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4896) (Sat.Literal.pos 30) (Sat.Literal.pos 135) (lex_12_30_prefix s) (positive_select s 30) (lex_12_30_image s)

theorem lex_12_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.pos 4896)] :=
  (lex_12_30_gate s).prop _ (List.Mem.head _)

theorem lex_12_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.neg 30), (Sat.Literal.pos 135)] :=
  (lex_12_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.pos 30), (Sat.Literal.neg 135)] :=
  (lex_12_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.neg 30), (Sat.Literal.neg 135), (Sat.Literal.pos 4897)] :=
  (lex_12_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4896), (Sat.Literal.pos 30), (Sat.Literal.pos 135), (Sat.Literal.pos 4897)] :=
  (lex_12_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4897) = lexBefore s permutation12 29 := by
  exact (positive_lex_of_descriptor s 4897 permutation12 30 (by rfl)).trans ((lex_skipped s permutation12 29 30 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation12 29) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation12 29 by rw [image12_eq]; rfl))

theorem lex_12_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4898) (Sat.Literal.pos 4897) (Sat.Literal.pos 29) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation12 29 (assignment s)
    (Sat.Literal.pos 4898) (Sat.Literal.pos 4897) (Sat.Literal.pos 29) (Sat.Literal.pos 71) (positive_of_descriptor s 4898 (.lex permutation12 29) (by rfl)) (lex_12_29_prefix s) (positive_select s 29) (lex_12_29_image s)

theorem lex_12_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.pos 29), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation12 29 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4897) (Sat.Literal.pos 29) (Sat.Literal.pos 71) (lex_12_29_prefix s) (positive_select s 29) (lex_12_29_image s)

theorem lex_12_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.pos 4897)] :=
  (lex_12_29_gate s).prop _ (List.Mem.head _)

theorem lex_12_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.neg 29), (Sat.Literal.pos 71)] :=
  (lex_12_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.pos 29), (Sat.Literal.neg 71)] :=
  (lex_12_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.neg 29), (Sat.Literal.neg 71), (Sat.Literal.pos 4898)] :=
  (lex_12_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4897), (Sat.Literal.pos 29), (Sat.Literal.pos 71), (Sat.Literal.pos 4898)] :=
  (lex_12_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4898) = lexBefore s permutation12 28 := by
  exact (positive_lex_of_descriptor s 4898 permutation12 29 (by rfl)).trans ((lex_skipped s permutation12 28 29 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation12 28) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation12 28 by rw [image12_eq]; rfl))

theorem lex_12_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4899) (Sat.Literal.pos 4898) (Sat.Literal.pos 28) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation12 28 (assignment s)
    (Sat.Literal.pos 4899) (Sat.Literal.pos 4898) (Sat.Literal.pos 28) (Sat.Literal.pos 7) (positive_of_descriptor s 4899 (.lex permutation12 28) (by rfl)) (lex_12_28_prefix s) (positive_select s 28) (lex_12_28_image s)

theorem lex_12_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.pos 28), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation12 28 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4898) (Sat.Literal.pos 28) (Sat.Literal.pos 7) (lex_12_28_prefix s) (positive_select s 28) (lex_12_28_image s)

theorem lex_12_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.pos 4898)] :=
  (lex_12_28_gate s).prop _ (List.Mem.head _)

theorem lex_12_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.neg 28), (Sat.Literal.pos 7)] :=
  (lex_12_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.pos 28), (Sat.Literal.neg 7)] :=
  (lex_12_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.neg 28), (Sat.Literal.neg 7), (Sat.Literal.pos 4899)] :=
  (lex_12_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4898), (Sat.Literal.pos 28), (Sat.Literal.pos 7), (Sat.Literal.pos 4899)] :=
  (lex_12_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4899) = lexBefore s permutation12 27 := by
  exact (positive_lex_of_descriptor s 4899 permutation12 28 (by rfl)).trans ((lex_skipped s permutation12 27 28 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation12 27) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation12 27 by rw [image12_eq]; rfl))

theorem lex_12_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4900) (Sat.Literal.pos 4899) (Sat.Literal.pos 27) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation12 27 (assignment s)
    (Sat.Literal.pos 4900) (Sat.Literal.pos 4899) (Sat.Literal.pos 27) (Sat.Literal.pos 198) (positive_of_descriptor s 4900 (.lex permutation12 27) (by rfl)) (lex_12_27_prefix s) (positive_select s 27) (lex_12_27_image s)

theorem lex_12_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.pos 27), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation12 27 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4899) (Sat.Literal.pos 27) (Sat.Literal.pos 198) (lex_12_27_prefix s) (positive_select s 27) (lex_12_27_image s)

theorem lex_12_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.pos 4899)] :=
  (lex_12_27_gate s).prop _ (List.Mem.head _)

theorem lex_12_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.neg 27), (Sat.Literal.pos 198)] :=
  (lex_12_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.pos 27), (Sat.Literal.neg 198)] :=
  (lex_12_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.neg 27), (Sat.Literal.neg 198), (Sat.Literal.pos 4900)] :=
  (lex_12_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4899), (Sat.Literal.pos 27), (Sat.Literal.pos 198), (Sat.Literal.pos 4900)] :=
  (lex_12_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4900) = lexBefore s permutation12 26 := by
  exact (positive_lex_of_descriptor s 4900 permutation12 27 (by rfl)).trans ((lex_skipped s permutation12 26 27 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation12 26) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation12 26 by rw [image12_eq]; rfl))

theorem lex_12_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4901) (Sat.Literal.pos 4900) (Sat.Literal.pos 26) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation12 26 (assignment s)
    (Sat.Literal.pos 4901) (Sat.Literal.pos 4900) (Sat.Literal.pos 26) (Sat.Literal.pos 134) (positive_of_descriptor s 4901 (.lex permutation12 26) (by rfl)) (lex_12_26_prefix s) (positive_select s 26) (lex_12_26_image s)

theorem lex_12_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.pos 26), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation12 26 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4900) (Sat.Literal.pos 26) (Sat.Literal.pos 134) (lex_12_26_prefix s) (positive_select s 26) (lex_12_26_image s)

theorem lex_12_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.pos 4900)] :=
  (lex_12_26_gate s).prop _ (List.Mem.head _)

theorem lex_12_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.neg 26), (Sat.Literal.pos 134)] :=
  (lex_12_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.pos 26), (Sat.Literal.neg 134)] :=
  (lex_12_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.neg 26), (Sat.Literal.neg 134), (Sat.Literal.pos 4901)] :=
  (lex_12_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4900), (Sat.Literal.pos 26), (Sat.Literal.pos 134), (Sat.Literal.pos 4901)] :=
  (lex_12_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4901) = lexBefore s permutation12 25 := by
  exact (positive_lex_of_descriptor s 4901 permutation12 26 (by rfl)).trans ((lex_skipped s permutation12 25 26 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation12 25) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation12 25 by rw [image12_eq]; rfl))

theorem lex_12_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4902) (Sat.Literal.pos 4901) (Sat.Literal.pos 25) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation12 25 (assignment s)
    (Sat.Literal.pos 4902) (Sat.Literal.pos 4901) (Sat.Literal.pos 25) (Sat.Literal.pos 70) (positive_of_descriptor s 4902 (.lex permutation12 25) (by rfl)) (lex_12_25_prefix s) (positive_select s 25) (lex_12_25_image s)

theorem lex_12_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.pos 25), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation12 25 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4901) (Sat.Literal.pos 25) (Sat.Literal.pos 70) (lex_12_25_prefix s) (positive_select s 25) (lex_12_25_image s)

theorem lex_12_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.pos 4901)] :=
  (lex_12_25_gate s).prop _ (List.Mem.head _)

theorem lex_12_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.neg 25), (Sat.Literal.pos 70)] :=
  (lex_12_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.pos 25), (Sat.Literal.neg 70)] :=
  (lex_12_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.neg 25), (Sat.Literal.neg 70), (Sat.Literal.pos 4902)] :=
  (lex_12_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4901), (Sat.Literal.pos 25), (Sat.Literal.pos 70), (Sat.Literal.pos 4902)] :=
  (lex_12_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4902) = lexBefore s permutation12 24 := by
  exact (positive_lex_of_descriptor s 4902 permutation12 25 (by rfl)).trans ((lex_skipped s permutation12 24 25 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation12 24) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation12 24 by rw [image12_eq]; rfl))

theorem lex_12_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4903) (Sat.Literal.pos 4902) (Sat.Literal.pos 24) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation12 24 (assignment s)
    (Sat.Literal.pos 4903) (Sat.Literal.pos 4902) (Sat.Literal.pos 24) (Sat.Literal.pos 6) (positive_of_descriptor s 4903 (.lex permutation12 24) (by rfl)) (lex_12_24_prefix s) (positive_select s 24) (lex_12_24_image s)

theorem lex_12_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.pos 24), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation12 24 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4902) (Sat.Literal.pos 24) (Sat.Literal.pos 6) (lex_12_24_prefix s) (positive_select s 24) (lex_12_24_image s)

theorem lex_12_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.pos 4902)] :=
  (lex_12_24_gate s).prop _ (List.Mem.head _)

theorem lex_12_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.neg 24), (Sat.Literal.pos 6)] :=
  (lex_12_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.pos 24), (Sat.Literal.neg 6)] :=
  (lex_12_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.neg 24), (Sat.Literal.neg 6), (Sat.Literal.pos 4903)] :=
  (lex_12_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4902), (Sat.Literal.pos 24), (Sat.Literal.pos 6), (Sat.Literal.pos 4903)] :=
  (lex_12_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4903) = lexBefore s permutation12 23 := by
  exact (positive_lex_of_descriptor s 4903 permutation12 24 (by rfl)).trans ((lex_skipped s permutation12 23 24 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation12 23) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation12 23 by rw [image12_eq]; rfl))

theorem lex_12_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4904) (Sat.Literal.pos 4903) (Sat.Literal.pos 23) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation12 23 (assignment s)
    (Sat.Literal.pos 4904) (Sat.Literal.pos 4903) (Sat.Literal.pos 23) (Sat.Literal.pos 197) (positive_of_descriptor s 4904 (.lex permutation12 23) (by rfl)) (lex_12_23_prefix s) (positive_select s 23) (lex_12_23_image s)

theorem lex_12_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.pos 23), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation12 23 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4903) (Sat.Literal.pos 23) (Sat.Literal.pos 197) (lex_12_23_prefix s) (positive_select s 23) (lex_12_23_image s)

theorem lex_12_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.pos 4903)] :=
  (lex_12_23_gate s).prop _ (List.Mem.head _)

theorem lex_12_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.neg 23), (Sat.Literal.pos 197)] :=
  (lex_12_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.pos 23), (Sat.Literal.neg 197)] :=
  (lex_12_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.neg 23), (Sat.Literal.neg 197), (Sat.Literal.pos 4904)] :=
  (lex_12_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4903), (Sat.Literal.pos 23), (Sat.Literal.pos 197), (Sat.Literal.pos 4904)] :=
  (lex_12_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4904) = lexBefore s permutation12 22 := by
  exact (positive_lex_of_descriptor s 4904 permutation12 23 (by rfl)).trans ((lex_skipped s permutation12 22 23 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation12 22) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation12 22 by rw [image12_eq]; rfl))

theorem lex_12_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4905) (Sat.Literal.pos 4904) (Sat.Literal.pos 22) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation12 22 (assignment s)
    (Sat.Literal.pos 4905) (Sat.Literal.pos 4904) (Sat.Literal.pos 22) (Sat.Literal.pos 133) (positive_of_descriptor s 4905 (.lex permutation12 22) (by rfl)) (lex_12_22_prefix s) (positive_select s 22) (lex_12_22_image s)

theorem lex_12_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.pos 22), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation12 22 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4904) (Sat.Literal.pos 22) (Sat.Literal.pos 133) (lex_12_22_prefix s) (positive_select s 22) (lex_12_22_image s)

theorem lex_12_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.pos 4904)] :=
  (lex_12_22_gate s).prop _ (List.Mem.head _)

theorem lex_12_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.neg 22), (Sat.Literal.pos 133)] :=
  (lex_12_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.pos 22), (Sat.Literal.neg 133)] :=
  (lex_12_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.neg 22), (Sat.Literal.neg 133), (Sat.Literal.pos 4905)] :=
  (lex_12_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4904), (Sat.Literal.pos 22), (Sat.Literal.pos 133), (Sat.Literal.pos 4905)] :=
  (lex_12_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4905) = lexBefore s permutation12 21 := by
  exact (positive_lex_of_descriptor s 4905 permutation12 22 (by rfl)).trans ((lex_skipped s permutation12 21 22 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation12 21) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation12 21 by rw [image12_eq]; rfl))

theorem lex_12_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4906) (Sat.Literal.pos 4905) (Sat.Literal.pos 21) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation12 21 (assignment s)
    (Sat.Literal.pos 4906) (Sat.Literal.pos 4905) (Sat.Literal.pos 21) (Sat.Literal.pos 69) (positive_of_descriptor s 4906 (.lex permutation12 21) (by rfl)) (lex_12_21_prefix s) (positive_select s 21) (lex_12_21_image s)

theorem lex_12_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.pos 21), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation12 21 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4905) (Sat.Literal.pos 21) (Sat.Literal.pos 69) (lex_12_21_prefix s) (positive_select s 21) (lex_12_21_image s)

theorem lex_12_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.pos 4905)] :=
  (lex_12_21_gate s).prop _ (List.Mem.head _)

theorem lex_12_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.neg 21), (Sat.Literal.pos 69)] :=
  (lex_12_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.pos 21), (Sat.Literal.neg 69)] :=
  (lex_12_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.neg 21), (Sat.Literal.neg 69), (Sat.Literal.pos 4906)] :=
  (lex_12_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4905), (Sat.Literal.pos 21), (Sat.Literal.pos 69), (Sat.Literal.pos 4906)] :=
  (lex_12_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4906) = lexBefore s permutation12 20 := by
  exact (positive_lex_of_descriptor s 4906 permutation12 21 (by rfl)).trans ((lex_skipped s permutation12 20 21 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation12 20) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation12 20 by rw [image12_eq]; rfl))

theorem lex_12_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4907) (Sat.Literal.pos 4906) (Sat.Literal.pos 20) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation12 20 (assignment s)
    (Sat.Literal.pos 4907) (Sat.Literal.pos 4906) (Sat.Literal.pos 20) (Sat.Literal.pos 5) (positive_of_descriptor s 4907 (.lex permutation12 20) (by rfl)) (lex_12_20_prefix s) (positive_select s 20) (lex_12_20_image s)

theorem lex_12_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.pos 20), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation12 20 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4906) (Sat.Literal.pos 20) (Sat.Literal.pos 5) (lex_12_20_prefix s) (positive_select s 20) (lex_12_20_image s)

theorem lex_12_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.pos 4906)] :=
  (lex_12_20_gate s).prop _ (List.Mem.head _)

theorem lex_12_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.neg 20), (Sat.Literal.pos 5)] :=
  (lex_12_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.pos 20), (Sat.Literal.neg 5)] :=
  (lex_12_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.neg 20), (Sat.Literal.neg 5), (Sat.Literal.pos 4907)] :=
  (lex_12_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4906), (Sat.Literal.pos 20), (Sat.Literal.pos 5), (Sat.Literal.pos 4907)] :=
  (lex_12_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4907) = lexBefore s permutation12 19 := by
  exact (positive_lex_of_descriptor s 4907 permutation12 20 (by rfl)).trans ((lex_skipped s permutation12 19 20 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation12 19) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation12 19 by rw [image12_eq]; rfl))

theorem lex_12_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4908) (Sat.Literal.pos 4907) (Sat.Literal.pos 19) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation12 19 (assignment s)
    (Sat.Literal.pos 4908) (Sat.Literal.pos 4907) (Sat.Literal.pos 19) (Sat.Literal.pos 196) (positive_of_descriptor s 4908 (.lex permutation12 19) (by rfl)) (lex_12_19_prefix s) (positive_select s 19) (lex_12_19_image s)

theorem lex_12_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.pos 19), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation12 19 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4907) (Sat.Literal.pos 19) (Sat.Literal.pos 196) (lex_12_19_prefix s) (positive_select s 19) (lex_12_19_image s)

theorem lex_12_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.pos 4907)] :=
  (lex_12_19_gate s).prop _ (List.Mem.head _)

theorem lex_12_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.neg 19), (Sat.Literal.pos 196)] :=
  (lex_12_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.pos 19), (Sat.Literal.neg 196)] :=
  (lex_12_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.neg 19), (Sat.Literal.neg 196), (Sat.Literal.pos 4908)] :=
  (lex_12_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4907), (Sat.Literal.pos 19), (Sat.Literal.pos 196), (Sat.Literal.pos 4908)] :=
  (lex_12_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4908) = lexBefore s permutation12 18 := by
  exact (positive_lex_of_descriptor s 4908 permutation12 19 (by rfl)).trans ((lex_skipped s permutation12 18 19 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation12 18) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation12 18 by rw [image12_eq]; rfl))

theorem lex_12_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4909) (Sat.Literal.pos 4908) (Sat.Literal.pos 18) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation12 18 (assignment s)
    (Sat.Literal.pos 4909) (Sat.Literal.pos 4908) (Sat.Literal.pos 18) (Sat.Literal.pos 132) (positive_of_descriptor s 4909 (.lex permutation12 18) (by rfl)) (lex_12_18_prefix s) (positive_select s 18) (lex_12_18_image s)

theorem lex_12_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.pos 18), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation12 18 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4908) (Sat.Literal.pos 18) (Sat.Literal.pos 132) (lex_12_18_prefix s) (positive_select s 18) (lex_12_18_image s)

theorem lex_12_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.pos 4908)] :=
  (lex_12_18_gate s).prop _ (List.Mem.head _)

theorem lex_12_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.neg 18), (Sat.Literal.pos 132)] :=
  (lex_12_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.pos 18), (Sat.Literal.neg 132)] :=
  (lex_12_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.neg 18), (Sat.Literal.neg 132), (Sat.Literal.pos 4909)] :=
  (lex_12_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4908), (Sat.Literal.pos 18), (Sat.Literal.pos 132), (Sat.Literal.pos 4909)] :=
  (lex_12_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4909) = lexBefore s permutation12 17 := by
  exact (positive_lex_of_descriptor s 4909 permutation12 18 (by rfl)).trans ((lex_skipped s permutation12 17 18 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation12 17) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation12 17 by rw [image12_eq]; rfl))

theorem lex_12_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4910) (Sat.Literal.pos 4909) (Sat.Literal.pos 17) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation12 17 (assignment s)
    (Sat.Literal.pos 4910) (Sat.Literal.pos 4909) (Sat.Literal.pos 17) (Sat.Literal.pos 68) (positive_of_descriptor s 4910 (.lex permutation12 17) (by rfl)) (lex_12_17_prefix s) (positive_select s 17) (lex_12_17_image s)

theorem lex_12_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.pos 17), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation12 17 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4909) (Sat.Literal.pos 17) (Sat.Literal.pos 68) (lex_12_17_prefix s) (positive_select s 17) (lex_12_17_image s)

theorem lex_12_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.pos 4909)] :=
  (lex_12_17_gate s).prop _ (List.Mem.head _)

theorem lex_12_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.neg 17), (Sat.Literal.pos 68)] :=
  (lex_12_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.pos 17), (Sat.Literal.neg 68)] :=
  (lex_12_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.neg 17), (Sat.Literal.neg 68), (Sat.Literal.pos 4910)] :=
  (lex_12_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4909), (Sat.Literal.pos 17), (Sat.Literal.pos 68), (Sat.Literal.pos 4910)] :=
  (lex_12_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4910) = lexBefore s permutation12 16 := by
  exact (positive_lex_of_descriptor s 4910 permutation12 17 (by rfl)).trans ((lex_skipped s permutation12 16 17 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation12 16) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation12 16 by rw [image12_eq]; rfl))

theorem lex_12_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4911) (Sat.Literal.pos 4910) (Sat.Literal.pos 16) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation12 16 (assignment s)
    (Sat.Literal.pos 4911) (Sat.Literal.pos 4910) (Sat.Literal.pos 16) (Sat.Literal.pos 4) (positive_of_descriptor s 4911 (.lex permutation12 16) (by rfl)) (lex_12_16_prefix s) (positive_select s 16) (lex_12_16_image s)

theorem lex_12_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.pos 16), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation12 16 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4910) (Sat.Literal.pos 16) (Sat.Literal.pos 4) (lex_12_16_prefix s) (positive_select s 16) (lex_12_16_image s)

theorem lex_12_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.pos 4910)] :=
  (lex_12_16_gate s).prop _ (List.Mem.head _)

theorem lex_12_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.neg 16), (Sat.Literal.pos 4)] :=
  (lex_12_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.pos 16), (Sat.Literal.neg 4)] :=
  (lex_12_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.neg 16), (Sat.Literal.neg 4), (Sat.Literal.pos 4911)] :=
  (lex_12_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4910), (Sat.Literal.pos 16), (Sat.Literal.pos 4), (Sat.Literal.pos 4911)] :=
  (lex_12_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4911) = lexBefore s permutation12 15 := by
  exact (positive_lex_of_descriptor s 4911 permutation12 16 (by rfl)).trans ((lex_skipped s permutation12 15 16 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation12 15) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation12 15 by rw [image12_eq]; rfl))

theorem lex_12_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4912) (Sat.Literal.pos 4911) (Sat.Literal.pos 15) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation12 15 (assignment s)
    (Sat.Literal.pos 4912) (Sat.Literal.pos 4911) (Sat.Literal.pos 15) (Sat.Literal.pos 195) (positive_of_descriptor s 4912 (.lex permutation12 15) (by rfl)) (lex_12_15_prefix s) (positive_select s 15) (lex_12_15_image s)

theorem lex_12_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.pos 15), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation12 15 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4911) (Sat.Literal.pos 15) (Sat.Literal.pos 195) (lex_12_15_prefix s) (positive_select s 15) (lex_12_15_image s)

theorem lex_12_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.pos 4911)] :=
  (lex_12_15_gate s).prop _ (List.Mem.head _)

theorem lex_12_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.neg 15), (Sat.Literal.pos 195)] :=
  (lex_12_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.pos 15), (Sat.Literal.neg 195)] :=
  (lex_12_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.neg 15), (Sat.Literal.neg 195), (Sat.Literal.pos 4912)] :=
  (lex_12_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4911), (Sat.Literal.pos 15), (Sat.Literal.pos 195), (Sat.Literal.pos 4912)] :=
  (lex_12_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4912) = lexBefore s permutation12 14 := by
  exact (positive_lex_of_descriptor s 4912 permutation12 15 (by rfl)).trans ((lex_skipped s permutation12 14 15 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation12 14) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation12 14 by rw [image12_eq]; rfl))

theorem lex_12_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4913) (Sat.Literal.pos 4912) (Sat.Literal.pos 14) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation12 14 (assignment s)
    (Sat.Literal.pos 4913) (Sat.Literal.pos 4912) (Sat.Literal.pos 14) (Sat.Literal.pos 131) (positive_of_descriptor s 4913 (.lex permutation12 14) (by rfl)) (lex_12_14_prefix s) (positive_select s 14) (lex_12_14_image s)

theorem lex_12_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.pos 14), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation12 14 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4912) (Sat.Literal.pos 14) (Sat.Literal.pos 131) (lex_12_14_prefix s) (positive_select s 14) (lex_12_14_image s)

theorem lex_12_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.pos 4912)] :=
  (lex_12_14_gate s).prop _ (List.Mem.head _)

theorem lex_12_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.neg 14), (Sat.Literal.pos 131)] :=
  (lex_12_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.pos 14), (Sat.Literal.neg 131)] :=
  (lex_12_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.neg 14), (Sat.Literal.neg 131), (Sat.Literal.pos 4913)] :=
  (lex_12_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4912), (Sat.Literal.pos 14), (Sat.Literal.pos 131), (Sat.Literal.pos 4913)] :=
  (lex_12_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4913) = lexBefore s permutation12 13 := by
  exact (positive_lex_of_descriptor s 4913 permutation12 14 (by rfl)).trans ((lex_skipped s permutation12 13 14 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation12 13) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation12 13 by rw [image12_eq]; rfl))

theorem lex_12_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4914) (Sat.Literal.pos 4913) (Sat.Literal.pos 13) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation12 13 (assignment s)
    (Sat.Literal.pos 4914) (Sat.Literal.pos 4913) (Sat.Literal.pos 13) (Sat.Literal.pos 67) (positive_of_descriptor s 4914 (.lex permutation12 13) (by rfl)) (lex_12_13_prefix s) (positive_select s 13) (lex_12_13_image s)

theorem lex_12_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.pos 13), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation12 13 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4913) (Sat.Literal.pos 13) (Sat.Literal.pos 67) (lex_12_13_prefix s) (positive_select s 13) (lex_12_13_image s)

theorem lex_12_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.pos 4913)] :=
  (lex_12_13_gate s).prop _ (List.Mem.head _)

theorem lex_12_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.neg 13), (Sat.Literal.pos 67)] :=
  (lex_12_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.pos 13), (Sat.Literal.neg 67)] :=
  (lex_12_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.neg 13), (Sat.Literal.neg 67), (Sat.Literal.pos 4914)] :=
  (lex_12_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4913), (Sat.Literal.pos 13), (Sat.Literal.pos 67), (Sat.Literal.pos 4914)] :=
  (lex_12_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4914) = lexBefore s permutation12 12 := by
  exact (positive_lex_of_descriptor s 4914 permutation12 13 (by rfl)).trans ((lex_skipped s permutation12 12 13 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation12 12) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation12 12 by rw [image12_eq]; rfl))

theorem lex_12_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4915) (Sat.Literal.pos 4914) (Sat.Literal.pos 12) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation12 12 (assignment s)
    (Sat.Literal.pos 4915) (Sat.Literal.pos 4914) (Sat.Literal.pos 12) (Sat.Literal.pos 3) (positive_of_descriptor s 4915 (.lex permutation12 12) (by rfl)) (lex_12_12_prefix s) (positive_select s 12) (lex_12_12_image s)

theorem lex_12_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.pos 12), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation12 12 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4914) (Sat.Literal.pos 12) (Sat.Literal.pos 3) (lex_12_12_prefix s) (positive_select s 12) (lex_12_12_image s)

theorem lex_12_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.pos 4914)] :=
  (lex_12_12_gate s).prop _ (List.Mem.head _)

theorem lex_12_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.neg 12), (Sat.Literal.pos 3)] :=
  (lex_12_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.pos 12), (Sat.Literal.neg 3)] :=
  (lex_12_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.neg 12), (Sat.Literal.neg 3), (Sat.Literal.pos 4915)] :=
  (lex_12_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4914), (Sat.Literal.pos 12), (Sat.Literal.pos 3), (Sat.Literal.pos 4915)] :=
  (lex_12_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4915) = lexBefore s permutation12 11 := by
  exact (positive_lex_of_descriptor s 4915 permutation12 12 (by rfl)).trans ((lex_skipped s permutation12 11 12 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation12 11) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation12 11 by rw [image12_eq]; rfl))

theorem lex_12_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4916) (Sat.Literal.pos 4915) (Sat.Literal.pos 11) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation12 11 (assignment s)
    (Sat.Literal.pos 4916) (Sat.Literal.pos 4915) (Sat.Literal.pos 11) (Sat.Literal.pos 194) (positive_of_descriptor s 4916 (.lex permutation12 11) (by rfl)) (lex_12_11_prefix s) (positive_select s 11) (lex_12_11_image s)

theorem lex_12_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.pos 11), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation12 11 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4915) (Sat.Literal.pos 11) (Sat.Literal.pos 194) (lex_12_11_prefix s) (positive_select s 11) (lex_12_11_image s)

theorem lex_12_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.pos 4915)] :=
  (lex_12_11_gate s).prop _ (List.Mem.head _)

theorem lex_12_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.neg 11), (Sat.Literal.pos 194)] :=
  (lex_12_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.pos 11), (Sat.Literal.neg 194)] :=
  (lex_12_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.neg 11), (Sat.Literal.neg 194), (Sat.Literal.pos 4916)] :=
  (lex_12_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4915), (Sat.Literal.pos 11), (Sat.Literal.pos 194), (Sat.Literal.pos 4916)] :=
  (lex_12_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4916) = lexBefore s permutation12 10 := by
  exact (positive_lex_of_descriptor s 4916 permutation12 11 (by rfl)).trans ((lex_skipped s permutation12 10 11 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation12 10) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation12 10 by rw [image12_eq]; rfl))

theorem lex_12_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4917) (Sat.Literal.pos 4916) (Sat.Literal.pos 10) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation12 10 (assignment s)
    (Sat.Literal.pos 4917) (Sat.Literal.pos 4916) (Sat.Literal.pos 10) (Sat.Literal.pos 130) (positive_of_descriptor s 4917 (.lex permutation12 10) (by rfl)) (lex_12_10_prefix s) (positive_select s 10) (lex_12_10_image s)

theorem lex_12_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.pos 10), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation12 10 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4916) (Sat.Literal.pos 10) (Sat.Literal.pos 130) (lex_12_10_prefix s) (positive_select s 10) (lex_12_10_image s)

theorem lex_12_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.pos 4916)] :=
  (lex_12_10_gate s).prop _ (List.Mem.head _)

theorem lex_12_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.neg 10), (Sat.Literal.pos 130)] :=
  (lex_12_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.pos 10), (Sat.Literal.neg 130)] :=
  (lex_12_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.neg 10), (Sat.Literal.neg 130), (Sat.Literal.pos 4917)] :=
  (lex_12_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4916), (Sat.Literal.pos 10), (Sat.Literal.pos 130), (Sat.Literal.pos 4917)] :=
  (lex_12_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4917) = lexBefore s permutation12 9 := by
  exact (positive_lex_of_descriptor s 4917 permutation12 10 (by rfl)).trans ((lex_skipped s permutation12 9 10 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation12 9) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation12 9 by rw [image12_eq]; rfl))

theorem lex_12_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4918) (Sat.Literal.pos 4917) (Sat.Literal.pos 9) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation12 9 (assignment s)
    (Sat.Literal.pos 4918) (Sat.Literal.pos 4917) (Sat.Literal.pos 9) (Sat.Literal.pos 66) (positive_of_descriptor s 4918 (.lex permutation12 9) (by rfl)) (lex_12_9_prefix s) (positive_select s 9) (lex_12_9_image s)

theorem lex_12_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.pos 9), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation12 9 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4917) (Sat.Literal.pos 9) (Sat.Literal.pos 66) (lex_12_9_prefix s) (positive_select s 9) (lex_12_9_image s)

theorem lex_12_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.pos 4917)] :=
  (lex_12_9_gate s).prop _ (List.Mem.head _)

theorem lex_12_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.neg 9), (Sat.Literal.pos 66)] :=
  (lex_12_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.pos 9), (Sat.Literal.neg 66)] :=
  (lex_12_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.neg 9), (Sat.Literal.neg 66), (Sat.Literal.pos 4918)] :=
  (lex_12_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4917), (Sat.Literal.pos 9), (Sat.Literal.pos 66), (Sat.Literal.pos 4918)] :=
  (lex_12_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4918) = lexBefore s permutation12 8 := by
  exact (positive_lex_of_descriptor s 4918 permutation12 9 (by rfl)).trans ((lex_skipped s permutation12 8 9 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation12 8) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation12 8 by rw [image12_eq]; rfl))

theorem lex_12_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4919) (Sat.Literal.pos 4918) (Sat.Literal.pos 8) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation12 8 (assignment s)
    (Sat.Literal.pos 4919) (Sat.Literal.pos 4918) (Sat.Literal.pos 8) (Sat.Literal.pos 2) (positive_of_descriptor s 4919 (.lex permutation12 8) (by rfl)) (lex_12_8_prefix s) (positive_select s 8) (lex_12_8_image s)

theorem lex_12_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.pos 8), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation12 8 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4918) (Sat.Literal.pos 8) (Sat.Literal.pos 2) (lex_12_8_prefix s) (positive_select s 8) (lex_12_8_image s)

theorem lex_12_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.pos 4918)] :=
  (lex_12_8_gate s).prop _ (List.Mem.head _)

theorem lex_12_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.neg 8), (Sat.Literal.pos 2)] :=
  (lex_12_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.pos 8), (Sat.Literal.neg 2)] :=
  (lex_12_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.neg 8), (Sat.Literal.neg 2), (Sat.Literal.pos 4919)] :=
  (lex_12_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4918), (Sat.Literal.pos 8), (Sat.Literal.pos 2), (Sat.Literal.pos 4919)] :=
  (lex_12_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4919) = lexBefore s permutation12 7 := by
  exact (positive_lex_of_descriptor s 4919 permutation12 8 (by rfl)).trans ((lex_skipped s permutation12 7 8 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation12 7) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation12 7 by rw [image12_eq]; rfl))

theorem lex_12_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4920) (Sat.Literal.pos 4919) (Sat.Literal.pos 7) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation12 7 (assignment s)
    (Sat.Literal.pos 4920) (Sat.Literal.pos 4919) (Sat.Literal.pos 7) (Sat.Literal.pos 193) (positive_of_descriptor s 4920 (.lex permutation12 7) (by rfl)) (lex_12_7_prefix s) (positive_select s 7) (lex_12_7_image s)

theorem lex_12_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.pos 7), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation12 7 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4919) (Sat.Literal.pos 7) (Sat.Literal.pos 193) (lex_12_7_prefix s) (positive_select s 7) (lex_12_7_image s)

theorem lex_12_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.pos 4919)] :=
  (lex_12_7_gate s).prop _ (List.Mem.head _)

theorem lex_12_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.neg 7), (Sat.Literal.pos 193)] :=
  (lex_12_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.pos 7), (Sat.Literal.neg 193)] :=
  (lex_12_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.neg 7), (Sat.Literal.neg 193), (Sat.Literal.pos 4920)] :=
  (lex_12_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4919), (Sat.Literal.pos 7), (Sat.Literal.pos 193), (Sat.Literal.pos 4920)] :=
  (lex_12_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4920) = lexBefore s permutation12 6 := by
  exact (positive_lex_of_descriptor s 4920 permutation12 7 (by rfl)).trans ((lex_skipped s permutation12 6 7 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation12 6) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation12 6 by rw [image12_eq]; rfl))

theorem lex_12_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4921) (Sat.Literal.pos 4920) (Sat.Literal.pos 6) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation12 6 (assignment s)
    (Sat.Literal.pos 4921) (Sat.Literal.pos 4920) (Sat.Literal.pos 6) (Sat.Literal.pos 129) (positive_of_descriptor s 4921 (.lex permutation12 6) (by rfl)) (lex_12_6_prefix s) (positive_select s 6) (lex_12_6_image s)

theorem lex_12_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.pos 6), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation12 6 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4920) (Sat.Literal.pos 6) (Sat.Literal.pos 129) (lex_12_6_prefix s) (positive_select s 6) (lex_12_6_image s)

theorem lex_12_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.pos 4920)] :=
  (lex_12_6_gate s).prop _ (List.Mem.head _)

theorem lex_12_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.neg 6), (Sat.Literal.pos 129)] :=
  (lex_12_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.pos 6), (Sat.Literal.neg 129)] :=
  (lex_12_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.neg 6), (Sat.Literal.neg 129), (Sat.Literal.pos 4921)] :=
  (lex_12_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4920), (Sat.Literal.pos 6), (Sat.Literal.pos 129), (Sat.Literal.pos 4921)] :=
  (lex_12_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4921) = lexBefore s permutation12 5 := by
  exact (positive_lex_of_descriptor s 4921 permutation12 6 (by rfl)).trans ((lex_skipped s permutation12 5 6 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation12 5) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation12 5 by rw [image12_eq]; rfl))

theorem lex_12_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4922) (Sat.Literal.pos 4921) (Sat.Literal.pos 5) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation12 5 (assignment s)
    (Sat.Literal.pos 4922) (Sat.Literal.pos 4921) (Sat.Literal.pos 5) (Sat.Literal.pos 65) (positive_of_descriptor s 4922 (.lex permutation12 5) (by rfl)) (lex_12_5_prefix s) (positive_select s 5) (lex_12_5_image s)

theorem lex_12_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.pos 5), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation12 5 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4921) (Sat.Literal.pos 5) (Sat.Literal.pos 65) (lex_12_5_prefix s) (positive_select s 5) (lex_12_5_image s)

theorem lex_12_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.pos 4921)] :=
  (lex_12_5_gate s).prop _ (List.Mem.head _)

theorem lex_12_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.neg 5), (Sat.Literal.pos 65)] :=
  (lex_12_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.pos 5), (Sat.Literal.neg 65)] :=
  (lex_12_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.neg 5), (Sat.Literal.neg 65), (Sat.Literal.pos 4922)] :=
  (lex_12_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4921), (Sat.Literal.pos 5), (Sat.Literal.pos 65), (Sat.Literal.pos 4922)] :=
  (lex_12_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4922) = lexBefore s permutation12 4 := by
  exact (positive_lex_of_descriptor s 4922 permutation12 5 (by rfl)).trans ((lex_skipped s permutation12 4 5 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation12 4) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation12 4 by rw [image12_eq]; rfl))

theorem lex_12_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4923) (Sat.Literal.pos 4922) (Sat.Literal.pos 4) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation12 4 (assignment s)
    (Sat.Literal.pos 4923) (Sat.Literal.pos 4922) (Sat.Literal.pos 4) (Sat.Literal.pos 1) (positive_of_descriptor s 4923 (.lex permutation12 4) (by rfl)) (lex_12_4_prefix s) (positive_select s 4) (lex_12_4_image s)

theorem lex_12_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.pos 4), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation12 4 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4922) (Sat.Literal.pos 4) (Sat.Literal.pos 1) (lex_12_4_prefix s) (positive_select s 4) (lex_12_4_image s)

theorem lex_12_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.pos 4922)] :=
  (lex_12_4_gate s).prop _ (List.Mem.head _)

theorem lex_12_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.neg 4), (Sat.Literal.pos 1)] :=
  (lex_12_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.pos 4), (Sat.Literal.neg 1)] :=
  (lex_12_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.neg 4), (Sat.Literal.neg 1), (Sat.Literal.pos 4923)] :=
  (lex_12_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4922), (Sat.Literal.pos 4), (Sat.Literal.pos 1), (Sat.Literal.pos 4923)] :=
  (lex_12_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4923) = lexBefore s permutation12 3 := by
  exact (positive_lex_of_descriptor s 4923 permutation12 4 (by rfl)).trans ((lex_skipped s permutation12 3 4 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation12 3) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation12 3 by rw [image12_eq]; rfl))

theorem lex_12_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4924) (Sat.Literal.pos 4923) (Sat.Literal.pos 3) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation12 3 (assignment s)
    (Sat.Literal.pos 4924) (Sat.Literal.pos 4923) (Sat.Literal.pos 3) (Sat.Literal.pos 192) (positive_of_descriptor s 4924 (.lex permutation12 3) (by rfl)) (lex_12_3_prefix s) (positive_select s 3) (lex_12_3_image s)

theorem lex_12_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.pos 3), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation12 3 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4923) (Sat.Literal.pos 3) (Sat.Literal.pos 192) (lex_12_3_prefix s) (positive_select s 3) (lex_12_3_image s)

theorem lex_12_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.pos 4923)] :=
  (lex_12_3_gate s).prop _ (List.Mem.head _)

theorem lex_12_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.neg 3), (Sat.Literal.pos 192)] :=
  (lex_12_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.pos 3), (Sat.Literal.neg 192)] :=
  (lex_12_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.neg 3), (Sat.Literal.neg 192), (Sat.Literal.pos 4924)] :=
  (lex_12_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4923), (Sat.Literal.pos 3), (Sat.Literal.pos 192), (Sat.Literal.pos 4924)] :=
  (lex_12_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_12_103_gate

end Crown.CertificateData
