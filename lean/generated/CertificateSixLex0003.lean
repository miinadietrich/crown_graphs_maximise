import Crown.CertificateSixLexLookup
import Crown.CertificateSixRanges

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly Crown.CertificateSixAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_7_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 791) = lexBefore s permutation7 42 := by
  exact (positive_lex_of_descriptor s 791 permutation7 43 (by rfl)).trans ((lex_skipped s permutation7 42 43 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation7 42) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation7 42 by rw [image7_eq]; rfl))

theorem lex_7_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 792) (Sat.Literal.pos 791) (Sat.Literal.pos 42) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation7 42 (assignment s)
    (Sat.Literal.pos 792) (Sat.Literal.pos 791) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (positive_of_descriptor s 792 (.lex permutation7 42) (by rfl)) (lex_7_42_prefix s) (positive_select s 42) (lex_7_42_image s)

theorem lex_7_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation7 42 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 791) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (lex_7_42_prefix s) (positive_select s 42) (lex_7_42_image s)

theorem lex_7_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.pos 791)] :=
  (lex_7_42_gate s).prop _ (List.Mem.head _)

theorem lex_7_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.neg 42), (Sat.Literal.pos 21)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.neg 42), (Sat.Literal.neg 21), (Sat.Literal.pos 792)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.pos 42), (Sat.Literal.pos 21), (Sat.Literal.pos 792)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 792) = lexBefore s permutation7 41 := by
  exact (positive_lex_of_descriptor s 792 permutation7 42 (by rfl)).trans ((lex_skipped s permutation7 41 42 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation7 41) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation7 41 by rw [image7_eq]; rfl))

theorem lex_7_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 793) (Sat.Literal.pos 792) (Sat.Literal.pos 41) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation7 41 (assignment s)
    (Sat.Literal.pos 793) (Sat.Literal.pos 792) (Sat.Literal.pos 41) (Sat.Literal.pos 13) (positive_of_descriptor s 793 (.lex permutation7 41) (by rfl)) (lex_7_41_prefix s) (positive_select s 41) (lex_7_41_image s)

theorem lex_7_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.pos 41), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation7 41 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 792) (Sat.Literal.pos 41) (Sat.Literal.pos 13) (lex_7_41_prefix s) (positive_select s 41) (lex_7_41_image s)

theorem lex_7_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.pos 792)] :=
  (lex_7_41_gate s).prop _ (List.Mem.head _)

theorem lex_7_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.neg 41), (Sat.Literal.pos 13)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.pos 41), (Sat.Literal.neg 13)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.neg 41), (Sat.Literal.neg 13), (Sat.Literal.pos 793)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 792), (Sat.Literal.pos 41), (Sat.Literal.pos 13), (Sat.Literal.pos 793)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 793) = lexBefore s permutation7 40 := by
  exact (positive_lex_of_descriptor s 793 permutation7 41 (by rfl)).trans ((lex_skipped s permutation7 40 41 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation7 40) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation7 40 by rw [image7_eq]; rfl))

theorem lex_7_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 794) (Sat.Literal.pos 793) (Sat.Literal.pos 40) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation7 40 (assignment s)
    (Sat.Literal.pos 794) (Sat.Literal.pos 793) (Sat.Literal.pos 40) (Sat.Literal.pos 5) (positive_of_descriptor s 794 (.lex permutation7 40) (by rfl)) (lex_7_40_prefix s) (positive_select s 40) (lex_7_40_image s)

theorem lex_7_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.pos 40), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation7 40 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 793) (Sat.Literal.pos 40) (Sat.Literal.pos 5) (lex_7_40_prefix s) (positive_select s 40) (lex_7_40_image s)

theorem lex_7_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.pos 793)] :=
  (lex_7_40_gate s).prop _ (List.Mem.head _)

theorem lex_7_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.neg 40), (Sat.Literal.pos 5)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.pos 40), (Sat.Literal.neg 5)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.neg 40), (Sat.Literal.neg 5), (Sat.Literal.pos 794)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 793), (Sat.Literal.pos 40), (Sat.Literal.pos 5), (Sat.Literal.pos 794)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 794) = lexBefore s permutation7 39 := by
  exact (positive_lex_of_descriptor s 794 permutation7 40 (by rfl)).trans ((lex_skipped s permutation7 39 40 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation7 39) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 64) = permuteMask permutation7 39 by rw [image7_eq]; rfl))

theorem lex_7_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 795) (Sat.Literal.pos 794) (Sat.Literal.pos 39) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation7 39 (assignment s)
    (Sat.Literal.pos 795) (Sat.Literal.pos 794) (Sat.Literal.pos 39) (Sat.Literal.pos 60) (positive_of_descriptor s 795 (.lex permutation7 39) (by rfl)) (lex_7_39_prefix s) (positive_select s 39) (lex_7_39_image s)

theorem lex_7_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.pos 39), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation7 39 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 794) (Sat.Literal.pos 39) (Sat.Literal.pos 60) (lex_7_39_prefix s) (positive_select s 39) (lex_7_39_image s)

theorem lex_7_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.pos 794)] :=
  (lex_7_39_gate s).prop _ (List.Mem.head _)

theorem lex_7_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.neg 39), (Sat.Literal.pos 60)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.pos 39), (Sat.Literal.neg 60)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.neg 39), (Sat.Literal.neg 60), (Sat.Literal.pos 795)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 794), (Sat.Literal.pos 39), (Sat.Literal.pos 60), (Sat.Literal.pos 795)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 795) = lexBefore s permutation7 38 := by
  exact (positive_lex_of_descriptor s 795 permutation7 39 (by rfl)).trans ((lex_skipped s permutation7 38 39 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation7 38) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation7 38 by rw [image7_eq]; rfl))

theorem lex_7_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 796) (Sat.Literal.pos 795) (Sat.Literal.pos 38) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation7 38 (assignment s)
    (Sat.Literal.pos 796) (Sat.Literal.pos 795) (Sat.Literal.pos 38) (Sat.Literal.pos 52) (positive_of_descriptor s 796 (.lex permutation7 38) (by rfl)) (lex_7_38_prefix s) (positive_select s 38) (lex_7_38_image s)

theorem lex_7_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.pos 38), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation7 38 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 795) (Sat.Literal.pos 38) (Sat.Literal.pos 52) (lex_7_38_prefix s) (positive_select s 38) (lex_7_38_image s)

theorem lex_7_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.pos 795)] :=
  (lex_7_38_gate s).prop _ (List.Mem.head _)

theorem lex_7_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.neg 38), (Sat.Literal.pos 52)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.pos 38), (Sat.Literal.neg 52)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.neg 38), (Sat.Literal.neg 52), (Sat.Literal.pos 796)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 795), (Sat.Literal.pos 38), (Sat.Literal.pos 52), (Sat.Literal.pos 796)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 796) = lexBefore s permutation7 37 := by
  exact (positive_lex_of_descriptor s 796 permutation7 38 (by rfl)).trans ((lex_skipped s permutation7 37 38 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation7 37) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation7 37 by rw [image7_eq]; rfl))

theorem lex_7_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 797) (Sat.Literal.pos 796) (Sat.Literal.pos 37) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation7 37 (assignment s)
    (Sat.Literal.pos 797) (Sat.Literal.pos 796) (Sat.Literal.pos 37) (Sat.Literal.pos 44) (positive_of_descriptor s 797 (.lex permutation7 37) (by rfl)) (lex_7_37_prefix s) (positive_select s 37) (lex_7_37_image s)

theorem lex_7_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.pos 37), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation7 37 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 796) (Sat.Literal.pos 37) (Sat.Literal.pos 44) (lex_7_37_prefix s) (positive_select s 37) (lex_7_37_image s)

theorem lex_7_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.pos 796)] :=
  (lex_7_37_gate s).prop _ (List.Mem.head _)

theorem lex_7_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.neg 37), (Sat.Literal.pos 44)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.pos 37), (Sat.Literal.neg 44)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.neg 37), (Sat.Literal.neg 44), (Sat.Literal.pos 797)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 796), (Sat.Literal.pos 37), (Sat.Literal.pos 44), (Sat.Literal.pos 797)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 797) = lexBefore s permutation7 35 := by
  exact (positive_lex_of_descriptor s 797 permutation7 37 (by rfl)).trans ((lex_skipped s permutation7 35 37 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 36 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation7 35) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation7 35 by rw [image7_eq]; rfl))

theorem lex_7_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 798) (Sat.Literal.pos 797) (Sat.Literal.pos 35) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation7 35 (assignment s)
    (Sat.Literal.pos 798) (Sat.Literal.pos 797) (Sat.Literal.pos 35) (Sat.Literal.pos 28) (positive_of_descriptor s 798 (.lex permutation7 35) (by rfl)) (lex_7_35_prefix s) (positive_select s 35) (lex_7_35_image s)

theorem lex_7_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.pos 35), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation7 35 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 797) (Sat.Literal.pos 35) (Sat.Literal.pos 28) (lex_7_35_prefix s) (positive_select s 35) (lex_7_35_image s)

theorem lex_7_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.pos 797)] :=
  (lex_7_35_gate s).prop _ (List.Mem.head _)

theorem lex_7_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.neg 35), (Sat.Literal.pos 28)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.pos 35), (Sat.Literal.neg 28)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.neg 35), (Sat.Literal.neg 28), (Sat.Literal.pos 798)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 797), (Sat.Literal.pos 35), (Sat.Literal.pos 28), (Sat.Literal.pos 798)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 798) = lexBefore s permutation7 34 := by
  exact (positive_lex_of_descriptor s 798 permutation7 35 (by rfl)).trans ((lex_skipped s permutation7 34 35 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation7 34) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation7 34 by rw [image7_eq]; rfl))

theorem lex_7_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 799) (Sat.Literal.pos 798) (Sat.Literal.pos 34) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation7 34 (assignment s)
    (Sat.Literal.pos 799) (Sat.Literal.pos 798) (Sat.Literal.pos 34) (Sat.Literal.pos 20) (positive_of_descriptor s 799 (.lex permutation7 34) (by rfl)) (lex_7_34_prefix s) (positive_select s 34) (lex_7_34_image s)

theorem lex_7_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.pos 34), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation7 34 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 798) (Sat.Literal.pos 34) (Sat.Literal.pos 20) (lex_7_34_prefix s) (positive_select s 34) (lex_7_34_image s)

theorem lex_7_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.pos 798)] :=
  (lex_7_34_gate s).prop _ (List.Mem.head _)

theorem lex_7_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.neg 34), (Sat.Literal.pos 20)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.pos 34), (Sat.Literal.neg 20)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.neg 34), (Sat.Literal.neg 20), (Sat.Literal.pos 799)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 798), (Sat.Literal.pos 34), (Sat.Literal.pos 20), (Sat.Literal.pos 799)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 799) = lexBefore s permutation7 33 := by
  exact (positive_lex_of_descriptor s 799 permutation7 34 (by rfl)).trans ((lex_skipped s permutation7 33 34 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation7 33) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation7 33 by rw [image7_eq]; rfl))

theorem lex_7_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 800) (Sat.Literal.pos 799) (Sat.Literal.pos 33) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation7 33 (assignment s)
    (Sat.Literal.pos 800) (Sat.Literal.pos 799) (Sat.Literal.pos 33) (Sat.Literal.pos 12) (positive_of_descriptor s 800 (.lex permutation7 33) (by rfl)) (lex_7_33_prefix s) (positive_select s 33) (lex_7_33_image s)

theorem lex_7_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.pos 33), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation7 33 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 799) (Sat.Literal.pos 33) (Sat.Literal.pos 12) (lex_7_33_prefix s) (positive_select s 33) (lex_7_33_image s)

theorem lex_7_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.pos 799)] :=
  (lex_7_33_gate s).prop _ (List.Mem.head _)

theorem lex_7_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.neg 33), (Sat.Literal.pos 12)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.pos 33), (Sat.Literal.neg 12)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.neg 33), (Sat.Literal.neg 12), (Sat.Literal.pos 800)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 799), (Sat.Literal.pos 33), (Sat.Literal.pos 12), (Sat.Literal.pos 800)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_32_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 800) = lexBefore s permutation7 32 := by
  exact (positive_lex_of_descriptor s 800 permutation7 33 (by rfl)).trans ((lex_skipped s permutation7 32 33 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_32_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation7 32) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation7 32 by rw [image7_eq]; rfl))

theorem lex_7_32_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 801) (Sat.Literal.pos 800) (Sat.Literal.pos 32) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation7 32 (assignment s)
    (Sat.Literal.pos 801) (Sat.Literal.pos 800) (Sat.Literal.pos 32) (Sat.Literal.pos 4) (positive_of_descriptor s 801 (.lex permutation7 32) (by rfl)) (lex_7_32_prefix s) (positive_select s 32) (lex_7_32_image s)

theorem lex_7_32_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.pos 32), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation7 32 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 800) (Sat.Literal.pos 32) (Sat.Literal.pos 4) (lex_7_32_prefix s) (positive_select s 32) (lex_7_32_image s)

theorem lex_7_32_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.pos 800)] :=
  (lex_7_32_gate s).prop _ (List.Mem.head _)

theorem lex_7_32_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.neg 32), (Sat.Literal.pos 4)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_32_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.pos 32), (Sat.Literal.neg 4)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_32_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.neg 32), (Sat.Literal.neg 4), (Sat.Literal.pos 801)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_32_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 800), (Sat.Literal.pos 32), (Sat.Literal.pos 4), (Sat.Literal.pos 801)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_31_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 801) = lexBefore s permutation7 31 := by
  exact (positive_lex_of_descriptor s 801 permutation7 32 (by rfl)).trans ((lex_skipped s permutation7 31 32 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_31_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation7 31) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation7 31 by rw [image7_eq]; rfl))

theorem lex_7_31_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 802) (Sat.Literal.pos 801) (Sat.Literal.pos 31) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation7 31 (assignment s)
    (Sat.Literal.pos 802) (Sat.Literal.pos 801) (Sat.Literal.pos 31) (Sat.Literal.pos 59) (positive_of_descriptor s 802 (.lex permutation7 31) (by rfl)) (lex_7_31_prefix s) (positive_select s 31) (lex_7_31_image s)

theorem lex_7_31_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.pos 31), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation7 31 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 801) (Sat.Literal.pos 31) (Sat.Literal.pos 59) (lex_7_31_prefix s) (positive_select s 31) (lex_7_31_image s)

theorem lex_7_31_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.pos 801)] :=
  (lex_7_31_gate s).prop _ (List.Mem.head _)

theorem lex_7_31_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.neg 31), (Sat.Literal.pos 59)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_31_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.pos 31), (Sat.Literal.neg 59)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_31_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.neg 31), (Sat.Literal.neg 59), (Sat.Literal.pos 802)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_31_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 801), (Sat.Literal.pos 31), (Sat.Literal.pos 59), (Sat.Literal.pos 802)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 802) = lexBefore s permutation7 30 := by
  exact (positive_lex_of_descriptor s 802 permutation7 31 (by rfl)).trans ((lex_skipped s permutation7 30 31 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation7 30) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation7 30 by rw [image7_eq]; rfl))

theorem lex_7_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 803) (Sat.Literal.pos 802) (Sat.Literal.pos 30) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation7 30 (assignment s)
    (Sat.Literal.pos 803) (Sat.Literal.pos 802) (Sat.Literal.pos 30) (Sat.Literal.pos 51) (positive_of_descriptor s 803 (.lex permutation7 30) (by rfl)) (lex_7_30_prefix s) (positive_select s 30) (lex_7_30_image s)

theorem lex_7_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.pos 30), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation7 30 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 802) (Sat.Literal.pos 30) (Sat.Literal.pos 51) (lex_7_30_prefix s) (positive_select s 30) (lex_7_30_image s)

theorem lex_7_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.pos 802)] :=
  (lex_7_30_gate s).prop _ (List.Mem.head _)

theorem lex_7_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.neg 30), (Sat.Literal.pos 51)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.pos 30), (Sat.Literal.neg 51)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.neg 30), (Sat.Literal.neg 51), (Sat.Literal.pos 803)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 802), (Sat.Literal.pos 30), (Sat.Literal.pos 51), (Sat.Literal.pos 803)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 803) = lexBefore s permutation7 29 := by
  exact (positive_lex_of_descriptor s 803 permutation7 30 (by rfl)).trans ((lex_skipped s permutation7 29 30 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation7 29) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation7 29 by rw [image7_eq]; rfl))

theorem lex_7_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 804) (Sat.Literal.pos 803) (Sat.Literal.pos 29) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation7 29 (assignment s)
    (Sat.Literal.pos 804) (Sat.Literal.pos 803) (Sat.Literal.pos 29) (Sat.Literal.pos 43) (positive_of_descriptor s 804 (.lex permutation7 29) (by rfl)) (lex_7_29_prefix s) (positive_select s 29) (lex_7_29_image s)

theorem lex_7_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.pos 29), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation7 29 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 803) (Sat.Literal.pos 29) (Sat.Literal.pos 43) (lex_7_29_prefix s) (positive_select s 29) (lex_7_29_image s)

theorem lex_7_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.pos 803)] :=
  (lex_7_29_gate s).prop _ (List.Mem.head _)

theorem lex_7_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.neg 29), (Sat.Literal.pos 43)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.pos 29), (Sat.Literal.neg 43)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.neg 29), (Sat.Literal.neg 43), (Sat.Literal.pos 804)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 803), (Sat.Literal.pos 29), (Sat.Literal.pos 43), (Sat.Literal.pos 804)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 804) = lexBefore s permutation7 28 := by
  exact (positive_lex_of_descriptor s 804 permutation7 29 (by rfl)).trans ((lex_skipped s permutation7 28 29 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation7 28) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation7 28 by rw [image7_eq]; rfl))

theorem lex_7_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 805) (Sat.Literal.pos 804) (Sat.Literal.pos 28) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation7 28 (assignment s)
    (Sat.Literal.pos 805) (Sat.Literal.pos 804) (Sat.Literal.pos 28) (Sat.Literal.pos 35) (positive_of_descriptor s 805 (.lex permutation7 28) (by rfl)) (lex_7_28_prefix s) (positive_select s 28) (lex_7_28_image s)

theorem lex_7_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.pos 28), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation7 28 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 804) (Sat.Literal.pos 28) (Sat.Literal.pos 35) (lex_7_28_prefix s) (positive_select s 28) (lex_7_28_image s)

theorem lex_7_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.pos 804)] :=
  (lex_7_28_gate s).prop _ (List.Mem.head _)

theorem lex_7_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.neg 28), (Sat.Literal.pos 35)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.pos 28), (Sat.Literal.neg 35)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.neg 28), (Sat.Literal.neg 35), (Sat.Literal.pos 805)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 804), (Sat.Literal.pos 28), (Sat.Literal.pos 35), (Sat.Literal.pos 805)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 805) = lexBefore s permutation7 26 := by
  exact (positive_lex_of_descriptor s 805 permutation7 28 (by rfl)).trans ((lex_skipped s permutation7 26 28 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 27 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation7 26) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation7 26 by rw [image7_eq]; rfl))

theorem lex_7_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 806) (Sat.Literal.pos 805) (Sat.Literal.pos 26) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation7 26 (assignment s)
    (Sat.Literal.pos 806) (Sat.Literal.pos 805) (Sat.Literal.pos 26) (Sat.Literal.pos 19) (positive_of_descriptor s 806 (.lex permutation7 26) (by rfl)) (lex_7_26_prefix s) (positive_select s 26) (lex_7_26_image s)

theorem lex_7_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.pos 26), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation7 26 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 805) (Sat.Literal.pos 26) (Sat.Literal.pos 19) (lex_7_26_prefix s) (positive_select s 26) (lex_7_26_image s)

theorem lex_7_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.pos 805)] :=
  (lex_7_26_gate s).prop _ (List.Mem.head _)

theorem lex_7_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.neg 26), (Sat.Literal.pos 19)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.pos 26), (Sat.Literal.neg 19)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.neg 26), (Sat.Literal.neg 19), (Sat.Literal.pos 806)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 805), (Sat.Literal.pos 26), (Sat.Literal.pos 19), (Sat.Literal.pos 806)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 806) = lexBefore s permutation7 25 := by
  exact (positive_lex_of_descriptor s 806 permutation7 26 (by rfl)).trans ((lex_skipped s permutation7 25 26 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation7 25) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation7 25 by rw [image7_eq]; rfl))

theorem lex_7_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 807) (Sat.Literal.pos 806) (Sat.Literal.pos 25) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation7 25 (assignment s)
    (Sat.Literal.pos 807) (Sat.Literal.pos 806) (Sat.Literal.pos 25) (Sat.Literal.pos 11) (positive_of_descriptor s 807 (.lex permutation7 25) (by rfl)) (lex_7_25_prefix s) (positive_select s 25) (lex_7_25_image s)

theorem lex_7_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.pos 25), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation7 25 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 806) (Sat.Literal.pos 25) (Sat.Literal.pos 11) (lex_7_25_prefix s) (positive_select s 25) (lex_7_25_image s)

theorem lex_7_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.pos 806)] :=
  (lex_7_25_gate s).prop _ (List.Mem.head _)

theorem lex_7_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.neg 25), (Sat.Literal.pos 11)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.pos 25), (Sat.Literal.neg 11)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.neg 25), (Sat.Literal.neg 11), (Sat.Literal.pos 807)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 806), (Sat.Literal.pos 25), (Sat.Literal.pos 11), (Sat.Literal.pos 807)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 807) = lexBefore s permutation7 24 := by
  exact (positive_lex_of_descriptor s 807 permutation7 25 (by rfl)).trans ((lex_skipped s permutation7 24 25 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation7 24) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 64) = permuteMask permutation7 24 by rw [image7_eq]; rfl))

theorem lex_7_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 808) (Sat.Literal.pos 807) (Sat.Literal.pos 24) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation7 24 (assignment s)
    (Sat.Literal.pos 808) (Sat.Literal.pos 807) (Sat.Literal.pos 24) (Sat.Literal.pos 3) (positive_of_descriptor s 808 (.lex permutation7 24) (by rfl)) (lex_7_24_prefix s) (positive_select s 24) (lex_7_24_image s)

theorem lex_7_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.pos 24), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation7 24 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 807) (Sat.Literal.pos 24) (Sat.Literal.pos 3) (lex_7_24_prefix s) (positive_select s 24) (lex_7_24_image s)

theorem lex_7_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.pos 807)] :=
  (lex_7_24_gate s).prop _ (List.Mem.head _)

theorem lex_7_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.neg 24), (Sat.Literal.pos 3)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.pos 24), (Sat.Literal.neg 3)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.neg 24), (Sat.Literal.neg 3), (Sat.Literal.pos 808)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 807), (Sat.Literal.pos 24), (Sat.Literal.pos 3), (Sat.Literal.pos 808)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 808) = lexBefore s permutation7 23 := by
  exact (positive_lex_of_descriptor s 808 permutation7 24 (by rfl)).trans ((lex_skipped s permutation7 23 24 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation7 23) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation7 23 by rw [image7_eq]; rfl))

theorem lex_7_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 809) (Sat.Literal.pos 808) (Sat.Literal.pos 23) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation7 23 (assignment s)
    (Sat.Literal.pos 809) (Sat.Literal.pos 808) (Sat.Literal.pos 23) (Sat.Literal.pos 58) (positive_of_descriptor s 809 (.lex permutation7 23) (by rfl)) (lex_7_23_prefix s) (positive_select s 23) (lex_7_23_image s)

theorem lex_7_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.pos 23), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation7 23 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 808) (Sat.Literal.pos 23) (Sat.Literal.pos 58) (lex_7_23_prefix s) (positive_select s 23) (lex_7_23_image s)

theorem lex_7_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.pos 808)] :=
  (lex_7_23_gate s).prop _ (List.Mem.head _)

theorem lex_7_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.neg 23), (Sat.Literal.pos 58)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.pos 23), (Sat.Literal.neg 58)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.neg 23), (Sat.Literal.neg 58), (Sat.Literal.pos 809)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 808), (Sat.Literal.pos 23), (Sat.Literal.pos 58), (Sat.Literal.pos 809)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 809) = lexBefore s permutation7 22 := by
  exact (positive_lex_of_descriptor s 809 permutation7 23 (by rfl)).trans ((lex_skipped s permutation7 22 23 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation7 22) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation7 22 by rw [image7_eq]; rfl))

theorem lex_7_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 810) (Sat.Literal.pos 809) (Sat.Literal.pos 22) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation7 22 (assignment s)
    (Sat.Literal.pos 810) (Sat.Literal.pos 809) (Sat.Literal.pos 22) (Sat.Literal.pos 50) (positive_of_descriptor s 810 (.lex permutation7 22) (by rfl)) (lex_7_22_prefix s) (positive_select s 22) (lex_7_22_image s)

theorem lex_7_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.pos 22), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation7 22 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 809) (Sat.Literal.pos 22) (Sat.Literal.pos 50) (lex_7_22_prefix s) (positive_select s 22) (lex_7_22_image s)

theorem lex_7_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.pos 809)] :=
  (lex_7_22_gate s).prop _ (List.Mem.head _)

theorem lex_7_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.neg 22), (Sat.Literal.pos 50)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.pos 22), (Sat.Literal.neg 50)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.neg 22), (Sat.Literal.neg 50), (Sat.Literal.pos 810)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 809), (Sat.Literal.pos 22), (Sat.Literal.pos 50), (Sat.Literal.pos 810)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 810) = lexBefore s permutation7 21 := by
  exact (positive_lex_of_descriptor s 810 permutation7 22 (by rfl)).trans ((lex_skipped s permutation7 21 22 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation7 21) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation7 21 by rw [image7_eq]; rfl))

theorem lex_7_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 811) (Sat.Literal.pos 810) (Sat.Literal.pos 21) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation7 21 (assignment s)
    (Sat.Literal.pos 811) (Sat.Literal.pos 810) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (positive_of_descriptor s 811 (.lex permutation7 21) (by rfl)) (lex_7_21_prefix s) (positive_select s 21) (lex_7_21_image s)

theorem lex_7_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation7 21 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 810) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (lex_7_21_prefix s) (positive_select s 21) (lex_7_21_image s)

theorem lex_7_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.pos 810)] :=
  (lex_7_21_gate s).prop _ (List.Mem.head _)

theorem lex_7_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.neg 21), (Sat.Literal.pos 42)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.neg 21), (Sat.Literal.neg 42), (Sat.Literal.pos 811)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 810), (Sat.Literal.pos 21), (Sat.Literal.pos 42), (Sat.Literal.pos 811)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 811) = lexBefore s permutation7 20 := by
  exact (positive_lex_of_descriptor s 811 permutation7 21 (by rfl)).trans ((lex_skipped s permutation7 20 21 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation7 20) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation7 20 by rw [image7_eq]; rfl))

theorem lex_7_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 812) (Sat.Literal.pos 811) (Sat.Literal.pos 20) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation7 20 (assignment s)
    (Sat.Literal.pos 812) (Sat.Literal.pos 811) (Sat.Literal.pos 20) (Sat.Literal.pos 34) (positive_of_descriptor s 812 (.lex permutation7 20) (by rfl)) (lex_7_20_prefix s) (positive_select s 20) (lex_7_20_image s)

theorem lex_7_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.pos 20), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation7 20 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 811) (Sat.Literal.pos 20) (Sat.Literal.pos 34) (lex_7_20_prefix s) (positive_select s 20) (lex_7_20_image s)

theorem lex_7_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.pos 811)] :=
  (lex_7_20_gate s).prop _ (List.Mem.head _)

theorem lex_7_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.neg 20), (Sat.Literal.pos 34)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.pos 20), (Sat.Literal.neg 34)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.neg 20), (Sat.Literal.neg 34), (Sat.Literal.pos 812)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 811), (Sat.Literal.pos 20), (Sat.Literal.pos 34), (Sat.Literal.pos 812)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 812) = lexBefore s permutation7 19 := by
  exact (positive_lex_of_descriptor s 812 permutation7 20 (by rfl)).trans ((lex_skipped s permutation7 19 20 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation7 19) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation7 19 by rw [image7_eq]; rfl))

theorem lex_7_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 813) (Sat.Literal.pos 812) (Sat.Literal.pos 19) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation7 19 (assignment s)
    (Sat.Literal.pos 813) (Sat.Literal.pos 812) (Sat.Literal.pos 19) (Sat.Literal.pos 26) (positive_of_descriptor s 813 (.lex permutation7 19) (by rfl)) (lex_7_19_prefix s) (positive_select s 19) (lex_7_19_image s)

theorem lex_7_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.pos 19), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation7 19 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 812) (Sat.Literal.pos 19) (Sat.Literal.pos 26) (lex_7_19_prefix s) (positive_select s 19) (lex_7_19_image s)

theorem lex_7_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.pos 812)] :=
  (lex_7_19_gate s).prop _ (List.Mem.head _)

theorem lex_7_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.neg 19), (Sat.Literal.pos 26)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.pos 19), (Sat.Literal.neg 26)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.neg 19), (Sat.Literal.neg 26), (Sat.Literal.pos 813)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 812), (Sat.Literal.pos 19), (Sat.Literal.pos 26), (Sat.Literal.pos 813)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 813) = lexBefore s permutation7 17 := by
  exact (positive_lex_of_descriptor s 813 permutation7 19 (by rfl)).trans ((lex_skipped s permutation7 17 19 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 18 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation7 17) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation7 17 by rw [image7_eq]; rfl))

theorem lex_7_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 814) (Sat.Literal.pos 813) (Sat.Literal.pos 17) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation7 17 (assignment s)
    (Sat.Literal.pos 814) (Sat.Literal.pos 813) (Sat.Literal.pos 17) (Sat.Literal.pos 10) (positive_of_descriptor s 814 (.lex permutation7 17) (by rfl)) (lex_7_17_prefix s) (positive_select s 17) (lex_7_17_image s)

theorem lex_7_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.pos 17), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation7 17 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 813) (Sat.Literal.pos 17) (Sat.Literal.pos 10) (lex_7_17_prefix s) (positive_select s 17) (lex_7_17_image s)

theorem lex_7_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.pos 813)] :=
  (lex_7_17_gate s).prop _ (List.Mem.head _)

theorem lex_7_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.neg 17), (Sat.Literal.pos 10)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.pos 17), (Sat.Literal.neg 10)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.neg 17), (Sat.Literal.neg 10), (Sat.Literal.pos 814)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 813), (Sat.Literal.pos 17), (Sat.Literal.pos 10), (Sat.Literal.pos 814)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 814) = lexBefore s permutation7 16 := by
  exact (positive_lex_of_descriptor s 814 permutation7 17 (by rfl)).trans ((lex_skipped s permutation7 16 17 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation7 16) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation7 16 by rw [image7_eq]; rfl))

theorem lex_7_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 815) (Sat.Literal.pos 814) (Sat.Literal.pos 16) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation7 16 (assignment s)
    (Sat.Literal.pos 815) (Sat.Literal.pos 814) (Sat.Literal.pos 16) (Sat.Literal.pos 2) (positive_of_descriptor s 815 (.lex permutation7 16) (by rfl)) (lex_7_16_prefix s) (positive_select s 16) (lex_7_16_image s)

theorem lex_7_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.pos 16), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation7 16 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 814) (Sat.Literal.pos 16) (Sat.Literal.pos 2) (lex_7_16_prefix s) (positive_select s 16) (lex_7_16_image s)

theorem lex_7_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.pos 814)] :=
  (lex_7_16_gate s).prop _ (List.Mem.head _)

theorem lex_7_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.neg 16), (Sat.Literal.pos 2)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.pos 16), (Sat.Literal.neg 2)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.neg 16), (Sat.Literal.neg 2), (Sat.Literal.pos 815)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 814), (Sat.Literal.pos 16), (Sat.Literal.pos 2), (Sat.Literal.pos 815)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_15_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 815) = lexBefore s permutation7 15 := by
  exact (positive_lex_of_descriptor s 815 permutation7 16 (by rfl)).trans ((lex_skipped s permutation7 15 16 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_15_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation7 15) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation7 15 by rw [image7_eq]; rfl))

theorem lex_7_15_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 816) (Sat.Literal.pos 815) (Sat.Literal.pos 15) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation7 15 (assignment s)
    (Sat.Literal.pos 816) (Sat.Literal.pos 815) (Sat.Literal.pos 15) (Sat.Literal.pos 57) (positive_of_descriptor s 816 (.lex permutation7 15) (by rfl)) (lex_7_15_prefix s) (positive_select s 15) (lex_7_15_image s)

theorem lex_7_15_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.pos 15), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation7 15 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 815) (Sat.Literal.pos 15) (Sat.Literal.pos 57) (lex_7_15_prefix s) (positive_select s 15) (lex_7_15_image s)

theorem lex_7_15_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.pos 815)] :=
  (lex_7_15_gate s).prop _ (List.Mem.head _)

theorem lex_7_15_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.neg 15), (Sat.Literal.pos 57)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_15_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.pos 15), (Sat.Literal.neg 57)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_15_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.neg 15), (Sat.Literal.neg 57), (Sat.Literal.pos 816)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_15_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 815), (Sat.Literal.pos 15), (Sat.Literal.pos 57), (Sat.Literal.pos 816)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 816) = lexBefore s permutation7 14 := by
  exact (positive_lex_of_descriptor s 816 permutation7 15 (by rfl)).trans ((lex_skipped s permutation7 14 15 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation7 14) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation7 14 by rw [image7_eq]; rfl))

theorem lex_7_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 817) (Sat.Literal.pos 816) (Sat.Literal.pos 14) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation7 14 (assignment s)
    (Sat.Literal.pos 817) (Sat.Literal.pos 816) (Sat.Literal.pos 14) (Sat.Literal.pos 49) (positive_of_descriptor s 817 (.lex permutation7 14) (by rfl)) (lex_7_14_prefix s) (positive_select s 14) (lex_7_14_image s)

theorem lex_7_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.pos 14), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation7 14 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 816) (Sat.Literal.pos 14) (Sat.Literal.pos 49) (lex_7_14_prefix s) (positive_select s 14) (lex_7_14_image s)

theorem lex_7_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.pos 816)] :=
  (lex_7_14_gate s).prop _ (List.Mem.head _)

theorem lex_7_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.neg 14), (Sat.Literal.pos 49)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.pos 14), (Sat.Literal.neg 49)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.neg 14), (Sat.Literal.neg 49), (Sat.Literal.pos 817)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 816), (Sat.Literal.pos 14), (Sat.Literal.pos 49), (Sat.Literal.pos 817)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 817) = lexBefore s permutation7 13 := by
  exact (positive_lex_of_descriptor s 817 permutation7 14 (by rfl)).trans ((lex_skipped s permutation7 13 14 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation7 13) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation7 13 by rw [image7_eq]; rfl))

theorem lex_7_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 818) (Sat.Literal.pos 817) (Sat.Literal.pos 13) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation7 13 (assignment s)
    (Sat.Literal.pos 818) (Sat.Literal.pos 817) (Sat.Literal.pos 13) (Sat.Literal.pos 41) (positive_of_descriptor s 818 (.lex permutation7 13) (by rfl)) (lex_7_13_prefix s) (positive_select s 13) (lex_7_13_image s)

theorem lex_7_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.pos 13), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation7 13 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 817) (Sat.Literal.pos 13) (Sat.Literal.pos 41) (lex_7_13_prefix s) (positive_select s 13) (lex_7_13_image s)

theorem lex_7_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.pos 817)] :=
  (lex_7_13_gate s).prop _ (List.Mem.head _)

theorem lex_7_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.neg 13), (Sat.Literal.pos 41)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.pos 13), (Sat.Literal.neg 41)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.neg 13), (Sat.Literal.neg 41), (Sat.Literal.pos 818)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 817), (Sat.Literal.pos 13), (Sat.Literal.pos 41), (Sat.Literal.pos 818)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 818) = lexBefore s permutation7 12 := by
  exact (positive_lex_of_descriptor s 818 permutation7 13 (by rfl)).trans ((lex_skipped s permutation7 12 13 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation7 12) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation7 12 by rw [image7_eq]; rfl))

theorem lex_7_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 819) (Sat.Literal.pos 818) (Sat.Literal.pos 12) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation7 12 (assignment s)
    (Sat.Literal.pos 819) (Sat.Literal.pos 818) (Sat.Literal.pos 12) (Sat.Literal.pos 33) (positive_of_descriptor s 819 (.lex permutation7 12) (by rfl)) (lex_7_12_prefix s) (positive_select s 12) (lex_7_12_image s)

theorem lex_7_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.pos 12), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation7 12 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 818) (Sat.Literal.pos 12) (Sat.Literal.pos 33) (lex_7_12_prefix s) (positive_select s 12) (lex_7_12_image s)

theorem lex_7_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.pos 818)] :=
  (lex_7_12_gate s).prop _ (List.Mem.head _)

theorem lex_7_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.neg 12), (Sat.Literal.pos 33)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.pos 12), (Sat.Literal.neg 33)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.neg 12), (Sat.Literal.neg 33), (Sat.Literal.pos 819)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 818), (Sat.Literal.pos 12), (Sat.Literal.pos 33), (Sat.Literal.pos 819)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 819) = lexBefore s permutation7 11 := by
  exact (positive_lex_of_descriptor s 819 permutation7 12 (by rfl)).trans ((lex_skipped s permutation7 11 12 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation7 11) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation7 11 by rw [image7_eq]; rfl))

theorem lex_7_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 820) (Sat.Literal.pos 819) (Sat.Literal.pos 11) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation7 11 (assignment s)
    (Sat.Literal.pos 820) (Sat.Literal.pos 819) (Sat.Literal.pos 11) (Sat.Literal.pos 25) (positive_of_descriptor s 820 (.lex permutation7 11) (by rfl)) (lex_7_11_prefix s) (positive_select s 11) (lex_7_11_image s)

theorem lex_7_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.pos 11), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation7 11 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 819) (Sat.Literal.pos 11) (Sat.Literal.pos 25) (lex_7_11_prefix s) (positive_select s 11) (lex_7_11_image s)

theorem lex_7_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.pos 819)] :=
  (lex_7_11_gate s).prop _ (List.Mem.head _)

theorem lex_7_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.neg 11), (Sat.Literal.pos 25)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.pos 11), (Sat.Literal.neg 25)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.neg 11), (Sat.Literal.neg 25), (Sat.Literal.pos 820)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 819), (Sat.Literal.pos 11), (Sat.Literal.pos 25), (Sat.Literal.pos 820)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 820) = lexBefore s permutation7 10 := by
  exact (positive_lex_of_descriptor s 820 permutation7 11 (by rfl)).trans ((lex_skipped s permutation7 10 11 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation7 10) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation7 10 by rw [image7_eq]; rfl))

theorem lex_7_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 821) (Sat.Literal.pos 820) (Sat.Literal.pos 10) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation7 10 (assignment s)
    (Sat.Literal.pos 821) (Sat.Literal.pos 820) (Sat.Literal.pos 10) (Sat.Literal.pos 17) (positive_of_descriptor s 821 (.lex permutation7 10) (by rfl)) (lex_7_10_prefix s) (positive_select s 10) (lex_7_10_image s)

theorem lex_7_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.pos 10), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation7 10 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 820) (Sat.Literal.pos 10) (Sat.Literal.pos 17) (lex_7_10_prefix s) (positive_select s 10) (lex_7_10_image s)

theorem lex_7_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.pos 820)] :=
  (lex_7_10_gate s).prop _ (List.Mem.head _)

theorem lex_7_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.neg 10), (Sat.Literal.pos 17)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.pos 10), (Sat.Literal.neg 17)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.neg 10), (Sat.Literal.neg 17), (Sat.Literal.pos 821)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 820), (Sat.Literal.pos 10), (Sat.Literal.pos 17), (Sat.Literal.pos 821)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 821) = lexBefore s permutation7 8 := by
  exact (positive_lex_of_descriptor s 821 permutation7 10 (by rfl)).trans ((lex_skipped s permutation7 8 10 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 9 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation7 8) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 64) = permuteMask permutation7 8 by rw [image7_eq]; rfl))

theorem lex_7_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 822) (Sat.Literal.pos 821) (Sat.Literal.pos 8) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation7 8 (assignment s)
    (Sat.Literal.pos 822) (Sat.Literal.pos 821) (Sat.Literal.pos 8) (Sat.Literal.pos 1) (positive_of_descriptor s 822 (.lex permutation7 8) (by rfl)) (lex_7_8_prefix s) (positive_select s 8) (lex_7_8_image s)

theorem lex_7_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.pos 8), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation7 8 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 821) (Sat.Literal.pos 8) (Sat.Literal.pos 1) (lex_7_8_prefix s) (positive_select s 8) (lex_7_8_image s)

theorem lex_7_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.pos 821)] :=
  (lex_7_8_gate s).prop _ (List.Mem.head _)

theorem lex_7_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.neg 8), (Sat.Literal.pos 1)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.pos 8), (Sat.Literal.neg 1)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.neg 8), (Sat.Literal.neg 1), (Sat.Literal.pos 822)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 821), (Sat.Literal.pos 8), (Sat.Literal.pos 1), (Sat.Literal.pos 822)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_7_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 822) = lexBefore s permutation7 7 := by
  exact (positive_lex_of_descriptor s 822 permutation7 8 (by rfl)).trans ((lex_skipped s permutation7 7 8 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_7_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation7 7) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 64) = permuteMask permutation7 7 by rw [image7_eq]; rfl))

theorem lex_7_7_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 823) (Sat.Literal.pos 822) (Sat.Literal.pos 7) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation7 7 (assignment s)
    (Sat.Literal.pos 823) (Sat.Literal.pos 822) (Sat.Literal.pos 7) (Sat.Literal.pos 56) (positive_of_descriptor s 823 (.lex permutation7 7) (by rfl)) (lex_7_7_prefix s) (positive_select s 7) (lex_7_7_image s)

theorem lex_7_7_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.pos 7), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation7 7 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 822) (Sat.Literal.pos 7) (Sat.Literal.pos 56) (lex_7_7_prefix s) (positive_select s 7) (lex_7_7_image s)

theorem lex_7_7_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.pos 822)] :=
  (lex_7_7_gate s).prop _ (List.Mem.head _)

theorem lex_7_7_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.neg 7), (Sat.Literal.pos 56)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_7_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.pos 7), (Sat.Literal.neg 56)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_7_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.neg 7), (Sat.Literal.neg 56), (Sat.Literal.pos 823)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_7_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 822), (Sat.Literal.pos 7), (Sat.Literal.pos 56), (Sat.Literal.pos 823)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 823) = lexBefore s permutation7 6 := by
  exact (positive_lex_of_descriptor s 823 permutation7 7 (by rfl)).trans ((lex_skipped s permutation7 6 7 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation7 6) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 64) = permuteMask permutation7 6 by rw [image7_eq]; rfl))

theorem lex_7_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 824) (Sat.Literal.pos 823) (Sat.Literal.pos 6) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation7 6 (assignment s)
    (Sat.Literal.pos 824) (Sat.Literal.pos 823) (Sat.Literal.pos 6) (Sat.Literal.pos 48) (positive_of_descriptor s 824 (.lex permutation7 6) (by rfl)) (lex_7_6_prefix s) (positive_select s 6) (lex_7_6_image s)

theorem lex_7_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.pos 6), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation7 6 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 823) (Sat.Literal.pos 6) (Sat.Literal.pos 48) (lex_7_6_prefix s) (positive_select s 6) (lex_7_6_image s)

theorem lex_7_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.pos 823)] :=
  (lex_7_6_gate s).prop _ (List.Mem.head _)

theorem lex_7_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.neg 6), (Sat.Literal.pos 48)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.pos 6), (Sat.Literal.neg 48)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.neg 6), (Sat.Literal.neg 48), (Sat.Literal.pos 824)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 823), (Sat.Literal.pos 6), (Sat.Literal.pos 48), (Sat.Literal.pos 824)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 824) = lexBefore s permutation7 5 := by
  exact (positive_lex_of_descriptor s 824 permutation7 6 (by rfl)).trans ((lex_skipped s permutation7 5 6 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation7 5) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation7 5 by rw [image7_eq]; rfl))

theorem lex_7_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 825) (Sat.Literal.pos 824) (Sat.Literal.pos 5) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation7 5 (assignment s)
    (Sat.Literal.pos 825) (Sat.Literal.pos 824) (Sat.Literal.pos 5) (Sat.Literal.pos 40) (positive_of_descriptor s 825 (.lex permutation7 5) (by rfl)) (lex_7_5_prefix s) (positive_select s 5) (lex_7_5_image s)

theorem lex_7_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.pos 5), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation7 5 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 824) (Sat.Literal.pos 5) (Sat.Literal.pos 40) (lex_7_5_prefix s) (positive_select s 5) (lex_7_5_image s)

theorem lex_7_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.pos 824)] :=
  (lex_7_5_gate s).prop _ (List.Mem.head _)

theorem lex_7_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.neg 5), (Sat.Literal.pos 40)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.pos 5), (Sat.Literal.neg 40)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.neg 5), (Sat.Literal.neg 40), (Sat.Literal.pos 825)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 824), (Sat.Literal.pos 5), (Sat.Literal.pos 40), (Sat.Literal.pos 825)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 825) = lexBefore s permutation7 4 := by
  exact (positive_lex_of_descriptor s 825 permutation7 5 (by rfl)).trans ((lex_skipped s permutation7 4 5 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation7 4) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 64) = permuteMask permutation7 4 by rw [image7_eq]; rfl))

theorem lex_7_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 826) (Sat.Literal.pos 825) (Sat.Literal.pos 4) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation7 4 (assignment s)
    (Sat.Literal.pos 826) (Sat.Literal.pos 825) (Sat.Literal.pos 4) (Sat.Literal.pos 32) (positive_of_descriptor s 826 (.lex permutation7 4) (by rfl)) (lex_7_4_prefix s) (positive_select s 4) (lex_7_4_image s)

theorem lex_7_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.pos 4), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation7 4 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 825) (Sat.Literal.pos 4) (Sat.Literal.pos 32) (lex_7_4_prefix s) (positive_select s 4) (lex_7_4_image s)

theorem lex_7_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.pos 825)] :=
  (lex_7_4_gate s).prop _ (List.Mem.head _)

theorem lex_7_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.neg 4), (Sat.Literal.pos 32)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.pos 4), (Sat.Literal.neg 32)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.neg 4), (Sat.Literal.neg 32), (Sat.Literal.pos 826)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 825), (Sat.Literal.pos 4), (Sat.Literal.pos 32), (Sat.Literal.pos 826)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_3_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 826) = lexBefore s permutation7 3 := by
  exact (positive_lex_of_descriptor s 826 permutation7 4 (by rfl)).trans ((lex_skipped s permutation7 3 4 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_3_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation7 3) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation7 3 by rw [image7_eq]; rfl))

theorem lex_7_3_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 827) (Sat.Literal.pos 826) (Sat.Literal.pos 3) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation7 3 (assignment s)
    (Sat.Literal.pos 827) (Sat.Literal.pos 826) (Sat.Literal.pos 3) (Sat.Literal.pos 24) (positive_of_descriptor s 827 (.lex permutation7 3) (by rfl)) (lex_7_3_prefix s) (positive_select s 3) (lex_7_3_image s)

theorem lex_7_3_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.pos 3), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation7 3 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 826) (Sat.Literal.pos 3) (Sat.Literal.pos 24) (lex_7_3_prefix s) (positive_select s 3) (lex_7_3_image s)

theorem lex_7_3_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.pos 826)] :=
  (lex_7_3_gate s).prop _ (List.Mem.head _)

theorem lex_7_3_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.neg 3), (Sat.Literal.pos 24)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_3_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.pos 3), (Sat.Literal.neg 24)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_3_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.neg 3), (Sat.Literal.neg 24), (Sat.Literal.pos 827)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_3_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 826), (Sat.Literal.pos 3), (Sat.Literal.pos 24), (Sat.Literal.pos 827)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 827) = lexBefore s permutation7 2 := by
  exact (positive_lex_of_descriptor s 827 permutation7 3 (by rfl)).trans ((lex_skipped s permutation7 2 3 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation7 2) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation7 2 by rw [image7_eq]; rfl))

theorem lex_7_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 828) (Sat.Literal.pos 827) (Sat.Literal.pos 2) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation7 2 (assignment s)
    (Sat.Literal.pos 828) (Sat.Literal.pos 827) (Sat.Literal.pos 2) (Sat.Literal.pos 16) (positive_of_descriptor s 828 (.lex permutation7 2) (by rfl)) (lex_7_2_prefix s) (positive_select s 2) (lex_7_2_image s)

theorem lex_7_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.pos 2), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation7 2 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 827) (Sat.Literal.pos 2) (Sat.Literal.pos 16) (lex_7_2_prefix s) (positive_select s 2) (lex_7_2_image s)

theorem lex_7_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.pos 827)] :=
  (lex_7_2_gate s).prop _ (List.Mem.head _)

theorem lex_7_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.neg 2), (Sat.Literal.pos 16)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.pos 2), (Sat.Literal.neg 16)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.neg 2), (Sat.Literal.neg 16), (Sat.Literal.pos 828)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 827), (Sat.Literal.pos 2), (Sat.Literal.pos 16), (Sat.Literal.pos 828)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_1_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 828) = lexBefore s permutation7 1 := by
  exact (positive_lex_of_descriptor s 828 permutation7 2 (by rfl)).trans ((lex_skipped s permutation7 1 2 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_1_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation7 1) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation7 1 by rw [image7_eq]; rfl))

theorem lex_7_1_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 829) (Sat.Literal.pos 828) (Sat.Literal.pos 1) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation7 1 (assignment s)
    (Sat.Literal.pos 829) (Sat.Literal.pos 828) (Sat.Literal.pos 1) (Sat.Literal.pos 8) (positive_of_descriptor s 829 (.lex permutation7 1) (by rfl)) (lex_7_1_prefix s) (positive_select s 1) (lex_7_1_image s)

theorem lex_7_1_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.pos 1), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation7 1 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 828) (Sat.Literal.pos 1) (Sat.Literal.pos 8) (lex_7_1_prefix s) (positive_select s 1) (lex_7_1_image s)

theorem lex_7_1_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 829), (Sat.Literal.pos 828)] :=
  (lex_7_1_gate s).prop _ (List.Mem.head _)

theorem lex_7_1_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 829), (Sat.Literal.neg 1), (Sat.Literal.pos 8)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_1_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 829), (Sat.Literal.pos 1), (Sat.Literal.neg 8)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_1_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.neg 1), (Sat.Literal.neg 8), (Sat.Literal.pos 829)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_1_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 828), (Sat.Literal.pos 1), (Sat.Literal.pos 8), (Sat.Literal.pos 829)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation8 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation8 62 (by intro j hj; rw [image8_eq]; exact fixedOnRange_spec image8 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_8_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation8 62) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation8 62 by rw [image8_eq]; rfl))

theorem lex_8_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 830) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation8 62 (assignment s)
    (Sat.Literal.pos 830) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 47) (positive_of_descriptor s 830 (.lex permutation8 62) (by rfl)) (lex_8_62_prefix s) (positive_select s 62) (lex_8_62_image s)

theorem lex_8_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation8 62 (hmax permutation8) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 47) (lex_8_62_prefix s) (positive_select s 62) (lex_8_62_image s)

theorem lex_8_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.neg 64)] :=
  (lex_8_62_gate s).prop _ (List.Mem.head _)

theorem lex_8_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.neg 62), (Sat.Literal.pos 47)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.pos 62), (Sat.Literal.neg 47)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 47), (Sat.Literal.pos 830)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 47), (Sat.Literal.pos 830)] :=
  (lex_8_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 830) = lexBefore s permutation8 61 := by
  exact (positive_lex_of_descriptor s 830 permutation8 62 (by rfl)).trans ((lex_skipped s permutation8 61 62 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation8 61) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation8 61 by rw [image8_eq]; rfl))

theorem lex_8_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 831) (Sat.Literal.pos 830) (Sat.Literal.pos 61) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation8 61 (assignment s)
    (Sat.Literal.pos 831) (Sat.Literal.pos 830) (Sat.Literal.pos 61) (Sat.Literal.pos 31) (positive_of_descriptor s 831 (.lex permutation8 61) (by rfl)) (lex_8_61_prefix s) (positive_select s 61) (lex_8_61_image s)

theorem lex_8_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.pos 61), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation8 61 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 830) (Sat.Literal.pos 61) (Sat.Literal.pos 31) (lex_8_61_prefix s) (positive_select s 61) (lex_8_61_image s)

theorem lex_8_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.pos 830)] :=
  (lex_8_61_gate s).prop _ (List.Mem.head _)

theorem lex_8_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.neg 61), (Sat.Literal.pos 31)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.pos 61), (Sat.Literal.neg 31)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.neg 61), (Sat.Literal.neg 31), (Sat.Literal.pos 831)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 830), (Sat.Literal.pos 61), (Sat.Literal.pos 31), (Sat.Literal.pos 831)] :=
  (lex_8_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_60_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 831) = lexBefore s permutation8 60 := by
  exact (positive_lex_of_descriptor s 831 permutation8 61 (by rfl)).trans ((lex_skipped s permutation8 60 61 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_60_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation8 60) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 64) = permuteMask permutation8 60 by rw [image8_eq]; rfl))

theorem lex_8_60_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 832) (Sat.Literal.pos 831) (Sat.Literal.pos 60) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation8 60 (assignment s)
    (Sat.Literal.pos 832) (Sat.Literal.pos 831) (Sat.Literal.pos 60) (Sat.Literal.pos 15) (positive_of_descriptor s 832 (.lex permutation8 60) (by rfl)) (lex_8_60_prefix s) (positive_select s 60) (lex_8_60_image s)

theorem lex_8_60_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.pos 60), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation8 60 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 831) (Sat.Literal.pos 60) (Sat.Literal.pos 15) (lex_8_60_prefix s) (positive_select s 60) (lex_8_60_image s)

theorem lex_8_60_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.pos 831)] :=
  (lex_8_60_gate s).prop _ (List.Mem.head _)

theorem lex_8_60_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.neg 60), (Sat.Literal.pos 15)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_60_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.pos 60), (Sat.Literal.neg 15)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_60_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.neg 60), (Sat.Literal.neg 15), (Sat.Literal.pos 832)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_60_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 831), (Sat.Literal.pos 60), (Sat.Literal.pos 15), (Sat.Literal.pos 832)] :=
  (lex_8_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 832) = lexBefore s permutation8 59 := by
  exact (positive_lex_of_descriptor s 832 permutation8 60 (by rfl)).trans ((lex_skipped s permutation8 59 60 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation8 59) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation8 59 by rw [image8_eq]; rfl))

theorem lex_8_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 833) (Sat.Literal.pos 832) (Sat.Literal.pos 59) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation8 59 (assignment s)
    (Sat.Literal.pos 833) (Sat.Literal.pos 832) (Sat.Literal.pos 59) (Sat.Literal.pos 62) (positive_of_descriptor s 833 (.lex permutation8 59) (by rfl)) (lex_8_59_prefix s) (positive_select s 59) (lex_8_59_image s)

theorem lex_8_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.pos 59), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation8 59 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 832) (Sat.Literal.pos 59) (Sat.Literal.pos 62) (lex_8_59_prefix s) (positive_select s 59) (lex_8_59_image s)

theorem lex_8_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.pos 832)] :=
  (lex_8_59_gate s).prop _ (List.Mem.head _)

theorem lex_8_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.neg 59), (Sat.Literal.pos 62)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.pos 59), (Sat.Literal.neg 62)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.neg 59), (Sat.Literal.neg 62), (Sat.Literal.pos 833)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 832), (Sat.Literal.pos 59), (Sat.Literal.pos 62), (Sat.Literal.pos 833)] :=
  (lex_8_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 833) = lexBefore s permutation8 58 := by
  exact (positive_lex_of_descriptor s 833 permutation8 59 (by rfl)).trans ((lex_skipped s permutation8 58 59 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation8 58) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation8 58 by rw [image8_eq]; rfl))

theorem lex_8_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 834) (Sat.Literal.pos 833) (Sat.Literal.pos 58) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation8 58 (assignment s)
    (Sat.Literal.pos 834) (Sat.Literal.pos 833) (Sat.Literal.pos 58) (Sat.Literal.pos 46) (positive_of_descriptor s 834 (.lex permutation8 58) (by rfl)) (lex_8_58_prefix s) (positive_select s 58) (lex_8_58_image s)

theorem lex_8_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.pos 58), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation8 58 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 833) (Sat.Literal.pos 58) (Sat.Literal.pos 46) (lex_8_58_prefix s) (positive_select s 58) (lex_8_58_image s)

theorem lex_8_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.pos 833)] :=
  (lex_8_58_gate s).prop _ (List.Mem.head _)

theorem lex_8_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.neg 58), (Sat.Literal.pos 46)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.pos 58), (Sat.Literal.neg 46)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.neg 58), (Sat.Literal.neg 46), (Sat.Literal.pos 834)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 833), (Sat.Literal.pos 58), (Sat.Literal.pos 46), (Sat.Literal.pos 834)] :=
  (lex_8_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 834) = lexBefore s permutation8 57 := by
  exact (positive_lex_of_descriptor s 834 permutation8 58 (by rfl)).trans ((lex_skipped s permutation8 57 58 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation8 57) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation8 57 by rw [image8_eq]; rfl))

theorem lex_8_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 835) (Sat.Literal.pos 834) (Sat.Literal.pos 57) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation8 57 (assignment s)
    (Sat.Literal.pos 835) (Sat.Literal.pos 834) (Sat.Literal.pos 57) (Sat.Literal.pos 30) (positive_of_descriptor s 835 (.lex permutation8 57) (by rfl)) (lex_8_57_prefix s) (positive_select s 57) (lex_8_57_image s)

theorem lex_8_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.pos 57), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation8 57 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 834) (Sat.Literal.pos 57) (Sat.Literal.pos 30) (lex_8_57_prefix s) (positive_select s 57) (lex_8_57_image s)

theorem lex_8_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.pos 834)] :=
  (lex_8_57_gate s).prop _ (List.Mem.head _)

theorem lex_8_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.neg 57), (Sat.Literal.pos 30)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.pos 57), (Sat.Literal.neg 30)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.neg 57), (Sat.Literal.neg 30), (Sat.Literal.pos 835)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 834), (Sat.Literal.pos 57), (Sat.Literal.pos 30), (Sat.Literal.pos 835)] :=
  (lex_8_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_56_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 835) = lexBefore s permutation8 56 := by
  exact (positive_lex_of_descriptor s 835 permutation8 57 (by rfl)).trans ((lex_skipped s permutation8 56 57 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_56_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation8 56) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation8 56 by rw [image8_eq]; rfl))

theorem lex_8_56_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 836) (Sat.Literal.pos 835) (Sat.Literal.pos 56) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation8 56 (assignment s)
    (Sat.Literal.pos 836) (Sat.Literal.pos 835) (Sat.Literal.pos 56) (Sat.Literal.pos 14) (positive_of_descriptor s 836 (.lex permutation8 56) (by rfl)) (lex_8_56_prefix s) (positive_select s 56) (lex_8_56_image s)

theorem lex_8_56_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.pos 56), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation8 56 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 835) (Sat.Literal.pos 56) (Sat.Literal.pos 14) (lex_8_56_prefix s) (positive_select s 56) (lex_8_56_image s)

theorem lex_8_56_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.pos 835)] :=
  (lex_8_56_gate s).prop _ (List.Mem.head _)

theorem lex_8_56_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.neg 56), (Sat.Literal.pos 14)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_56_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.pos 56), (Sat.Literal.neg 14)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_56_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.neg 56), (Sat.Literal.neg 14), (Sat.Literal.pos 836)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_56_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 835), (Sat.Literal.pos 56), (Sat.Literal.pos 14), (Sat.Literal.pos 836)] :=
  (lex_8_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 836) = lexBefore s permutation8 55 := by
  exact (positive_lex_of_descriptor s 836 permutation8 56 (by rfl)).trans ((lex_skipped s permutation8 55 56 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation8 55) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation8 55 by rw [image8_eq]; rfl))

theorem lex_8_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 837) (Sat.Literal.pos 836) (Sat.Literal.pos 55) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation8 55 (assignment s)
    (Sat.Literal.pos 837) (Sat.Literal.pos 836) (Sat.Literal.pos 55) (Sat.Literal.pos 61) (positive_of_descriptor s 837 (.lex permutation8 55) (by rfl)) (lex_8_55_prefix s) (positive_select s 55) (lex_8_55_image s)

theorem lex_8_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.pos 55), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation8 55 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 836) (Sat.Literal.pos 55) (Sat.Literal.pos 61) (lex_8_55_prefix s) (positive_select s 55) (lex_8_55_image s)

theorem lex_8_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.pos 836)] :=
  (lex_8_55_gate s).prop _ (List.Mem.head _)

theorem lex_8_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.neg 55), (Sat.Literal.pos 61)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.pos 55), (Sat.Literal.neg 61)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.neg 55), (Sat.Literal.neg 61), (Sat.Literal.pos 837)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 836), (Sat.Literal.pos 55), (Sat.Literal.pos 61), (Sat.Literal.pos 837)] :=
  (lex_8_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 837) = lexBefore s permutation8 54 := by
  exact (positive_lex_of_descriptor s 837 permutation8 55 (by rfl)).trans ((lex_skipped s permutation8 54 55 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation8 54) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation8 54 by rw [image8_eq]; rfl))

theorem lex_8_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 838) (Sat.Literal.pos 837) (Sat.Literal.pos 54) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation8 54 (assignment s)
    (Sat.Literal.pos 838) (Sat.Literal.pos 837) (Sat.Literal.pos 54) (Sat.Literal.pos 45) (positive_of_descriptor s 838 (.lex permutation8 54) (by rfl)) (lex_8_54_prefix s) (positive_select s 54) (lex_8_54_image s)

theorem lex_8_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.pos 54), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation8 54 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 837) (Sat.Literal.pos 54) (Sat.Literal.pos 45) (lex_8_54_prefix s) (positive_select s 54) (lex_8_54_image s)

theorem lex_8_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.pos 837)] :=
  (lex_8_54_gate s).prop _ (List.Mem.head _)

theorem lex_8_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.neg 54), (Sat.Literal.pos 45)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.pos 54), (Sat.Literal.neg 45)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.neg 54), (Sat.Literal.neg 45), (Sat.Literal.pos 838)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 837), (Sat.Literal.pos 54), (Sat.Literal.pos 45), (Sat.Literal.pos 838)] :=
  (lex_8_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 838) = lexBefore s permutation8 53 := by
  exact (positive_lex_of_descriptor s 838 permutation8 54 (by rfl)).trans ((lex_skipped s permutation8 53 54 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation8 53) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation8 53 by rw [image8_eq]; rfl))

theorem lex_8_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 839) (Sat.Literal.pos 838) (Sat.Literal.pos 53) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation8 53 (assignment s)
    (Sat.Literal.pos 839) (Sat.Literal.pos 838) (Sat.Literal.pos 53) (Sat.Literal.pos 29) (positive_of_descriptor s 839 (.lex permutation8 53) (by rfl)) (lex_8_53_prefix s) (positive_select s 53) (lex_8_53_image s)

theorem lex_8_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.pos 53), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation8 53 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 838) (Sat.Literal.pos 53) (Sat.Literal.pos 29) (lex_8_53_prefix s) (positive_select s 53) (lex_8_53_image s)

theorem lex_8_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.pos 838)] :=
  (lex_8_53_gate s).prop _ (List.Mem.head _)

theorem lex_8_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.neg 53), (Sat.Literal.pos 29)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.pos 53), (Sat.Literal.neg 29)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.neg 53), (Sat.Literal.neg 29), (Sat.Literal.pos 839)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 838), (Sat.Literal.pos 53), (Sat.Literal.pos 29), (Sat.Literal.pos 839)] :=
  (lex_8_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 839) = lexBefore s permutation8 52 := by
  exact (positive_lex_of_descriptor s 839 permutation8 53 (by rfl)).trans ((lex_skipped s permutation8 52 53 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation8 52) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation8 52 by rw [image8_eq]; rfl))

theorem lex_8_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 840) (Sat.Literal.pos 839) (Sat.Literal.pos 52) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation8 52 (assignment s)
    (Sat.Literal.pos 840) (Sat.Literal.pos 839) (Sat.Literal.pos 52) (Sat.Literal.pos 13) (positive_of_descriptor s 840 (.lex permutation8 52) (by rfl)) (lex_8_52_prefix s) (positive_select s 52) (lex_8_52_image s)

theorem lex_8_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.pos 52), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation8 52 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 839) (Sat.Literal.pos 52) (Sat.Literal.pos 13) (lex_8_52_prefix s) (positive_select s 52) (lex_8_52_image s)

theorem lex_8_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.pos 839)] :=
  (lex_8_52_gate s).prop _ (List.Mem.head _)

theorem lex_8_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.neg 52), (Sat.Literal.pos 13)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.pos 52), (Sat.Literal.neg 13)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.neg 52), (Sat.Literal.neg 13), (Sat.Literal.pos 840)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 839), (Sat.Literal.pos 52), (Sat.Literal.pos 13), (Sat.Literal.pos 840)] :=
  (lex_8_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 840) = lexBefore s permutation8 51 := by
  exact (positive_lex_of_descriptor s 840 permutation8 52 (by rfl)).trans ((lex_skipped s permutation8 51 52 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation8 51) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 64) = permuteMask permutation8 51 by rw [image8_eq]; rfl))

theorem lex_8_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 841) (Sat.Literal.pos 840) (Sat.Literal.pos 51) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation8 51 (assignment s)
    (Sat.Literal.pos 841) (Sat.Literal.pos 840) (Sat.Literal.pos 51) (Sat.Literal.pos 60) (positive_of_descriptor s 841 (.lex permutation8 51) (by rfl)) (lex_8_51_prefix s) (positive_select s 51) (lex_8_51_image s)

theorem lex_8_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.pos 51), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation8 51 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 840) (Sat.Literal.pos 51) (Sat.Literal.pos 60) (lex_8_51_prefix s) (positive_select s 51) (lex_8_51_image s)

theorem lex_8_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.pos 840)] :=
  (lex_8_51_gate s).prop _ (List.Mem.head _)

theorem lex_8_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.neg 51), (Sat.Literal.pos 60)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.pos 51), (Sat.Literal.neg 60)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.neg 51), (Sat.Literal.neg 60), (Sat.Literal.pos 841)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 840), (Sat.Literal.pos 51), (Sat.Literal.pos 60), (Sat.Literal.pos 841)] :=
  (lex_8_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 841) = lexBefore s permutation8 50 := by
  exact (positive_lex_of_descriptor s 841 permutation8 51 (by rfl)).trans ((lex_skipped s permutation8 50 51 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation8 50) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation8 50 by rw [image8_eq]; rfl))

theorem lex_8_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 842) (Sat.Literal.pos 841) (Sat.Literal.pos 50) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation8 50 (assignment s)
    (Sat.Literal.pos 842) (Sat.Literal.pos 841) (Sat.Literal.pos 50) (Sat.Literal.pos 44) (positive_of_descriptor s 842 (.lex permutation8 50) (by rfl)) (lex_8_50_prefix s) (positive_select s 50) (lex_8_50_image s)

theorem lex_8_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.pos 50), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation8 50 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 841) (Sat.Literal.pos 50) (Sat.Literal.pos 44) (lex_8_50_prefix s) (positive_select s 50) (lex_8_50_image s)

theorem lex_8_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.pos 841)] :=
  (lex_8_50_gate s).prop _ (List.Mem.head _)

theorem lex_8_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.neg 50), (Sat.Literal.pos 44)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.pos 50), (Sat.Literal.neg 44)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.neg 50), (Sat.Literal.neg 44), (Sat.Literal.pos 842)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 841), (Sat.Literal.pos 50), (Sat.Literal.pos 44), (Sat.Literal.pos 842)] :=
  (lex_8_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 842) = lexBefore s permutation8 49 := by
  exact (positive_lex_of_descriptor s 842 permutation8 50 (by rfl)).trans ((lex_skipped s permutation8 49 50 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation8 49) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation8 49 by rw [image8_eq]; rfl))

theorem lex_8_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 843) (Sat.Literal.pos 842) (Sat.Literal.pos 49) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation8 49 (assignment s)
    (Sat.Literal.pos 843) (Sat.Literal.pos 842) (Sat.Literal.pos 49) (Sat.Literal.pos 28) (positive_of_descriptor s 843 (.lex permutation8 49) (by rfl)) (lex_8_49_prefix s) (positive_select s 49) (lex_8_49_image s)

theorem lex_8_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.pos 49), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation8 49 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 842) (Sat.Literal.pos 49) (Sat.Literal.pos 28) (lex_8_49_prefix s) (positive_select s 49) (lex_8_49_image s)

theorem lex_8_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.pos 842)] :=
  (lex_8_49_gate s).prop _ (List.Mem.head _)

theorem lex_8_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.neg 49), (Sat.Literal.pos 28)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.pos 49), (Sat.Literal.neg 28)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.neg 49), (Sat.Literal.neg 28), (Sat.Literal.pos 843)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 842), (Sat.Literal.pos 49), (Sat.Literal.pos 28), (Sat.Literal.pos 843)] :=
  (lex_8_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_48_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 843) = lexBefore s permutation8 48 := by
  exact (positive_lex_of_descriptor s 843 permutation8 49 (by rfl)).trans ((lex_skipped s permutation8 48 49 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_48_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation8 48) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation8 48 by rw [image8_eq]; rfl))

theorem lex_8_48_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 844) (Sat.Literal.pos 843) (Sat.Literal.pos 48) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation8 48 (assignment s)
    (Sat.Literal.pos 844) (Sat.Literal.pos 843) (Sat.Literal.pos 48) (Sat.Literal.pos 12) (positive_of_descriptor s 844 (.lex permutation8 48) (by rfl)) (lex_8_48_prefix s) (positive_select s 48) (lex_8_48_image s)

theorem lex_8_48_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.pos 48), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation8 48 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 843) (Sat.Literal.pos 48) (Sat.Literal.pos 12) (lex_8_48_prefix s) (positive_select s 48) (lex_8_48_image s)

theorem lex_8_48_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.pos 843)] :=
  (lex_8_48_gate s).prop _ (List.Mem.head _)

theorem lex_8_48_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.neg 48), (Sat.Literal.pos 12)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_48_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.pos 48), (Sat.Literal.neg 12)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_48_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.neg 48), (Sat.Literal.neg 12), (Sat.Literal.pos 844)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_48_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 843), (Sat.Literal.pos 48), (Sat.Literal.pos 12), (Sat.Literal.pos 844)] :=
  (lex_8_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 844) = lexBefore s permutation8 47 := by
  exact (positive_lex_of_descriptor s 844 permutation8 48 (by rfl)).trans ((lex_skipped s permutation8 47 48 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation8 47) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation8 47 by rw [image8_eq]; rfl))

theorem lex_8_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 845) (Sat.Literal.pos 844) (Sat.Literal.pos 47) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation8 47 (assignment s)
    (Sat.Literal.pos 845) (Sat.Literal.pos 844) (Sat.Literal.pos 47) (Sat.Literal.pos 59) (positive_of_descriptor s 845 (.lex permutation8 47) (by rfl)) (lex_8_47_prefix s) (positive_select s 47) (lex_8_47_image s)

theorem lex_8_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.pos 47), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation8 47 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 844) (Sat.Literal.pos 47) (Sat.Literal.pos 59) (lex_8_47_prefix s) (positive_select s 47) (lex_8_47_image s)

theorem lex_8_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.pos 844)] :=
  (lex_8_47_gate s).prop _ (List.Mem.head _)

theorem lex_8_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.neg 47), (Sat.Literal.pos 59)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.pos 47), (Sat.Literal.neg 59)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.neg 47), (Sat.Literal.neg 59), (Sat.Literal.pos 845)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 844), (Sat.Literal.pos 47), (Sat.Literal.pos 59), (Sat.Literal.pos 845)] :=
  (lex_8_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 845) = lexBefore s permutation8 46 := by
  exact (positive_lex_of_descriptor s 845 permutation8 47 (by rfl)).trans ((lex_skipped s permutation8 46 47 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation8 46) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation8 46 by rw [image8_eq]; rfl))

theorem lex_8_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 846) (Sat.Literal.pos 845) (Sat.Literal.pos 46) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation8 46 (assignment s)
    (Sat.Literal.pos 846) (Sat.Literal.pos 845) (Sat.Literal.pos 46) (Sat.Literal.pos 43) (positive_of_descriptor s 846 (.lex permutation8 46) (by rfl)) (lex_8_46_prefix s) (positive_select s 46) (lex_8_46_image s)

theorem lex_8_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.pos 46), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation8 46 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 845) (Sat.Literal.pos 46) (Sat.Literal.pos 43) (lex_8_46_prefix s) (positive_select s 46) (lex_8_46_image s)

theorem lex_8_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.pos 845)] :=
  (lex_8_46_gate s).prop _ (List.Mem.head _)

theorem lex_8_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.neg 46), (Sat.Literal.pos 43)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.pos 46), (Sat.Literal.neg 43)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.neg 46), (Sat.Literal.neg 43), (Sat.Literal.pos 846)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 845), (Sat.Literal.pos 46), (Sat.Literal.pos 43), (Sat.Literal.pos 846)] :=
  (lex_8_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 846) = lexBefore s permutation8 45 := by
  exact (positive_lex_of_descriptor s 846 permutation8 46 (by rfl)).trans ((lex_skipped s permutation8 45 46 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation8 45) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation8 45 by rw [image8_eq]; rfl))

theorem lex_8_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 847) (Sat.Literal.pos 846) (Sat.Literal.pos 45) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation8 45 (assignment s)
    (Sat.Literal.pos 847) (Sat.Literal.pos 846) (Sat.Literal.pos 45) (Sat.Literal.pos 27) (positive_of_descriptor s 847 (.lex permutation8 45) (by rfl)) (lex_8_45_prefix s) (positive_select s 45) (lex_8_45_image s)

theorem lex_8_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.pos 45), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation8 45 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 846) (Sat.Literal.pos 45) (Sat.Literal.pos 27) (lex_8_45_prefix s) (positive_select s 45) (lex_8_45_image s)

theorem lex_8_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.pos 846)] :=
  (lex_8_45_gate s).prop _ (List.Mem.head _)

theorem lex_8_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.neg 45), (Sat.Literal.pos 27)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.pos 45), (Sat.Literal.neg 27)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.neg 45), (Sat.Literal.neg 27), (Sat.Literal.pos 847)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 846), (Sat.Literal.pos 45), (Sat.Literal.pos 27), (Sat.Literal.pos 847)] :=
  (lex_8_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 847) = lexBefore s permutation8 44 := by
  exact (positive_lex_of_descriptor s 847 permutation8 45 (by rfl)).trans ((lex_skipped s permutation8 44 45 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation8 44) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation8 44 by rw [image8_eq]; rfl))

theorem lex_8_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 848) (Sat.Literal.pos 847) (Sat.Literal.pos 44) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation8 44 (assignment s)
    (Sat.Literal.pos 848) (Sat.Literal.pos 847) (Sat.Literal.pos 44) (Sat.Literal.pos 11) (positive_of_descriptor s 848 (.lex permutation8 44) (by rfl)) (lex_8_44_prefix s) (positive_select s 44) (lex_8_44_image s)

theorem lex_8_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.pos 44), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation8 44 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 847) (Sat.Literal.pos 44) (Sat.Literal.pos 11) (lex_8_44_prefix s) (positive_select s 44) (lex_8_44_image s)

theorem lex_8_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.pos 847)] :=
  (lex_8_44_gate s).prop _ (List.Mem.head _)

theorem lex_8_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.neg 44), (Sat.Literal.pos 11)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.pos 44), (Sat.Literal.neg 11)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.neg 44), (Sat.Literal.neg 11), (Sat.Literal.pos 848)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 847), (Sat.Literal.pos 44), (Sat.Literal.pos 11), (Sat.Literal.pos 848)] :=
  (lex_8_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 848) = lexBefore s permutation8 43 := by
  exact (positive_lex_of_descriptor s 848 permutation8 44 (by rfl)).trans ((lex_skipped s permutation8 43 44 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation8 43) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation8 43 by rw [image8_eq]; rfl))

theorem lex_8_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 849) (Sat.Literal.pos 848) (Sat.Literal.pos 43) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation8 43 (assignment s)
    (Sat.Literal.pos 849) (Sat.Literal.pos 848) (Sat.Literal.pos 43) (Sat.Literal.pos 58) (positive_of_descriptor s 849 (.lex permutation8 43) (by rfl)) (lex_8_43_prefix s) (positive_select s 43) (lex_8_43_image s)

theorem lex_8_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.pos 43), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation8 43 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 848) (Sat.Literal.pos 43) (Sat.Literal.pos 58) (lex_8_43_prefix s) (positive_select s 43) (lex_8_43_image s)

theorem lex_8_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.pos 848)] :=
  (lex_8_43_gate s).prop _ (List.Mem.head _)

theorem lex_8_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.neg 43), (Sat.Literal.pos 58)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.pos 43), (Sat.Literal.neg 58)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.neg 43), (Sat.Literal.neg 58), (Sat.Literal.pos 849)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 848), (Sat.Literal.pos 43), (Sat.Literal.pos 58), (Sat.Literal.pos 849)] :=
  (lex_8_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 849) = lexBefore s permutation8 41 := by
  exact (positive_lex_of_descriptor s 849 permutation8 43 (by rfl)).trans ((lex_skipped s permutation8 41 43 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 42 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation8 41) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation8 41 by rw [image8_eq]; rfl))

theorem lex_8_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 850) (Sat.Literal.pos 849) (Sat.Literal.pos 41) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation8 41 (assignment s)
    (Sat.Literal.pos 850) (Sat.Literal.pos 849) (Sat.Literal.pos 41) (Sat.Literal.pos 26) (positive_of_descriptor s 850 (.lex permutation8 41) (by rfl)) (lex_8_41_prefix s) (positive_select s 41) (lex_8_41_image s)

theorem lex_8_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.pos 41), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation8 41 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 849) (Sat.Literal.pos 41) (Sat.Literal.pos 26) (lex_8_41_prefix s) (positive_select s 41) (lex_8_41_image s)

theorem lex_8_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.pos 849)] :=
  (lex_8_41_gate s).prop _ (List.Mem.head _)

theorem lex_8_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.neg 41), (Sat.Literal.pos 26)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.pos 41), (Sat.Literal.neg 26)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.neg 41), (Sat.Literal.neg 26), (Sat.Literal.pos 850)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 849), (Sat.Literal.pos 41), (Sat.Literal.pos 26), (Sat.Literal.pos 850)] :=
  (lex_8_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 850) = lexBefore s permutation8 40 := by
  exact (positive_lex_of_descriptor s 850 permutation8 41 (by rfl)).trans ((lex_skipped s permutation8 40 41 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation8 40) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation8 40 by rw [image8_eq]; rfl))

theorem lex_8_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 851) (Sat.Literal.pos 850) (Sat.Literal.pos 40) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation8 40 (assignment s)
    (Sat.Literal.pos 851) (Sat.Literal.pos 850) (Sat.Literal.pos 40) (Sat.Literal.pos 10) (positive_of_descriptor s 851 (.lex permutation8 40) (by rfl)) (lex_8_40_prefix s) (positive_select s 40) (lex_8_40_image s)

theorem lex_8_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.pos 40), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation8 40 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 850) (Sat.Literal.pos 40) (Sat.Literal.pos 10) (lex_8_40_prefix s) (positive_select s 40) (lex_8_40_image s)

theorem lex_8_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.pos 850)] :=
  (lex_8_40_gate s).prop _ (List.Mem.head _)

theorem lex_8_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.neg 40), (Sat.Literal.pos 10)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.pos 40), (Sat.Literal.neg 10)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.neg 40), (Sat.Literal.neg 10), (Sat.Literal.pos 851)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 850), (Sat.Literal.pos 40), (Sat.Literal.pos 10), (Sat.Literal.pos 851)] :=
  (lex_8_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 851) = lexBefore s permutation8 39 := by
  exact (positive_lex_of_descriptor s 851 permutation8 40 (by rfl)).trans ((lex_skipped s permutation8 39 40 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation8 39) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation8 39 by rw [image8_eq]; rfl))

theorem lex_8_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 852) (Sat.Literal.pos 851) (Sat.Literal.pos 39) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation8 39 (assignment s)
    (Sat.Literal.pos 852) (Sat.Literal.pos 851) (Sat.Literal.pos 39) (Sat.Literal.pos 57) (positive_of_descriptor s 852 (.lex permutation8 39) (by rfl)) (lex_8_39_prefix s) (positive_select s 39) (lex_8_39_image s)

theorem lex_8_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.pos 39), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation8 39 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 851) (Sat.Literal.pos 39) (Sat.Literal.pos 57) (lex_8_39_prefix s) (positive_select s 39) (lex_8_39_image s)

theorem lex_8_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.pos 851)] :=
  (lex_8_39_gate s).prop _ (List.Mem.head _)

theorem lex_8_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.neg 39), (Sat.Literal.pos 57)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.pos 39), (Sat.Literal.neg 57)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.neg 39), (Sat.Literal.neg 57), (Sat.Literal.pos 852)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 851), (Sat.Literal.pos 39), (Sat.Literal.pos 57), (Sat.Literal.pos 852)] :=
  (lex_8_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 852) = lexBefore s permutation8 38 := by
  exact (positive_lex_of_descriptor s 852 permutation8 39 (by rfl)).trans ((lex_skipped s permutation8 38 39 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation8 38) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation8 38 by rw [image8_eq]; rfl))

theorem lex_8_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 853) (Sat.Literal.pos 852) (Sat.Literal.pos 38) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation8 38 (assignment s)
    (Sat.Literal.pos 853) (Sat.Literal.pos 852) (Sat.Literal.pos 38) (Sat.Literal.pos 41) (positive_of_descriptor s 853 (.lex permutation8 38) (by rfl)) (lex_8_38_prefix s) (positive_select s 38) (lex_8_38_image s)

theorem lex_8_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.pos 38), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation8 38 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 852) (Sat.Literal.pos 38) (Sat.Literal.pos 41) (lex_8_38_prefix s) (positive_select s 38) (lex_8_38_image s)

theorem lex_8_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.pos 852)] :=
  (lex_8_38_gate s).prop _ (List.Mem.head _)

theorem lex_8_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.neg 38), (Sat.Literal.pos 41)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.pos 38), (Sat.Literal.neg 41)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.neg 38), (Sat.Literal.neg 41), (Sat.Literal.pos 853)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 852), (Sat.Literal.pos 38), (Sat.Literal.pos 41), (Sat.Literal.pos 853)] :=
  (lex_8_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 853) = lexBefore s permutation8 37 := by
  exact (positive_lex_of_descriptor s 853 permutation8 38 (by rfl)).trans ((lex_skipped s permutation8 37 38 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation8 37) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation8 37 by rw [image8_eq]; rfl))

theorem lex_8_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 854) (Sat.Literal.pos 853) (Sat.Literal.pos 37) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation8 37 (assignment s)
    (Sat.Literal.pos 854) (Sat.Literal.pos 853) (Sat.Literal.pos 37) (Sat.Literal.pos 25) (positive_of_descriptor s 854 (.lex permutation8 37) (by rfl)) (lex_8_37_prefix s) (positive_select s 37) (lex_8_37_image s)

theorem lex_8_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.pos 37), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation8 37 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 853) (Sat.Literal.pos 37) (Sat.Literal.pos 25) (lex_8_37_prefix s) (positive_select s 37) (lex_8_37_image s)

theorem lex_8_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.pos 853)] :=
  (lex_8_37_gate s).prop _ (List.Mem.head _)

theorem lex_8_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.neg 37), (Sat.Literal.pos 25)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.pos 37), (Sat.Literal.neg 25)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.neg 37), (Sat.Literal.neg 25), (Sat.Literal.pos 854)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 853), (Sat.Literal.pos 37), (Sat.Literal.pos 25), (Sat.Literal.pos 854)] :=
  (lex_8_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 854) = lexBefore s permutation8 36 := by
  exact (positive_lex_of_descriptor s 854 permutation8 37 (by rfl)).trans ((lex_skipped s permutation8 36 37 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation8 36) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation8 36 by rw [image8_eq]; rfl))

theorem lex_8_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 855) (Sat.Literal.pos 854) (Sat.Literal.pos 36) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation8 36 (assignment s)
    (Sat.Literal.pos 855) (Sat.Literal.pos 854) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (positive_of_descriptor s 855 (.lex permutation8 36) (by rfl)) (lex_8_36_prefix s) (positive_select s 36) (lex_8_36_image s)

theorem lex_8_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation8 36 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 854) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (lex_8_36_prefix s) (positive_select s 36) (lex_8_36_image s)

theorem lex_8_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.pos 854)] :=
  (lex_8_36_gate s).prop _ (List.Mem.head _)

theorem lex_8_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.neg 36), (Sat.Literal.pos 9)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.neg 36), (Sat.Literal.neg 9), (Sat.Literal.pos 855)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 854), (Sat.Literal.pos 36), (Sat.Literal.pos 9), (Sat.Literal.pos 855)] :=
  (lex_8_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 855) = lexBefore s permutation8 35 := by
  exact (positive_lex_of_descriptor s 855 permutation8 36 (by rfl)).trans ((lex_skipped s permutation8 35 36 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation8 35) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 64) = permuteMask permutation8 35 by rw [image8_eq]; rfl))

theorem lex_8_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 856) (Sat.Literal.pos 855) (Sat.Literal.pos 35) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation8 35 (assignment s)
    (Sat.Literal.pos 856) (Sat.Literal.pos 855) (Sat.Literal.pos 35) (Sat.Literal.pos 56) (positive_of_descriptor s 856 (.lex permutation8 35) (by rfl)) (lex_8_35_prefix s) (positive_select s 35) (lex_8_35_image s)

theorem lex_8_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.pos 35), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation8 35 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 855) (Sat.Literal.pos 35) (Sat.Literal.pos 56) (lex_8_35_prefix s) (positive_select s 35) (lex_8_35_image s)

theorem lex_8_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.pos 855)] :=
  (lex_8_35_gate s).prop _ (List.Mem.head _)

theorem lex_8_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.neg 35), (Sat.Literal.pos 56)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.pos 35), (Sat.Literal.neg 56)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.neg 35), (Sat.Literal.neg 56), (Sat.Literal.pos 856)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 855), (Sat.Literal.pos 35), (Sat.Literal.pos 56), (Sat.Literal.pos 856)] :=
  (lex_8_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 856) = lexBefore s permutation8 34 := by
  exact (positive_lex_of_descriptor s 856 permutation8 35 (by rfl)).trans ((lex_skipped s permutation8 34 35 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation8 34) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation8 34 by rw [image8_eq]; rfl))

theorem lex_8_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 857) (Sat.Literal.pos 856) (Sat.Literal.pos 34) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation8 34 (assignment s)
    (Sat.Literal.pos 857) (Sat.Literal.pos 856) (Sat.Literal.pos 34) (Sat.Literal.pos 40) (positive_of_descriptor s 857 (.lex permutation8 34) (by rfl)) (lex_8_34_prefix s) (positive_select s 34) (lex_8_34_image s)

theorem lex_8_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.pos 34), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation8 34 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 856) (Sat.Literal.pos 34) (Sat.Literal.pos 40) (lex_8_34_prefix s) (positive_select s 34) (lex_8_34_image s)

theorem lex_8_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.pos 856)] :=
  (lex_8_34_gate s).prop _ (List.Mem.head _)

theorem lex_8_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.neg 34), (Sat.Literal.pos 40)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.pos 34), (Sat.Literal.neg 40)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.neg 34), (Sat.Literal.neg 40), (Sat.Literal.pos 857)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 856), (Sat.Literal.pos 34), (Sat.Literal.pos 40), (Sat.Literal.pos 857)] :=
  (lex_8_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 857) = lexBefore s permutation8 33 := by
  exact (positive_lex_of_descriptor s 857 permutation8 34 (by rfl)).trans ((lex_skipped s permutation8 33 34 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation8 33) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation8 33 by rw [image8_eq]; rfl))

theorem lex_8_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 858) (Sat.Literal.pos 857) (Sat.Literal.pos 33) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation8 33 (assignment s)
    (Sat.Literal.pos 858) (Sat.Literal.pos 857) (Sat.Literal.pos 33) (Sat.Literal.pos 24) (positive_of_descriptor s 858 (.lex permutation8 33) (by rfl)) (lex_8_33_prefix s) (positive_select s 33) (lex_8_33_image s)

theorem lex_8_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.pos 33), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation8 33 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 857) (Sat.Literal.pos 33) (Sat.Literal.pos 24) (lex_8_33_prefix s) (positive_select s 33) (lex_8_33_image s)

theorem lex_8_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.pos 857)] :=
  (lex_8_33_gate s).prop _ (List.Mem.head _)

theorem lex_8_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.neg 33), (Sat.Literal.pos 24)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.pos 33), (Sat.Literal.neg 24)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.neg 33), (Sat.Literal.neg 24), (Sat.Literal.pos 858)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 857), (Sat.Literal.pos 33), (Sat.Literal.pos 24), (Sat.Literal.pos 858)] :=
  (lex_8_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_32_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 858) = lexBefore s permutation8 32 := by
  exact (positive_lex_of_descriptor s 858 permutation8 33 (by rfl)).trans ((lex_skipped s permutation8 32 33 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_32_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation8 32) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation8 32 by rw [image8_eq]; rfl))

theorem lex_8_32_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 859) (Sat.Literal.pos 858) (Sat.Literal.pos 32) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation8 32 (assignment s)
    (Sat.Literal.pos 859) (Sat.Literal.pos 858) (Sat.Literal.pos 32) (Sat.Literal.pos 8) (positive_of_descriptor s 859 (.lex permutation8 32) (by rfl)) (lex_8_32_prefix s) (positive_select s 32) (lex_8_32_image s)

theorem lex_8_32_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.pos 32), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation8 32 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 858) (Sat.Literal.pos 32) (Sat.Literal.pos 8) (lex_8_32_prefix s) (positive_select s 32) (lex_8_32_image s)

theorem lex_8_32_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.pos 858)] :=
  (lex_8_32_gate s).prop _ (List.Mem.head _)

theorem lex_8_32_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.neg 32), (Sat.Literal.pos 8)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_32_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.pos 32), (Sat.Literal.neg 8)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_32_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.neg 32), (Sat.Literal.neg 8), (Sat.Literal.pos 859)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_32_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 858), (Sat.Literal.pos 32), (Sat.Literal.pos 8), (Sat.Literal.pos 859)] :=
  (lex_8_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_31_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 859) = lexBefore s permutation8 31 := by
  exact (positive_lex_of_descriptor s 859 permutation8 32 (by rfl)).trans ((lex_skipped s permutation8 31 32 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_31_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation8 31) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation8 31 by rw [image8_eq]; rfl))

theorem lex_8_31_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 860) (Sat.Literal.pos 859) (Sat.Literal.pos 31) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation8 31 (assignment s)
    (Sat.Literal.pos 860) (Sat.Literal.pos 859) (Sat.Literal.pos 31) (Sat.Literal.pos 55) (positive_of_descriptor s 860 (.lex permutation8 31) (by rfl)) (lex_8_31_prefix s) (positive_select s 31) (lex_8_31_image s)

theorem lex_8_31_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.pos 31), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation8 31 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 859) (Sat.Literal.pos 31) (Sat.Literal.pos 55) (lex_8_31_prefix s) (positive_select s 31) (lex_8_31_image s)

theorem lex_8_31_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.pos 859)] :=
  (lex_8_31_gate s).prop _ (List.Mem.head _)

theorem lex_8_31_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.neg 31), (Sat.Literal.pos 55)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_31_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.pos 31), (Sat.Literal.neg 55)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_31_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.neg 31), (Sat.Literal.neg 55), (Sat.Literal.pos 860)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_31_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 859), (Sat.Literal.pos 31), (Sat.Literal.pos 55), (Sat.Literal.pos 860)] :=
  (lex_8_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 860) = lexBefore s permutation8 30 := by
  exact (positive_lex_of_descriptor s 860 permutation8 31 (by rfl)).trans ((lex_skipped s permutation8 30 31 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation8 30) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation8 30 by rw [image8_eq]; rfl))

theorem lex_8_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 861) (Sat.Literal.pos 860) (Sat.Literal.pos 30) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation8 30 (assignment s)
    (Sat.Literal.pos 861) (Sat.Literal.pos 860) (Sat.Literal.pos 30) (Sat.Literal.pos 39) (positive_of_descriptor s 861 (.lex permutation8 30) (by rfl)) (lex_8_30_prefix s) (positive_select s 30) (lex_8_30_image s)

theorem lex_8_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.pos 30), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation8 30 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 860) (Sat.Literal.pos 30) (Sat.Literal.pos 39) (lex_8_30_prefix s) (positive_select s 30) (lex_8_30_image s)

theorem lex_8_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.pos 860)] :=
  (lex_8_30_gate s).prop _ (List.Mem.head _)

theorem lex_8_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.neg 30), (Sat.Literal.pos 39)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.pos 30), (Sat.Literal.neg 39)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.neg 30), (Sat.Literal.neg 39), (Sat.Literal.pos 861)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 860), (Sat.Literal.pos 30), (Sat.Literal.pos 39), (Sat.Literal.pos 861)] :=
  (lex_8_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 861) = lexBefore s permutation8 29 := by
  exact (positive_lex_of_descriptor s 861 permutation8 30 (by rfl)).trans ((lex_skipped s permutation8 29 30 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation8 29) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation8 29 by rw [image8_eq]; rfl))

theorem lex_8_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 862) (Sat.Literal.pos 861) (Sat.Literal.pos 29) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation8 29 (assignment s)
    (Sat.Literal.pos 862) (Sat.Literal.pos 861) (Sat.Literal.pos 29) (Sat.Literal.pos 23) (positive_of_descriptor s 862 (.lex permutation8 29) (by rfl)) (lex_8_29_prefix s) (positive_select s 29) (lex_8_29_image s)

theorem lex_8_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.pos 29), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation8 29 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 861) (Sat.Literal.pos 29) (Sat.Literal.pos 23) (lex_8_29_prefix s) (positive_select s 29) (lex_8_29_image s)

theorem lex_8_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.pos 861)] :=
  (lex_8_29_gate s).prop _ (List.Mem.head _)

theorem lex_8_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.neg 29), (Sat.Literal.pos 23)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.pos 29), (Sat.Literal.neg 23)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.neg 29), (Sat.Literal.neg 23), (Sat.Literal.pos 862)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 861), (Sat.Literal.pos 29), (Sat.Literal.pos 23), (Sat.Literal.pos 862)] :=
  (lex_8_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 862) = lexBefore s permutation8 28 := by
  exact (positive_lex_of_descriptor s 862 permutation8 29 (by rfl)).trans ((lex_skipped s permutation8 28 29 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation8 28) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 64) = permuteMask permutation8 28 by rw [image8_eq]; rfl))

theorem lex_8_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 863) (Sat.Literal.pos 862) (Sat.Literal.pos 28) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation8 28 (assignment s)
    (Sat.Literal.pos 863) (Sat.Literal.pos 862) (Sat.Literal.pos 28) (Sat.Literal.pos 7) (positive_of_descriptor s 863 (.lex permutation8 28) (by rfl)) (lex_8_28_prefix s) (positive_select s 28) (lex_8_28_image s)

theorem lex_8_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.pos 28), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation8 28 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 862) (Sat.Literal.pos 28) (Sat.Literal.pos 7) (lex_8_28_prefix s) (positive_select s 28) (lex_8_28_image s)

theorem lex_8_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.pos 862)] :=
  (lex_8_28_gate s).prop _ (List.Mem.head _)

theorem lex_8_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.neg 28), (Sat.Literal.pos 7)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.pos 28), (Sat.Literal.neg 7)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.neg 28), (Sat.Literal.neg 7), (Sat.Literal.pos 863)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 862), (Sat.Literal.pos 28), (Sat.Literal.pos 7), (Sat.Literal.pos 863)] :=
  (lex_8_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 863) = lexBefore s permutation8 27 := by
  exact (positive_lex_of_descriptor s 863 permutation8 28 (by rfl)).trans ((lex_skipped s permutation8 27 28 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation8 27) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation8 27 by rw [image8_eq]; rfl))

theorem lex_8_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 864) (Sat.Literal.pos 863) (Sat.Literal.pos 27) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation8 27 (assignment s)
    (Sat.Literal.pos 864) (Sat.Literal.pos 863) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (positive_of_descriptor s 864 (.lex permutation8 27) (by rfl)) (lex_8_27_prefix s) (positive_select s 27) (lex_8_27_image s)

theorem lex_8_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation8 27 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 863) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (lex_8_27_prefix s) (positive_select s 27) (lex_8_27_image s)

theorem lex_8_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.pos 863)] :=
  (lex_8_27_gate s).prop _ (List.Mem.head _)

theorem lex_8_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.neg 27), (Sat.Literal.pos 54)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.neg 27), (Sat.Literal.neg 54), (Sat.Literal.pos 864)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 863), (Sat.Literal.pos 27), (Sat.Literal.pos 54), (Sat.Literal.pos 864)] :=
  (lex_8_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 864) = lexBefore s permutation8 26 := by
  exact (positive_lex_of_descriptor s 864 permutation8 27 (by rfl)).trans ((lex_skipped s permutation8 26 27 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation8 26) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation8 26 by rw [image8_eq]; rfl))

theorem lex_8_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 865) (Sat.Literal.pos 864) (Sat.Literal.pos 26) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation8 26 (assignment s)
    (Sat.Literal.pos 865) (Sat.Literal.pos 864) (Sat.Literal.pos 26) (Sat.Literal.pos 38) (positive_of_descriptor s 865 (.lex permutation8 26) (by rfl)) (lex_8_26_prefix s) (positive_select s 26) (lex_8_26_image s)

theorem lex_8_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.pos 26), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation8 26 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 864) (Sat.Literal.pos 26) (Sat.Literal.pos 38) (lex_8_26_prefix s) (positive_select s 26) (lex_8_26_image s)

theorem lex_8_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.pos 864)] :=
  (lex_8_26_gate s).prop _ (List.Mem.head _)

theorem lex_8_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.neg 26), (Sat.Literal.pos 38)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.pos 26), (Sat.Literal.neg 38)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.neg 26), (Sat.Literal.neg 38), (Sat.Literal.pos 865)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 864), (Sat.Literal.pos 26), (Sat.Literal.pos 38), (Sat.Literal.pos 865)] :=
  (lex_8_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 865) = lexBefore s permutation8 25 := by
  exact (positive_lex_of_descriptor s 865 permutation8 26 (by rfl)).trans ((lex_skipped s permutation8 25 26 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation8 25) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation8 25 by rw [image8_eq]; rfl))

theorem lex_8_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 866) (Sat.Literal.pos 865) (Sat.Literal.pos 25) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation8 25 (assignment s)
    (Sat.Literal.pos 866) (Sat.Literal.pos 865) (Sat.Literal.pos 25) (Sat.Literal.pos 22) (positive_of_descriptor s 866 (.lex permutation8 25) (by rfl)) (lex_8_25_prefix s) (positive_select s 25) (lex_8_25_image s)

theorem lex_8_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.pos 25), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation8 25 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 865) (Sat.Literal.pos 25) (Sat.Literal.pos 22) (lex_8_25_prefix s) (positive_select s 25) (lex_8_25_image s)

theorem lex_8_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.pos 865)] :=
  (lex_8_25_gate s).prop _ (List.Mem.head _)

theorem lex_8_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.neg 25), (Sat.Literal.pos 22)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.pos 25), (Sat.Literal.neg 22)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.neg 25), (Sat.Literal.neg 22), (Sat.Literal.pos 866)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 865), (Sat.Literal.pos 25), (Sat.Literal.pos 22), (Sat.Literal.pos 866)] :=
  (lex_8_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 866) = lexBefore s permutation8 24 := by
  exact (positive_lex_of_descriptor s 866 permutation8 25 (by rfl)).trans ((lex_skipped s permutation8 24 25 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation8 24) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation8 24 by rw [image8_eq]; rfl))

theorem lex_8_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 867) (Sat.Literal.pos 866) (Sat.Literal.pos 24) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation8 24 (assignment s)
    (Sat.Literal.pos 867) (Sat.Literal.pos 866) (Sat.Literal.pos 24) (Sat.Literal.pos 6) (positive_of_descriptor s 867 (.lex permutation8 24) (by rfl)) (lex_8_24_prefix s) (positive_select s 24) (lex_8_24_image s)

theorem lex_8_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.pos 24), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation8 24 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 866) (Sat.Literal.pos 24) (Sat.Literal.pos 6) (lex_8_24_prefix s) (positive_select s 24) (lex_8_24_image s)

theorem lex_8_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.pos 866)] :=
  (lex_8_24_gate s).prop _ (List.Mem.head _)

theorem lex_8_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.neg 24), (Sat.Literal.pos 6)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.pos 24), (Sat.Literal.neg 6)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.neg 24), (Sat.Literal.neg 6), (Sat.Literal.pos 867)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 866), (Sat.Literal.pos 24), (Sat.Literal.pos 6), (Sat.Literal.pos 867)] :=
  (lex_8_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 867) = lexBefore s permutation8 23 := by
  exact (positive_lex_of_descriptor s 867 permutation8 24 (by rfl)).trans ((lex_skipped s permutation8 23 24 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation8 23) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation8 23 by rw [image8_eq]; rfl))

theorem lex_8_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 868) (Sat.Literal.pos 867) (Sat.Literal.pos 23) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation8 23 (assignment s)
    (Sat.Literal.pos 868) (Sat.Literal.pos 867) (Sat.Literal.pos 23) (Sat.Literal.pos 53) (positive_of_descriptor s 868 (.lex permutation8 23) (by rfl)) (lex_8_23_prefix s) (positive_select s 23) (lex_8_23_image s)

theorem lex_8_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.pos 23), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation8 23 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 867) (Sat.Literal.pos 23) (Sat.Literal.pos 53) (lex_8_23_prefix s) (positive_select s 23) (lex_8_23_image s)

theorem lex_8_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.pos 867)] :=
  (lex_8_23_gate s).prop _ (List.Mem.head _)

theorem lex_8_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.neg 23), (Sat.Literal.pos 53)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.pos 23), (Sat.Literal.neg 53)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.neg 23), (Sat.Literal.neg 53), (Sat.Literal.pos 868)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 867), (Sat.Literal.pos 23), (Sat.Literal.pos 53), (Sat.Literal.pos 868)] :=
  (lex_8_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 868) = lexBefore s permutation8 22 := by
  exact (positive_lex_of_descriptor s 868 permutation8 23 (by rfl)).trans ((lex_skipped s permutation8 22 23 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation8 22) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation8 22 by rw [image8_eq]; rfl))

theorem lex_8_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 869) (Sat.Literal.pos 868) (Sat.Literal.pos 22) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation8 22 (assignment s)
    (Sat.Literal.pos 869) (Sat.Literal.pos 868) (Sat.Literal.pos 22) (Sat.Literal.pos 37) (positive_of_descriptor s 869 (.lex permutation8 22) (by rfl)) (lex_8_22_prefix s) (positive_select s 22) (lex_8_22_image s)

theorem lex_8_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.pos 22), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation8 22 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 868) (Sat.Literal.pos 22) (Sat.Literal.pos 37) (lex_8_22_prefix s) (positive_select s 22) (lex_8_22_image s)

theorem lex_8_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.pos 868)] :=
  (lex_8_22_gate s).prop _ (List.Mem.head _)

theorem lex_8_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.neg 22), (Sat.Literal.pos 37)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.pos 22), (Sat.Literal.neg 37)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.neg 22), (Sat.Literal.neg 37), (Sat.Literal.pos 869)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 868), (Sat.Literal.pos 22), (Sat.Literal.pos 37), (Sat.Literal.pos 869)] :=
  (lex_8_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 869) = lexBefore s permutation8 20 := by
  exact (positive_lex_of_descriptor s 869 permutation8 22 (by rfl)).trans ((lex_skipped s permutation8 20 22 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 21 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation8 20) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation8 20 by rw [image8_eq]; rfl))

theorem lex_8_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 870) (Sat.Literal.pos 869) (Sat.Literal.pos 20) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation8 20 (assignment s)
    (Sat.Literal.pos 870) (Sat.Literal.pos 869) (Sat.Literal.pos 20) (Sat.Literal.pos 5) (positive_of_descriptor s 870 (.lex permutation8 20) (by rfl)) (lex_8_20_prefix s) (positive_select s 20) (lex_8_20_image s)

theorem lex_8_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.pos 20), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation8 20 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 869) (Sat.Literal.pos 20) (Sat.Literal.pos 5) (lex_8_20_prefix s) (positive_select s 20) (lex_8_20_image s)

theorem lex_8_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.pos 869)] :=
  (lex_8_20_gate s).prop _ (List.Mem.head _)

theorem lex_8_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.neg 20), (Sat.Literal.pos 5)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.pos 20), (Sat.Literal.neg 5)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.neg 20), (Sat.Literal.neg 5), (Sat.Literal.pos 870)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 869), (Sat.Literal.pos 20), (Sat.Literal.pos 5), (Sat.Literal.pos 870)] :=
  (lex_8_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 870) = lexBefore s permutation8 19 := by
  exact (positive_lex_of_descriptor s 870 permutation8 20 (by rfl)).trans ((lex_skipped s permutation8 19 20 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation8 19) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation8 19 by rw [image8_eq]; rfl))

theorem lex_8_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 871) (Sat.Literal.pos 870) (Sat.Literal.pos 19) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation8 19 (assignment s)
    (Sat.Literal.pos 871) (Sat.Literal.pos 870) (Sat.Literal.pos 19) (Sat.Literal.pos 52) (positive_of_descriptor s 871 (.lex permutation8 19) (by rfl)) (lex_8_19_prefix s) (positive_select s 19) (lex_8_19_image s)

theorem lex_8_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.pos 19), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation8 19 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 870) (Sat.Literal.pos 19) (Sat.Literal.pos 52) (lex_8_19_prefix s) (positive_select s 19) (lex_8_19_image s)

theorem lex_8_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.pos 870)] :=
  (lex_8_19_gate s).prop _ (List.Mem.head _)

theorem lex_8_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.neg 19), (Sat.Literal.pos 52)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.pos 19), (Sat.Literal.neg 52)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.neg 19), (Sat.Literal.neg 52), (Sat.Literal.pos 871)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 870), (Sat.Literal.pos 19), (Sat.Literal.pos 52), (Sat.Literal.pos 871)] :=
  (lex_8_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 871) = lexBefore s permutation8 18 := by
  exact (positive_lex_of_descriptor s 871 permutation8 19 (by rfl)).trans ((lex_skipped s permutation8 18 19 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation8 18) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation8 18 by rw [image8_eq]; rfl))

theorem lex_8_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 872) (Sat.Literal.pos 871) (Sat.Literal.pos 18) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation8 18 (assignment s)
    (Sat.Literal.pos 872) (Sat.Literal.pos 871) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (positive_of_descriptor s 872 (.lex permutation8 18) (by rfl)) (lex_8_18_prefix s) (positive_select s 18) (lex_8_18_image s)

theorem lex_8_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation8 18 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 871) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (lex_8_18_prefix s) (positive_select s 18) (lex_8_18_image s)

theorem lex_8_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.pos 871)] :=
  (lex_8_18_gate s).prop _ (List.Mem.head _)

theorem lex_8_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.neg 18), (Sat.Literal.pos 36)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.neg 18), (Sat.Literal.neg 36), (Sat.Literal.pos 872)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 871), (Sat.Literal.pos 18), (Sat.Literal.pos 36), (Sat.Literal.pos 872)] :=
  (lex_8_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 872) = lexBefore s permutation8 17 := by
  exact (positive_lex_of_descriptor s 872 permutation8 18 (by rfl)).trans ((lex_skipped s permutation8 17 18 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation8 17) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation8 17 by rw [image8_eq]; rfl))

theorem lex_8_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 873) (Sat.Literal.pos 872) (Sat.Literal.pos 17) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation8 17 (assignment s)
    (Sat.Literal.pos 873) (Sat.Literal.pos 872) (Sat.Literal.pos 17) (Sat.Literal.pos 20) (positive_of_descriptor s 873 (.lex permutation8 17) (by rfl)) (lex_8_17_prefix s) (positive_select s 17) (lex_8_17_image s)

theorem lex_8_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.pos 17), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation8 17 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 872) (Sat.Literal.pos 17) (Sat.Literal.pos 20) (lex_8_17_prefix s) (positive_select s 17) (lex_8_17_image s)

theorem lex_8_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.pos 872)] :=
  (lex_8_17_gate s).prop _ (List.Mem.head _)

theorem lex_8_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.neg 17), (Sat.Literal.pos 20)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.pos 17), (Sat.Literal.neg 20)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.neg 17), (Sat.Literal.neg 20), (Sat.Literal.pos 873)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 872), (Sat.Literal.pos 17), (Sat.Literal.pos 20), (Sat.Literal.pos 873)] :=
  (lex_8_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 873) = lexBefore s permutation8 16 := by
  exact (positive_lex_of_descriptor s 873 permutation8 17 (by rfl)).trans ((lex_skipped s permutation8 16 17 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation8 16) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation8 16 by rw [image8_eq]; rfl))

theorem lex_8_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 874) (Sat.Literal.pos 873) (Sat.Literal.pos 16) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation8 16 (assignment s)
    (Sat.Literal.pos 874) (Sat.Literal.pos 873) (Sat.Literal.pos 16) (Sat.Literal.pos 4) (positive_of_descriptor s 874 (.lex permutation8 16) (by rfl)) (lex_8_16_prefix s) (positive_select s 16) (lex_8_16_image s)

theorem lex_8_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.pos 16), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation8 16 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 873) (Sat.Literal.pos 16) (Sat.Literal.pos 4) (lex_8_16_prefix s) (positive_select s 16) (lex_8_16_image s)

theorem lex_8_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.pos 873)] :=
  (lex_8_16_gate s).prop _ (List.Mem.head _)

theorem lex_8_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.neg 16), (Sat.Literal.pos 4)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.pos 16), (Sat.Literal.neg 4)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.neg 16), (Sat.Literal.neg 4), (Sat.Literal.pos 874)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 873), (Sat.Literal.pos 16), (Sat.Literal.pos 4), (Sat.Literal.pos 874)] :=
  (lex_8_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_15_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 874) = lexBefore s permutation8 15 := by
  exact (positive_lex_of_descriptor s 874 permutation8 16 (by rfl)).trans ((lex_skipped s permutation8 15 16 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_15_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation8 15) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation8 15 by rw [image8_eq]; rfl))

theorem lex_8_15_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 875) (Sat.Literal.pos 874) (Sat.Literal.pos 15) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation8 15 (assignment s)
    (Sat.Literal.pos 875) (Sat.Literal.pos 874) (Sat.Literal.pos 15) (Sat.Literal.pos 51) (positive_of_descriptor s 875 (.lex permutation8 15) (by rfl)) (lex_8_15_prefix s) (positive_select s 15) (lex_8_15_image s)

theorem lex_8_15_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.pos 15), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation8 15 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 874) (Sat.Literal.pos 15) (Sat.Literal.pos 51) (lex_8_15_prefix s) (positive_select s 15) (lex_8_15_image s)

theorem lex_8_15_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.pos 874)] :=
  (lex_8_15_gate s).prop _ (List.Mem.head _)

theorem lex_8_15_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.neg 15), (Sat.Literal.pos 51)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_15_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.pos 15), (Sat.Literal.neg 51)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_15_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.neg 15), (Sat.Literal.neg 51), (Sat.Literal.pos 875)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_15_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 874), (Sat.Literal.pos 15), (Sat.Literal.pos 51), (Sat.Literal.pos 875)] :=
  (lex_8_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 875) = lexBefore s permutation8 14 := by
  exact (positive_lex_of_descriptor s 875 permutation8 15 (by rfl)).trans ((lex_skipped s permutation8 14 15 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation8 14) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation8 14 by rw [image8_eq]; rfl))

theorem lex_8_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 876) (Sat.Literal.pos 875) (Sat.Literal.pos 14) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation8 14 (assignment s)
    (Sat.Literal.pos 876) (Sat.Literal.pos 875) (Sat.Literal.pos 14) (Sat.Literal.pos 35) (positive_of_descriptor s 876 (.lex permutation8 14) (by rfl)) (lex_8_14_prefix s) (positive_select s 14) (lex_8_14_image s)

theorem lex_8_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.pos 14), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation8 14 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 875) (Sat.Literal.pos 14) (Sat.Literal.pos 35) (lex_8_14_prefix s) (positive_select s 14) (lex_8_14_image s)

theorem lex_8_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.pos 875)] :=
  (lex_8_14_gate s).prop _ (List.Mem.head _)

theorem lex_8_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.neg 14), (Sat.Literal.pos 35)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.pos 14), (Sat.Literal.neg 35)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.neg 14), (Sat.Literal.neg 35), (Sat.Literal.pos 876)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 875), (Sat.Literal.pos 14), (Sat.Literal.pos 35), (Sat.Literal.pos 876)] :=
  (lex_8_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 876) = lexBefore s permutation8 13 := by
  exact (positive_lex_of_descriptor s 876 permutation8 14 (by rfl)).trans ((lex_skipped s permutation8 13 14 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation8 13) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation8 13 by rw [image8_eq]; rfl))

theorem lex_8_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 877) (Sat.Literal.pos 876) (Sat.Literal.pos 13) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation8 13 (assignment s)
    (Sat.Literal.pos 877) (Sat.Literal.pos 876) (Sat.Literal.pos 13) (Sat.Literal.pos 19) (positive_of_descriptor s 877 (.lex permutation8 13) (by rfl)) (lex_8_13_prefix s) (positive_select s 13) (lex_8_13_image s)

theorem lex_8_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.pos 13), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation8 13 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 876) (Sat.Literal.pos 13) (Sat.Literal.pos 19) (lex_8_13_prefix s) (positive_select s 13) (lex_8_13_image s)

theorem lex_8_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.pos 876)] :=
  (lex_8_13_gate s).prop _ (List.Mem.head _)

theorem lex_8_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.neg 13), (Sat.Literal.pos 19)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.pos 13), (Sat.Literal.neg 19)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.neg 13), (Sat.Literal.neg 19), (Sat.Literal.pos 877)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 876), (Sat.Literal.pos 13), (Sat.Literal.pos 19), (Sat.Literal.pos 877)] :=
  (lex_8_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 877) = lexBefore s permutation8 12 := by
  exact (positive_lex_of_descriptor s 877 permutation8 13 (by rfl)).trans ((lex_skipped s permutation8 12 13 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation8 12) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 64) = permuteMask permutation8 12 by rw [image8_eq]; rfl))

theorem lex_8_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 878) (Sat.Literal.pos 877) (Sat.Literal.pos 12) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation8 12 (assignment s)
    (Sat.Literal.pos 878) (Sat.Literal.pos 877) (Sat.Literal.pos 12) (Sat.Literal.pos 3) (positive_of_descriptor s 878 (.lex permutation8 12) (by rfl)) (lex_8_12_prefix s) (positive_select s 12) (lex_8_12_image s)

theorem lex_8_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.pos 12), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation8 12 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 877) (Sat.Literal.pos 12) (Sat.Literal.pos 3) (lex_8_12_prefix s) (positive_select s 12) (lex_8_12_image s)

theorem lex_8_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.pos 877)] :=
  (lex_8_12_gate s).prop _ (List.Mem.head _)

theorem lex_8_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.neg 12), (Sat.Literal.pos 3)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.pos 12), (Sat.Literal.neg 3)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.neg 12), (Sat.Literal.neg 3), (Sat.Literal.pos 878)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 877), (Sat.Literal.pos 12), (Sat.Literal.pos 3), (Sat.Literal.pos 878)] :=
  (lex_8_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 878) = lexBefore s permutation8 11 := by
  exact (positive_lex_of_descriptor s 878 permutation8 12 (by rfl)).trans ((lex_skipped s permutation8 11 12 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation8 11) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation8 11 by rw [image8_eq]; rfl))

theorem lex_8_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 879) (Sat.Literal.pos 878) (Sat.Literal.pos 11) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation8 11 (assignment s)
    (Sat.Literal.pos 879) (Sat.Literal.pos 878) (Sat.Literal.pos 11) (Sat.Literal.pos 50) (positive_of_descriptor s 879 (.lex permutation8 11) (by rfl)) (lex_8_11_prefix s) (positive_select s 11) (lex_8_11_image s)

theorem lex_8_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.pos 11), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation8 11 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 878) (Sat.Literal.pos 11) (Sat.Literal.pos 50) (lex_8_11_prefix s) (positive_select s 11) (lex_8_11_image s)

theorem lex_8_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.pos 878)] :=
  (lex_8_11_gate s).prop _ (List.Mem.head _)

theorem lex_8_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.neg 11), (Sat.Literal.pos 50)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.pos 11), (Sat.Literal.neg 50)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.neg 11), (Sat.Literal.neg 50), (Sat.Literal.pos 879)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 878), (Sat.Literal.pos 11), (Sat.Literal.pos 50), (Sat.Literal.pos 879)] :=
  (lex_8_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 879) = lexBefore s permutation8 10 := by
  exact (positive_lex_of_descriptor s 879 permutation8 11 (by rfl)).trans ((lex_skipped s permutation8 10 11 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation8 10) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation8 10 by rw [image8_eq]; rfl))

theorem lex_8_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 880) (Sat.Literal.pos 879) (Sat.Literal.pos 10) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation8 10 (assignment s)
    (Sat.Literal.pos 880) (Sat.Literal.pos 879) (Sat.Literal.pos 10) (Sat.Literal.pos 34) (positive_of_descriptor s 880 (.lex permutation8 10) (by rfl)) (lex_8_10_prefix s) (positive_select s 10) (lex_8_10_image s)

theorem lex_8_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.pos 10), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation8 10 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 879) (Sat.Literal.pos 10) (Sat.Literal.pos 34) (lex_8_10_prefix s) (positive_select s 10) (lex_8_10_image s)

theorem lex_8_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.pos 879)] :=
  (lex_8_10_gate s).prop _ (List.Mem.head _)

theorem lex_8_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.neg 10), (Sat.Literal.pos 34)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.pos 10), (Sat.Literal.neg 34)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.neg 10), (Sat.Literal.neg 34), (Sat.Literal.pos 880)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 879), (Sat.Literal.pos 10), (Sat.Literal.pos 34), (Sat.Literal.pos 880)] :=
  (lex_8_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 880) = lexBefore s permutation8 9 := by
  exact (positive_lex_of_descriptor s 880 permutation8 10 (by rfl)).trans ((lex_skipped s permutation8 9 10 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation8 9) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation8 9 by rw [image8_eq]; rfl))

theorem lex_8_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 881) (Sat.Literal.pos 880) (Sat.Literal.pos 9) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation8 9 (assignment s)
    (Sat.Literal.pos 881) (Sat.Literal.pos 880) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (positive_of_descriptor s 881 (.lex permutation8 9) (by rfl)) (lex_8_9_prefix s) (positive_select s 9) (lex_8_9_image s)

theorem lex_8_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation8 9 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 880) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (lex_8_9_prefix s) (positive_select s 9) (lex_8_9_image s)

theorem lex_8_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.pos 880)] :=
  (lex_8_9_gate s).prop _ (List.Mem.head _)

theorem lex_8_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.neg 9), (Sat.Literal.pos 18)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.neg 9), (Sat.Literal.neg 18), (Sat.Literal.pos 881)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 880), (Sat.Literal.pos 9), (Sat.Literal.pos 18), (Sat.Literal.pos 881)] :=
  (lex_8_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 881) = lexBefore s permutation8 8 := by
  exact (positive_lex_of_descriptor s 881 permutation8 9 (by rfl)).trans ((lex_skipped s permutation8 8 9 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation8 8) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation8 8 by rw [image8_eq]; rfl))

theorem lex_8_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 882) (Sat.Literal.pos 881) (Sat.Literal.pos 8) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation8 8 (assignment s)
    (Sat.Literal.pos 882) (Sat.Literal.pos 881) (Sat.Literal.pos 8) (Sat.Literal.pos 2) (positive_of_descriptor s 882 (.lex permutation8 8) (by rfl)) (lex_8_8_prefix s) (positive_select s 8) (lex_8_8_image s)

theorem lex_8_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.pos 8), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation8 8 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 881) (Sat.Literal.pos 8) (Sat.Literal.pos 2) (lex_8_8_prefix s) (positive_select s 8) (lex_8_8_image s)

theorem lex_8_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.pos 881)] :=
  (lex_8_8_gate s).prop _ (List.Mem.head _)

theorem lex_8_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.neg 8), (Sat.Literal.pos 2)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.pos 8), (Sat.Literal.neg 2)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.neg 8), (Sat.Literal.neg 2), (Sat.Literal.pos 882)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 881), (Sat.Literal.pos 8), (Sat.Literal.pos 2), (Sat.Literal.pos 882)] :=
  (lex_8_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_7_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 882) = lexBefore s permutation8 7 := by
  exact (positive_lex_of_descriptor s 882 permutation8 8 (by rfl)).trans ((lex_skipped s permutation8 7 8 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_7_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation8 7) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation8 7 by rw [image8_eq]; rfl))

theorem lex_8_7_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 883) (Sat.Literal.pos 882) (Sat.Literal.pos 7) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation8 7 (assignment s)
    (Sat.Literal.pos 883) (Sat.Literal.pos 882) (Sat.Literal.pos 7) (Sat.Literal.pos 49) (positive_of_descriptor s 883 (.lex permutation8 7) (by rfl)) (lex_8_7_prefix s) (positive_select s 7) (lex_8_7_image s)

theorem lex_8_7_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.pos 7), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation8 7 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 882) (Sat.Literal.pos 7) (Sat.Literal.pos 49) (lex_8_7_prefix s) (positive_select s 7) (lex_8_7_image s)

theorem lex_8_7_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.pos 882)] :=
  (lex_8_7_gate s).prop _ (List.Mem.head _)

theorem lex_8_7_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.neg 7), (Sat.Literal.pos 49)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_7_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.pos 7), (Sat.Literal.neg 49)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_7_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.neg 7), (Sat.Literal.neg 49), (Sat.Literal.pos 883)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_7_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 882), (Sat.Literal.pos 7), (Sat.Literal.pos 49), (Sat.Literal.pos 883)] :=
  (lex_8_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 883) = lexBefore s permutation8 6 := by
  exact (positive_lex_of_descriptor s 883 permutation8 7 (by rfl)).trans ((lex_skipped s permutation8 6 7 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation8 6) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation8 6 by rw [image8_eq]; rfl))

theorem lex_8_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 884) (Sat.Literal.pos 883) (Sat.Literal.pos 6) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation8 6 (assignment s)
    (Sat.Literal.pos 884) (Sat.Literal.pos 883) (Sat.Literal.pos 6) (Sat.Literal.pos 33) (positive_of_descriptor s 884 (.lex permutation8 6) (by rfl)) (lex_8_6_prefix s) (positive_select s 6) (lex_8_6_image s)

theorem lex_8_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.pos 6), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation8 6 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 883) (Sat.Literal.pos 6) (Sat.Literal.pos 33) (lex_8_6_prefix s) (positive_select s 6) (lex_8_6_image s)

theorem lex_8_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.pos 883)] :=
  (lex_8_6_gate s).prop _ (List.Mem.head _)

theorem lex_8_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.neg 6), (Sat.Literal.pos 33)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.pos 6), (Sat.Literal.neg 33)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.neg 6), (Sat.Literal.neg 33), (Sat.Literal.pos 884)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 883), (Sat.Literal.pos 6), (Sat.Literal.pos 33), (Sat.Literal.pos 884)] :=
  (lex_8_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 884) = lexBefore s permutation8 5 := by
  exact (positive_lex_of_descriptor s 884 permutation8 6 (by rfl)).trans ((lex_skipped s permutation8 5 6 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation8 5) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation8 5 by rw [image8_eq]; rfl))

theorem lex_8_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 885) (Sat.Literal.pos 884) (Sat.Literal.pos 5) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation8 5 (assignment s)
    (Sat.Literal.pos 885) (Sat.Literal.pos 884) (Sat.Literal.pos 5) (Sat.Literal.pos 17) (positive_of_descriptor s 885 (.lex permutation8 5) (by rfl)) (lex_8_5_prefix s) (positive_select s 5) (lex_8_5_image s)

theorem lex_8_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.pos 5), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation8 5 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 884) (Sat.Literal.pos 5) (Sat.Literal.pos 17) (lex_8_5_prefix s) (positive_select s 5) (lex_8_5_image s)

theorem lex_8_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.pos 884)] :=
  (lex_8_5_gate s).prop _ (List.Mem.head _)

theorem lex_8_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.neg 5), (Sat.Literal.pos 17)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.pos 5), (Sat.Literal.neg 17)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.neg 5), (Sat.Literal.neg 17), (Sat.Literal.pos 885)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 884), (Sat.Literal.pos 5), (Sat.Literal.pos 17), (Sat.Literal.pos 885)] :=
  (lex_8_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 885) = lexBefore s permutation8 4 := by
  exact (positive_lex_of_descriptor s 885 permutation8 5 (by rfl)).trans ((lex_skipped s permutation8 4 5 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation8 4) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 64) = permuteMask permutation8 4 by rw [image8_eq]; rfl))

theorem lex_8_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 886) (Sat.Literal.pos 885) (Sat.Literal.pos 4) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation8 4 (assignment s)
    (Sat.Literal.pos 886) (Sat.Literal.pos 885) (Sat.Literal.pos 4) (Sat.Literal.pos 1) (positive_of_descriptor s 886 (.lex permutation8 4) (by rfl)) (lex_8_4_prefix s) (positive_select s 4) (lex_8_4_image s)

theorem lex_8_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.pos 4), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation8 4 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 885) (Sat.Literal.pos 4) (Sat.Literal.pos 1) (lex_8_4_prefix s) (positive_select s 4) (lex_8_4_image s)

theorem lex_8_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.pos 885)] :=
  (lex_8_4_gate s).prop _ (List.Mem.head _)

theorem lex_8_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.neg 4), (Sat.Literal.pos 1)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.pos 4), (Sat.Literal.neg 1)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.neg 4), (Sat.Literal.neg 1), (Sat.Literal.pos 886)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 885), (Sat.Literal.pos 4), (Sat.Literal.pos 1), (Sat.Literal.pos 886)] :=
  (lex_8_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_3_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 886) = lexBefore s permutation8 3 := by
  exact (positive_lex_of_descriptor s 886 permutation8 4 (by rfl)).trans ((lex_skipped s permutation8 3 4 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_3_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation8 3) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 64) = permuteMask permutation8 3 by rw [image8_eq]; rfl))

theorem lex_8_3_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 887) (Sat.Literal.pos 886) (Sat.Literal.pos 3) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation8 3 (assignment s)
    (Sat.Literal.pos 887) (Sat.Literal.pos 886) (Sat.Literal.pos 3) (Sat.Literal.pos 48) (positive_of_descriptor s 887 (.lex permutation8 3) (by rfl)) (lex_8_3_prefix s) (positive_select s 3) (lex_8_3_image s)

theorem lex_8_3_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.pos 3), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation8 3 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 886) (Sat.Literal.pos 3) (Sat.Literal.pos 48) (lex_8_3_prefix s) (positive_select s 3) (lex_8_3_image s)

theorem lex_8_3_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.pos 886)] :=
  (lex_8_3_gate s).prop _ (List.Mem.head _)

theorem lex_8_3_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.neg 3), (Sat.Literal.pos 48)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_3_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.pos 3), (Sat.Literal.neg 48)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_3_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.neg 3), (Sat.Literal.neg 48), (Sat.Literal.pos 887)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_3_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 886), (Sat.Literal.pos 3), (Sat.Literal.pos 48), (Sat.Literal.pos 887)] :=
  (lex_8_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 887) = lexBefore s permutation8 2 := by
  exact (positive_lex_of_descriptor s 887 permutation8 3 (by rfl)).trans ((lex_skipped s permutation8 2 3 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation8 2) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 64) = permuteMask permutation8 2 by rw [image8_eq]; rfl))

theorem lex_8_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 888) (Sat.Literal.pos 887) (Sat.Literal.pos 2) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation8 2 (assignment s)
    (Sat.Literal.pos 888) (Sat.Literal.pos 887) (Sat.Literal.pos 2) (Sat.Literal.pos 32) (positive_of_descriptor s 888 (.lex permutation8 2) (by rfl)) (lex_8_2_prefix s) (positive_select s 2) (lex_8_2_image s)

theorem lex_8_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.pos 2), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation8 2 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 887) (Sat.Literal.pos 2) (Sat.Literal.pos 32) (lex_8_2_prefix s) (positive_select s 2) (lex_8_2_image s)

theorem lex_8_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.pos 887)] :=
  (lex_8_2_gate s).prop _ (List.Mem.head _)

theorem lex_8_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.neg 2), (Sat.Literal.pos 32)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.pos 2), (Sat.Literal.neg 32)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.neg 2), (Sat.Literal.neg 32), (Sat.Literal.pos 888)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 887), (Sat.Literal.pos 2), (Sat.Literal.pos 32), (Sat.Literal.pos 888)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_1_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 888) = lexBefore s permutation8 1 := by
  exact (positive_lex_of_descriptor s 888 permutation8 2 (by rfl)).trans ((lex_skipped s permutation8 1 2 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_1_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation8 1) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation8 1 by rw [image8_eq]; rfl))

theorem lex_8_1_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 889) (Sat.Literal.pos 888) (Sat.Literal.pos 1) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation8 1 (assignment s)
    (Sat.Literal.pos 889) (Sat.Literal.pos 888) (Sat.Literal.pos 1) (Sat.Literal.pos 16) (positive_of_descriptor s 889 (.lex permutation8 1) (by rfl)) (lex_8_1_prefix s) (positive_select s 1) (lex_8_1_image s)

theorem lex_8_1_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.pos 1), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation8 1 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 888) (Sat.Literal.pos 1) (Sat.Literal.pos 16) (lex_8_1_prefix s) (positive_select s 1) (lex_8_1_image s)

theorem lex_8_1_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 889), (Sat.Literal.pos 888)] :=
  (lex_8_1_gate s).prop _ (List.Mem.head _)

theorem lex_8_1_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 889), (Sat.Literal.neg 1), (Sat.Literal.pos 16)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_1_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 889), (Sat.Literal.pos 1), (Sat.Literal.neg 16)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_1_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.neg 1), (Sat.Literal.neg 16), (Sat.Literal.pos 889)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_1_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 888), (Sat.Literal.pos 1), (Sat.Literal.pos 16), (Sat.Literal.pos 889)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation9 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation9 62 (by intro j hj; rw [image9_eq]; exact fixedOnRange_spec image9 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_9_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation9 62) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation9 62 by rw [image9_eq]; rfl))

theorem lex_9_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 890) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation9 62 (assignment s)
    (Sat.Literal.pos 890) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 31) (positive_of_descriptor s 890 (.lex permutation9 62) (by rfl)) (lex_9_62_prefix s) (positive_select s 62) (lex_9_62_image s)

theorem lex_9_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation9 62 (hmax permutation9) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 31) (lex_9_62_prefix s) (positive_select s 62) (lex_9_62_image s)

theorem lex_9_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.neg 64)] :=
  (lex_9_62_gate s).prop _ (List.Mem.head _)

theorem lex_9_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.neg 62), (Sat.Literal.pos 31)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.pos 62), (Sat.Literal.neg 31)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 31), (Sat.Literal.pos 890)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 31), (Sat.Literal.pos 890)] :=
  (lex_9_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 890) = lexBefore s permutation9 61 := by
  exact (positive_lex_of_descriptor s 890 permutation9 62 (by rfl)).trans ((lex_skipped s permutation9 61 62 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation9 61) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation9 61 by rw [image9_eq]; rfl))

theorem lex_9_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 891) (Sat.Literal.pos 890) (Sat.Literal.pos 61) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation9 61 (assignment s)
    (Sat.Literal.pos 891) (Sat.Literal.pos 890) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (positive_of_descriptor s 891 (.lex permutation9 61) (by rfl)) (lex_9_61_prefix s) (positive_select s 61) (lex_9_61_image s)

theorem lex_9_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation9 61 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 890) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (lex_9_61_prefix s) (positive_select s 61) (lex_9_61_image s)

theorem lex_9_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 891), (Sat.Literal.pos 890)] :=
  (lex_9_61_gate s).prop _ (List.Mem.head _)

theorem lex_9_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 891), (Sat.Literal.neg 61), (Sat.Literal.pos 62)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 891), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.neg 61), (Sat.Literal.neg 62), (Sat.Literal.pos 891)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 890), (Sat.Literal.pos 61), (Sat.Literal.pos 62), (Sat.Literal.pos 891)] :=
  (lex_9_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_7_42_gate

end Crown.CertificateSixData
