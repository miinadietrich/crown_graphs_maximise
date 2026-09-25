import Crown.CertificateSixLexLookup
import Crown.CertificateSixRanges

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly Crown.CertificateSixAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_5_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 691) = lexBefore s permutation5 22 := by
  exact (positive_lex_of_descriptor s 691 permutation5 23 (by rfl)).trans ((lex_skipped s permutation5 22 23 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation5 22) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation5 22 by rw [image5_eq]; rfl))

theorem lex_5_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 692) (Sat.Literal.pos 691) (Sat.Literal.pos 22) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation5 22 (assignment s)
    (Sat.Literal.pos 692) (Sat.Literal.pos 691) (Sat.Literal.pos 22) (Sat.Literal.pos 44) (positive_of_descriptor s 692 (.lex permutation5 22) (by rfl)) (lex_5_22_prefix s) (positive_select s 22) (lex_5_22_image s)

theorem lex_5_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.pos 22), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation5 22 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 691) (Sat.Literal.pos 22) (Sat.Literal.pos 44) (lex_5_22_prefix s) (positive_select s 22) (lex_5_22_image s)

theorem lex_5_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.pos 691)] :=
  (lex_5_22_gate s).prop _ (List.Mem.head _)

theorem lex_5_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.neg 22), (Sat.Literal.pos 44)] :=
  (lex_5_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.pos 22), (Sat.Literal.neg 44)] :=
  (lex_5_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.neg 22), (Sat.Literal.neg 44), (Sat.Literal.pos 692)] :=
  (lex_5_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.pos 22), (Sat.Literal.pos 44), (Sat.Literal.pos 692)] :=
  (lex_5_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 692) = lexBefore s permutation5 21 := by
  exact (positive_lex_of_descriptor s 692 permutation5 22 (by rfl)).trans ((lex_skipped s permutation5 21 22 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation5 21) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation5 21 by rw [image5_eq]; rfl))

theorem lex_5_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 693) (Sat.Literal.pos 692) (Sat.Literal.pos 21) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation5 21 (assignment s)
    (Sat.Literal.pos 693) (Sat.Literal.pos 692) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (positive_of_descriptor s 693 (.lex permutation5 21) (by rfl)) (lex_5_21_prefix s) (positive_select s 21) (lex_5_21_image s)

theorem lex_5_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation5 21 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 692) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (lex_5_21_prefix s) (positive_select s 21) (lex_5_21_image s)

theorem lex_5_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.pos 692)] :=
  (lex_5_21_gate s).prop _ (List.Mem.head _)

theorem lex_5_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.neg 21), (Sat.Literal.pos 42)] :=
  (lex_5_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] :=
  (lex_5_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.neg 21), (Sat.Literal.neg 42), (Sat.Literal.pos 693)] :=
  (lex_5_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 692), (Sat.Literal.pos 21), (Sat.Literal.pos 42), (Sat.Literal.pos 693)] :=
  (lex_5_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 693) = lexBefore s permutation5 20 := by
  exact (positive_lex_of_descriptor s 693 permutation5 21 (by rfl)).trans ((lex_skipped s permutation5 20 21 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation5 20) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation5 20 by rw [image5_eq]; rfl))

theorem lex_5_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 694) (Sat.Literal.pos 693) (Sat.Literal.pos 20) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation5 20 (assignment s)
    (Sat.Literal.pos 694) (Sat.Literal.pos 693) (Sat.Literal.pos 20) (Sat.Literal.pos 40) (positive_of_descriptor s 694 (.lex permutation5 20) (by rfl)) (lex_5_20_prefix s) (positive_select s 20) (lex_5_20_image s)

theorem lex_5_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.pos 20), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation5 20 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 693) (Sat.Literal.pos 20) (Sat.Literal.pos 40) (lex_5_20_prefix s) (positive_select s 20) (lex_5_20_image s)

theorem lex_5_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.pos 693)] :=
  (lex_5_20_gate s).prop _ (List.Mem.head _)

theorem lex_5_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.neg 20), (Sat.Literal.pos 40)] :=
  (lex_5_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.pos 20), (Sat.Literal.neg 40)] :=
  (lex_5_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.neg 20), (Sat.Literal.neg 40), (Sat.Literal.pos 694)] :=
  (lex_5_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 693), (Sat.Literal.pos 20), (Sat.Literal.pos 40), (Sat.Literal.pos 694)] :=
  (lex_5_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 694) = lexBefore s permutation5 19 := by
  exact (positive_lex_of_descriptor s 694 permutation5 20 (by rfl)).trans ((lex_skipped s permutation5 19 20 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation5 19) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation5 19 by rw [image5_eq]; rfl))

theorem lex_5_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 695) (Sat.Literal.pos 694) (Sat.Literal.pos 19) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation5 19 (assignment s)
    (Sat.Literal.pos 695) (Sat.Literal.pos 694) (Sat.Literal.pos 19) (Sat.Literal.pos 38) (positive_of_descriptor s 695 (.lex permutation5 19) (by rfl)) (lex_5_19_prefix s) (positive_select s 19) (lex_5_19_image s)

theorem lex_5_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.pos 19), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation5 19 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 694) (Sat.Literal.pos 19) (Sat.Literal.pos 38) (lex_5_19_prefix s) (positive_select s 19) (lex_5_19_image s)

theorem lex_5_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.pos 694)] :=
  (lex_5_19_gate s).prop _ (List.Mem.head _)

theorem lex_5_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.neg 19), (Sat.Literal.pos 38)] :=
  (lex_5_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.pos 19), (Sat.Literal.neg 38)] :=
  (lex_5_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.neg 19), (Sat.Literal.neg 38), (Sat.Literal.pos 695)] :=
  (lex_5_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 694), (Sat.Literal.pos 19), (Sat.Literal.pos 38), (Sat.Literal.pos 695)] :=
  (lex_5_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 695) = lexBefore s permutation5 18 := by
  exact (positive_lex_of_descriptor s 695 permutation5 19 (by rfl)).trans ((lex_skipped s permutation5 18 19 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation5 18) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation5 18 by rw [image5_eq]; rfl))

theorem lex_5_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 696) (Sat.Literal.pos 695) (Sat.Literal.pos 18) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation5 18 (assignment s)
    (Sat.Literal.pos 696) (Sat.Literal.pos 695) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (positive_of_descriptor s 696 (.lex permutation5 18) (by rfl)) (lex_5_18_prefix s) (positive_select s 18) (lex_5_18_image s)

theorem lex_5_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation5 18 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 695) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (lex_5_18_prefix s) (positive_select s 18) (lex_5_18_image s)

theorem lex_5_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.pos 695)] :=
  (lex_5_18_gate s).prop _ (List.Mem.head _)

theorem lex_5_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.neg 18), (Sat.Literal.pos 36)] :=
  (lex_5_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] :=
  (lex_5_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.neg 18), (Sat.Literal.neg 36), (Sat.Literal.pos 696)] :=
  (lex_5_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 695), (Sat.Literal.pos 18), (Sat.Literal.pos 36), (Sat.Literal.pos 696)] :=
  (lex_5_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 696) = lexBefore s permutation5 17 := by
  exact (positive_lex_of_descriptor s 696 permutation5 18 (by rfl)).trans ((lex_skipped s permutation5 17 18 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation5 17) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation5 17 by rw [image5_eq]; rfl))

theorem lex_5_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 697) (Sat.Literal.pos 696) (Sat.Literal.pos 17) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation5 17 (assignment s)
    (Sat.Literal.pos 697) (Sat.Literal.pos 696) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (positive_of_descriptor s 697 (.lex permutation5 17) (by rfl)) (lex_5_17_prefix s) (positive_select s 17) (lex_5_17_image s)

theorem lex_5_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation5 17 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 696) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (lex_5_17_prefix s) (positive_select s 17) (lex_5_17_image s)

theorem lex_5_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.pos 696)] :=
  (lex_5_17_gate s).prop _ (List.Mem.head _)

theorem lex_5_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.neg 17), (Sat.Literal.pos 34)] :=
  (lex_5_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] :=
  (lex_5_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.neg 17), (Sat.Literal.neg 34), (Sat.Literal.pos 697)] :=
  (lex_5_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 696), (Sat.Literal.pos 17), (Sat.Literal.pos 34), (Sat.Literal.pos 697)] :=
  (lex_5_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 697) = lexBefore s permutation5 16 := by
  exact (positive_lex_of_descriptor s 697 permutation5 17 (by rfl)).trans ((lex_skipped s permutation5 16 17 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation5 16) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 64) = permuteMask permutation5 16 by rw [image5_eq]; rfl))

theorem lex_5_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 698) (Sat.Literal.pos 697) (Sat.Literal.pos 16) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation5 16 (assignment s)
    (Sat.Literal.pos 698) (Sat.Literal.pos 697) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (positive_of_descriptor s 698 (.lex permutation5 16) (by rfl)) (lex_5_16_prefix s) (positive_select s 16) (lex_5_16_image s)

theorem lex_5_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation5 16 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 697) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (lex_5_16_prefix s) (positive_select s 16) (lex_5_16_image s)

theorem lex_5_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.pos 697)] :=
  (lex_5_16_gate s).prop _ (List.Mem.head _)

theorem lex_5_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.neg 16), (Sat.Literal.pos 32)] :=
  (lex_5_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] :=
  (lex_5_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.neg 16), (Sat.Literal.neg 32), (Sat.Literal.pos 698)] :=
  (lex_5_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 697), (Sat.Literal.pos 16), (Sat.Literal.pos 32), (Sat.Literal.pos 698)] :=
  (lex_5_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_15_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 698) = lexBefore s permutation5 15 := by
  exact (positive_lex_of_descriptor s 698 permutation5 16 (by rfl)).trans ((lex_skipped s permutation5 15 16 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_15_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation5 15) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation5 15 by rw [image5_eq]; rfl))

theorem lex_5_15_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 699) (Sat.Literal.pos 698) (Sat.Literal.pos 15) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation5 15 (assignment s)
    (Sat.Literal.pos 699) (Sat.Literal.pos 698) (Sat.Literal.pos 15) (Sat.Literal.pos 30) (positive_of_descriptor s 699 (.lex permutation5 15) (by rfl)) (lex_5_15_prefix s) (positive_select s 15) (lex_5_15_image s)

theorem lex_5_15_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.pos 15), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation5 15 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 698) (Sat.Literal.pos 15) (Sat.Literal.pos 30) (lex_5_15_prefix s) (positive_select s 15) (lex_5_15_image s)

theorem lex_5_15_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.pos 698)] :=
  (lex_5_15_gate s).prop _ (List.Mem.head _)

theorem lex_5_15_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.neg 15), (Sat.Literal.pos 30)] :=
  (lex_5_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_15_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.pos 15), (Sat.Literal.neg 30)] :=
  (lex_5_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_15_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.neg 15), (Sat.Literal.neg 30), (Sat.Literal.pos 699)] :=
  (lex_5_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_15_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 698), (Sat.Literal.pos 15), (Sat.Literal.pos 30), (Sat.Literal.pos 699)] :=
  (lex_5_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 699) = lexBefore s permutation5 14 := by
  exact (positive_lex_of_descriptor s 699 permutation5 15 (by rfl)).trans ((lex_skipped s permutation5 14 15 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation5 14) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation5 14 by rw [image5_eq]; rfl))

theorem lex_5_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 700) (Sat.Literal.pos 699) (Sat.Literal.pos 14) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation5 14 (assignment s)
    (Sat.Literal.pos 700) (Sat.Literal.pos 699) (Sat.Literal.pos 14) (Sat.Literal.pos 28) (positive_of_descriptor s 700 (.lex permutation5 14) (by rfl)) (lex_5_14_prefix s) (positive_select s 14) (lex_5_14_image s)

theorem lex_5_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.pos 14), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation5 14 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 699) (Sat.Literal.pos 14) (Sat.Literal.pos 28) (lex_5_14_prefix s) (positive_select s 14) (lex_5_14_image s)

theorem lex_5_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.pos 699)] :=
  (lex_5_14_gate s).prop _ (List.Mem.head _)

theorem lex_5_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.neg 14), (Sat.Literal.pos 28)] :=
  (lex_5_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.pos 14), (Sat.Literal.neg 28)] :=
  (lex_5_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.neg 14), (Sat.Literal.neg 28), (Sat.Literal.pos 700)] :=
  (lex_5_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 699), (Sat.Literal.pos 14), (Sat.Literal.pos 28), (Sat.Literal.pos 700)] :=
  (lex_5_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 700) = lexBefore s permutation5 13 := by
  exact (positive_lex_of_descriptor s 700 permutation5 14 (by rfl)).trans ((lex_skipped s permutation5 13 14 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation5 13) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation5 13 by rw [image5_eq]; rfl))

theorem lex_5_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 701) (Sat.Literal.pos 700) (Sat.Literal.pos 13) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation5 13 (assignment s)
    (Sat.Literal.pos 701) (Sat.Literal.pos 700) (Sat.Literal.pos 13) (Sat.Literal.pos 26) (positive_of_descriptor s 701 (.lex permutation5 13) (by rfl)) (lex_5_13_prefix s) (positive_select s 13) (lex_5_13_image s)

theorem lex_5_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.pos 13), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation5 13 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 700) (Sat.Literal.pos 13) (Sat.Literal.pos 26) (lex_5_13_prefix s) (positive_select s 13) (lex_5_13_image s)

theorem lex_5_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.pos 700)] :=
  (lex_5_13_gate s).prop _ (List.Mem.head _)

theorem lex_5_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.neg 13), (Sat.Literal.pos 26)] :=
  (lex_5_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.pos 13), (Sat.Literal.neg 26)] :=
  (lex_5_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.neg 13), (Sat.Literal.neg 26), (Sat.Literal.pos 701)] :=
  (lex_5_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 700), (Sat.Literal.pos 13), (Sat.Literal.pos 26), (Sat.Literal.pos 701)] :=
  (lex_5_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 701) = lexBefore s permutation5 12 := by
  exact (positive_lex_of_descriptor s 701 permutation5 13 (by rfl)).trans ((lex_skipped s permutation5 12 13 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation5 12) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation5 12 by rw [image5_eq]; rfl))

theorem lex_5_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 702) (Sat.Literal.pos 701) (Sat.Literal.pos 12) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation5 12 (assignment s)
    (Sat.Literal.pos 702) (Sat.Literal.pos 701) (Sat.Literal.pos 12) (Sat.Literal.pos 24) (positive_of_descriptor s 702 (.lex permutation5 12) (by rfl)) (lex_5_12_prefix s) (positive_select s 12) (lex_5_12_image s)

theorem lex_5_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.pos 12), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation5 12 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 701) (Sat.Literal.pos 12) (Sat.Literal.pos 24) (lex_5_12_prefix s) (positive_select s 12) (lex_5_12_image s)

theorem lex_5_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.pos 701)] :=
  (lex_5_12_gate s).prop _ (List.Mem.head _)

theorem lex_5_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.neg 12), (Sat.Literal.pos 24)] :=
  (lex_5_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.pos 12), (Sat.Literal.neg 24)] :=
  (lex_5_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.neg 12), (Sat.Literal.neg 24), (Sat.Literal.pos 702)] :=
  (lex_5_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 701), (Sat.Literal.pos 12), (Sat.Literal.pos 24), (Sat.Literal.pos 702)] :=
  (lex_5_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 702) = lexBefore s permutation5 11 := by
  exact (positive_lex_of_descriptor s 702 permutation5 12 (by rfl)).trans ((lex_skipped s permutation5 11 12 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation5 11) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation5 11 by rw [image5_eq]; rfl))

theorem lex_5_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 703) (Sat.Literal.pos 702) (Sat.Literal.pos 11) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation5 11 (assignment s)
    (Sat.Literal.pos 703) (Sat.Literal.pos 702) (Sat.Literal.pos 11) (Sat.Literal.pos 22) (positive_of_descriptor s 703 (.lex permutation5 11) (by rfl)) (lex_5_11_prefix s) (positive_select s 11) (lex_5_11_image s)

theorem lex_5_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.pos 11), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation5 11 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 702) (Sat.Literal.pos 11) (Sat.Literal.pos 22) (lex_5_11_prefix s) (positive_select s 11) (lex_5_11_image s)

theorem lex_5_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.pos 702)] :=
  (lex_5_11_gate s).prop _ (List.Mem.head _)

theorem lex_5_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.neg 11), (Sat.Literal.pos 22)] :=
  (lex_5_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.pos 11), (Sat.Literal.neg 22)] :=
  (lex_5_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.neg 11), (Sat.Literal.neg 22), (Sat.Literal.pos 703)] :=
  (lex_5_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 702), (Sat.Literal.pos 11), (Sat.Literal.pos 22), (Sat.Literal.pos 703)] :=
  (lex_5_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 703) = lexBefore s permutation5 10 := by
  exact (positive_lex_of_descriptor s 703 permutation5 11 (by rfl)).trans ((lex_skipped s permutation5 10 11 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation5 10) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation5 10 by rw [image5_eq]; rfl))

theorem lex_5_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 704) (Sat.Literal.pos 703) (Sat.Literal.pos 10) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation5 10 (assignment s)
    (Sat.Literal.pos 704) (Sat.Literal.pos 703) (Sat.Literal.pos 10) (Sat.Literal.pos 20) (positive_of_descriptor s 704 (.lex permutation5 10) (by rfl)) (lex_5_10_prefix s) (positive_select s 10) (lex_5_10_image s)

theorem lex_5_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.pos 10), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation5 10 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 703) (Sat.Literal.pos 10) (Sat.Literal.pos 20) (lex_5_10_prefix s) (positive_select s 10) (lex_5_10_image s)

theorem lex_5_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.pos 703)] :=
  (lex_5_10_gate s).prop _ (List.Mem.head _)

theorem lex_5_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.neg 10), (Sat.Literal.pos 20)] :=
  (lex_5_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.pos 10), (Sat.Literal.neg 20)] :=
  (lex_5_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.neg 10), (Sat.Literal.neg 20), (Sat.Literal.pos 704)] :=
  (lex_5_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 703), (Sat.Literal.pos 10), (Sat.Literal.pos 20), (Sat.Literal.pos 704)] :=
  (lex_5_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 704) = lexBefore s permutation5 9 := by
  exact (positive_lex_of_descriptor s 704 permutation5 10 (by rfl)).trans ((lex_skipped s permutation5 9 10 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation5 9) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation5 9 by rw [image5_eq]; rfl))

theorem lex_5_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 705) (Sat.Literal.pos 704) (Sat.Literal.pos 9) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation5 9 (assignment s)
    (Sat.Literal.pos 705) (Sat.Literal.pos 704) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (positive_of_descriptor s 705 (.lex permutation5 9) (by rfl)) (lex_5_9_prefix s) (positive_select s 9) (lex_5_9_image s)

theorem lex_5_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation5 9 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 704) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (lex_5_9_prefix s) (positive_select s 9) (lex_5_9_image s)

theorem lex_5_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.pos 704)] :=
  (lex_5_9_gate s).prop _ (List.Mem.head _)

theorem lex_5_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.neg 9), (Sat.Literal.pos 18)] :=
  (lex_5_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] :=
  (lex_5_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.neg 9), (Sat.Literal.neg 18), (Sat.Literal.pos 705)] :=
  (lex_5_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 704), (Sat.Literal.pos 9), (Sat.Literal.pos 18), (Sat.Literal.pos 705)] :=
  (lex_5_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 705) = lexBefore s permutation5 8 := by
  exact (positive_lex_of_descriptor s 705 permutation5 9 (by rfl)).trans ((lex_skipped s permutation5 8 9 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation5 8) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation5 8 by rw [image5_eq]; rfl))

theorem lex_5_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 706) (Sat.Literal.pos 705) (Sat.Literal.pos 8) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation5 8 (assignment s)
    (Sat.Literal.pos 706) (Sat.Literal.pos 705) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (positive_of_descriptor s 706 (.lex permutation5 8) (by rfl)) (lex_5_8_prefix s) (positive_select s 8) (lex_5_8_image s)

theorem lex_5_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation5 8 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 705) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (lex_5_8_prefix s) (positive_select s 8) (lex_5_8_image s)

theorem lex_5_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.pos 705)] :=
  (lex_5_8_gate s).prop _ (List.Mem.head _)

theorem lex_5_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.neg 8), (Sat.Literal.pos 16)] :=
  (lex_5_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] :=
  (lex_5_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.neg 8), (Sat.Literal.neg 16), (Sat.Literal.pos 706)] :=
  (lex_5_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 705), (Sat.Literal.pos 8), (Sat.Literal.pos 16), (Sat.Literal.pos 706)] :=
  (lex_5_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_7_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 706) = lexBefore s permutation5 7 := by
  exact (positive_lex_of_descriptor s 706 permutation5 8 (by rfl)).trans ((lex_skipped s permutation5 7 8 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_7_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation5 7) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation5 7 by rw [image5_eq]; rfl))

theorem lex_5_7_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 707) (Sat.Literal.pos 706) (Sat.Literal.pos 7) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation5 7 (assignment s)
    (Sat.Literal.pos 707) (Sat.Literal.pos 706) (Sat.Literal.pos 7) (Sat.Literal.pos 14) (positive_of_descriptor s 707 (.lex permutation5 7) (by rfl)) (lex_5_7_prefix s) (positive_select s 7) (lex_5_7_image s)

theorem lex_5_7_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.pos 7), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation5 7 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 706) (Sat.Literal.pos 7) (Sat.Literal.pos 14) (lex_5_7_prefix s) (positive_select s 7) (lex_5_7_image s)

theorem lex_5_7_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.pos 706)] :=
  (lex_5_7_gate s).prop _ (List.Mem.head _)

theorem lex_5_7_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.neg 7), (Sat.Literal.pos 14)] :=
  (lex_5_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_7_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.pos 7), (Sat.Literal.neg 14)] :=
  (lex_5_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_7_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.neg 7), (Sat.Literal.neg 14), (Sat.Literal.pos 707)] :=
  (lex_5_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_7_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 706), (Sat.Literal.pos 7), (Sat.Literal.pos 14), (Sat.Literal.pos 707)] :=
  (lex_5_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 707) = lexBefore s permutation5 6 := by
  exact (positive_lex_of_descriptor s 707 permutation5 7 (by rfl)).trans ((lex_skipped s permutation5 6 7 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation5 6) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation5 6 by rw [image5_eq]; rfl))

theorem lex_5_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 708) (Sat.Literal.pos 707) (Sat.Literal.pos 6) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation5 6 (assignment s)
    (Sat.Literal.pos 708) (Sat.Literal.pos 707) (Sat.Literal.pos 6) (Sat.Literal.pos 12) (positive_of_descriptor s 708 (.lex permutation5 6) (by rfl)) (lex_5_6_prefix s) (positive_select s 6) (lex_5_6_image s)

theorem lex_5_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.pos 6), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation5 6 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 707) (Sat.Literal.pos 6) (Sat.Literal.pos 12) (lex_5_6_prefix s) (positive_select s 6) (lex_5_6_image s)

theorem lex_5_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.pos 707)] :=
  (lex_5_6_gate s).prop _ (List.Mem.head _)

theorem lex_5_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.neg 6), (Sat.Literal.pos 12)] :=
  (lex_5_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.pos 6), (Sat.Literal.neg 12)] :=
  (lex_5_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.neg 6), (Sat.Literal.neg 12), (Sat.Literal.pos 708)] :=
  (lex_5_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 707), (Sat.Literal.pos 6), (Sat.Literal.pos 12), (Sat.Literal.pos 708)] :=
  (lex_5_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 708) = lexBefore s permutation5 5 := by
  exact (positive_lex_of_descriptor s 708 permutation5 6 (by rfl)).trans ((lex_skipped s permutation5 5 6 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation5 5) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation5 5 by rw [image5_eq]; rfl))

theorem lex_5_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 709) (Sat.Literal.pos 708) (Sat.Literal.pos 5) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation5 5 (assignment s)
    (Sat.Literal.pos 709) (Sat.Literal.pos 708) (Sat.Literal.pos 5) (Sat.Literal.pos 10) (positive_of_descriptor s 709 (.lex permutation5 5) (by rfl)) (lex_5_5_prefix s) (positive_select s 5) (lex_5_5_image s)

theorem lex_5_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.pos 5), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation5 5 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 708) (Sat.Literal.pos 5) (Sat.Literal.pos 10) (lex_5_5_prefix s) (positive_select s 5) (lex_5_5_image s)

theorem lex_5_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.pos 708)] :=
  (lex_5_5_gate s).prop _ (List.Mem.head _)

theorem lex_5_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.neg 5), (Sat.Literal.pos 10)] :=
  (lex_5_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.pos 5), (Sat.Literal.neg 10)] :=
  (lex_5_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.neg 5), (Sat.Literal.neg 10), (Sat.Literal.pos 709)] :=
  (lex_5_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 708), (Sat.Literal.pos 5), (Sat.Literal.pos 10), (Sat.Literal.pos 709)] :=
  (lex_5_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 709) = lexBefore s permutation5 4 := by
  exact (positive_lex_of_descriptor s 709 permutation5 5 (by rfl)).trans ((lex_skipped s permutation5 4 5 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation5 4) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation5 4 by rw [image5_eq]; rfl))

theorem lex_5_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 710) (Sat.Literal.pos 709) (Sat.Literal.pos 4) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation5 4 (assignment s)
    (Sat.Literal.pos 710) (Sat.Literal.pos 709) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (positive_of_descriptor s 710 (.lex permutation5 4) (by rfl)) (lex_5_4_prefix s) (positive_select s 4) (lex_5_4_image s)

theorem lex_5_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation5 4 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 709) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (lex_5_4_prefix s) (positive_select s 4) (lex_5_4_image s)

theorem lex_5_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.pos 709)] :=
  (lex_5_4_gate s).prop _ (List.Mem.head _)

theorem lex_5_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.neg 4), (Sat.Literal.pos 8)] :=
  (lex_5_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] :=
  (lex_5_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.neg 4), (Sat.Literal.neg 8), (Sat.Literal.pos 710)] :=
  (lex_5_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 709), (Sat.Literal.pos 4), (Sat.Literal.pos 8), (Sat.Literal.pos 710)] :=
  (lex_5_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_3_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 710) = lexBefore s permutation5 3 := by
  exact (positive_lex_of_descriptor s 710 permutation5 4 (by rfl)).trans ((lex_skipped s permutation5 3 4 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_3_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation5 3) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation5 3 by rw [image5_eq]; rfl))

theorem lex_5_3_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 711) (Sat.Literal.pos 710) (Sat.Literal.pos 3) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation5 3 (assignment s)
    (Sat.Literal.pos 711) (Sat.Literal.pos 710) (Sat.Literal.pos 3) (Sat.Literal.pos 6) (positive_of_descriptor s 711 (.lex permutation5 3) (by rfl)) (lex_5_3_prefix s) (positive_select s 3) (lex_5_3_image s)

theorem lex_5_3_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.pos 3), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation5 3 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 710) (Sat.Literal.pos 3) (Sat.Literal.pos 6) (lex_5_3_prefix s) (positive_select s 3) (lex_5_3_image s)

theorem lex_5_3_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.pos 710)] :=
  (lex_5_3_gate s).prop _ (List.Mem.head _)

theorem lex_5_3_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.neg 3), (Sat.Literal.pos 6)] :=
  (lex_5_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_3_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.pos 3), (Sat.Literal.neg 6)] :=
  (lex_5_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_3_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.neg 3), (Sat.Literal.neg 6), (Sat.Literal.pos 711)] :=
  (lex_5_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_3_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 710), (Sat.Literal.pos 3), (Sat.Literal.pos 6), (Sat.Literal.pos 711)] :=
  (lex_5_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 711) = lexBefore s permutation5 2 := by
  exact (positive_lex_of_descriptor s 711 permutation5 3 (by rfl)).trans ((lex_skipped s permutation5 2 3 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation5 2) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation5 2 by rw [image5_eq]; rfl))

theorem lex_5_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 712) (Sat.Literal.pos 711) (Sat.Literal.pos 2) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation5 2 (assignment s)
    (Sat.Literal.pos 712) (Sat.Literal.pos 711) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (positive_of_descriptor s 712 (.lex permutation5 2) (by rfl)) (lex_5_2_prefix s) (positive_select s 2) (lex_5_2_image s)

theorem lex_5_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation5 2 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 711) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (lex_5_2_prefix s) (positive_select s 2) (lex_5_2_image s)

theorem lex_5_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.pos 711)] :=
  (lex_5_2_gate s).prop _ (List.Mem.head _)

theorem lex_5_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.neg 2), (Sat.Literal.pos 4)] :=
  (lex_5_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] :=
  (lex_5_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.neg 2), (Sat.Literal.neg 4), (Sat.Literal.pos 712)] :=
  (lex_5_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 711), (Sat.Literal.pos 2), (Sat.Literal.pos 4), (Sat.Literal.pos 712)] :=
  (lex_5_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_1_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 712) = lexBefore s permutation5 1 := by
  exact (positive_lex_of_descriptor s 712 permutation5 2 (by rfl)).trans ((lex_skipped s permutation5 1 2 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_1_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation5 1) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation5 1 by rw [image5_eq]; rfl))

theorem lex_5_1_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 713) (Sat.Literal.pos 712) (Sat.Literal.pos 1) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation5 1 (assignment s)
    (Sat.Literal.pos 713) (Sat.Literal.pos 712) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (positive_of_descriptor s 713 (.lex permutation5 1) (by rfl)) (lex_5_1_prefix s) (positive_select s 1) (lex_5_1_image s)

theorem lex_5_1_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation5 1 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 712) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (lex_5_1_prefix s) (positive_select s 1) (lex_5_1_image s)

theorem lex_5_1_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 713), (Sat.Literal.pos 712)] :=
  (lex_5_1_gate s).prop _ (List.Mem.head _)

theorem lex_5_1_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 713), (Sat.Literal.neg 1), (Sat.Literal.pos 2)] :=
  (lex_5_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_1_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 713), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] :=
  (lex_5_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_1_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.neg 1), (Sat.Literal.neg 2), (Sat.Literal.pos 713)] :=
  (lex_5_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_1_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 712), (Sat.Literal.pos 1), (Sat.Literal.pos 2), (Sat.Literal.pos 713)] :=
  (lex_5_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation6 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation6 62 (by intro j hj; rw [image6_eq]; exact fixedOnRange_spec image6 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_6_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation6 62) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation6 62 by rw [image6_eq]; rfl))

theorem lex_6_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 714) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation6 62 (assignment s)
    (Sat.Literal.pos 714) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 59) (positive_of_descriptor s 714 (.lex permutation6 62) (by rfl)) (lex_6_62_prefix s) (positive_select s 62) (lex_6_62_image s)

theorem lex_6_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation6 62 (hmax permutation6) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 59) (lex_6_62_prefix s) (positive_select s 62) (lex_6_62_image s)

theorem lex_6_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.neg 64)] :=
  (lex_6_62_gate s).prop _ (List.Mem.head _)

theorem lex_6_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.neg 62), (Sat.Literal.pos 59)] :=
  (lex_6_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.pos 62), (Sat.Literal.neg 59)] :=
  (lex_6_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 59), (Sat.Literal.pos 714)] :=
  (lex_6_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 59), (Sat.Literal.pos 714)] :=
  (lex_6_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 714) = lexBefore s permutation6 61 := by
  exact (positive_lex_of_descriptor s 714 permutation6 62 (by rfl)).trans ((lex_skipped s permutation6 61 62 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation6 61) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation6 61 by rw [image6_eq]; rfl))

theorem lex_6_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 715) (Sat.Literal.pos 714) (Sat.Literal.pos 61) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation6 61 (assignment s)
    (Sat.Literal.pos 715) (Sat.Literal.pos 714) (Sat.Literal.pos 61) (Sat.Literal.pos 55) (positive_of_descriptor s 715 (.lex permutation6 61) (by rfl)) (lex_6_61_prefix s) (positive_select s 61) (lex_6_61_image s)

theorem lex_6_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.pos 61), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation6 61 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 714) (Sat.Literal.pos 61) (Sat.Literal.pos 55) (lex_6_61_prefix s) (positive_select s 61) (lex_6_61_image s)

theorem lex_6_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.pos 714)] :=
  (lex_6_61_gate s).prop _ (List.Mem.head _)

theorem lex_6_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.neg 61), (Sat.Literal.pos 55)] :=
  (lex_6_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.pos 61), (Sat.Literal.neg 55)] :=
  (lex_6_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.neg 61), (Sat.Literal.neg 55), (Sat.Literal.pos 715)] :=
  (lex_6_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 714), (Sat.Literal.pos 61), (Sat.Literal.pos 55), (Sat.Literal.pos 715)] :=
  (lex_6_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_60_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 715) = lexBefore s permutation6 60 := by
  exact (positive_lex_of_descriptor s 715 permutation6 61 (by rfl)).trans ((lex_skipped s permutation6 60 61 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_60_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation6 60) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation6 60 by rw [image6_eq]; rfl))

theorem lex_6_60_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 716) (Sat.Literal.pos 715) (Sat.Literal.pos 60) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation6 60 (assignment s)
    (Sat.Literal.pos 716) (Sat.Literal.pos 715) (Sat.Literal.pos 60) (Sat.Literal.pos 51) (positive_of_descriptor s 716 (.lex permutation6 60) (by rfl)) (lex_6_60_prefix s) (positive_select s 60) (lex_6_60_image s)

theorem lex_6_60_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.pos 60), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation6 60 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 715) (Sat.Literal.pos 60) (Sat.Literal.pos 51) (lex_6_60_prefix s) (positive_select s 60) (lex_6_60_image s)

theorem lex_6_60_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.pos 715)] :=
  (lex_6_60_gate s).prop _ (List.Mem.head _)

theorem lex_6_60_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.neg 60), (Sat.Literal.pos 51)] :=
  (lex_6_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_60_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.pos 60), (Sat.Literal.neg 51)] :=
  (lex_6_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_60_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.neg 60), (Sat.Literal.neg 51), (Sat.Literal.pos 716)] :=
  (lex_6_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_60_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 715), (Sat.Literal.pos 60), (Sat.Literal.pos 51), (Sat.Literal.pos 716)] :=
  (lex_6_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 716) = lexBefore s permutation6 59 := by
  exact (positive_lex_of_descriptor s 716 permutation6 60 (by rfl)).trans ((lex_skipped s permutation6 59 60 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation6 59) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation6 59 by rw [image6_eq]; rfl))

theorem lex_6_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 717) (Sat.Literal.pos 716) (Sat.Literal.pos 59) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation6 59 (assignment s)
    (Sat.Literal.pos 717) (Sat.Literal.pos 716) (Sat.Literal.pos 59) (Sat.Literal.pos 47) (positive_of_descriptor s 717 (.lex permutation6 59) (by rfl)) (lex_6_59_prefix s) (positive_select s 59) (lex_6_59_image s)

theorem lex_6_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.pos 59), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation6 59 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 716) (Sat.Literal.pos 59) (Sat.Literal.pos 47) (lex_6_59_prefix s) (positive_select s 59) (lex_6_59_image s)

theorem lex_6_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.pos 716)] :=
  (lex_6_59_gate s).prop _ (List.Mem.head _)

theorem lex_6_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.neg 59), (Sat.Literal.pos 47)] :=
  (lex_6_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.pos 59), (Sat.Literal.neg 47)] :=
  (lex_6_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.neg 59), (Sat.Literal.neg 47), (Sat.Literal.pos 717)] :=
  (lex_6_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 716), (Sat.Literal.pos 59), (Sat.Literal.pos 47), (Sat.Literal.pos 717)] :=
  (lex_6_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 717) = lexBefore s permutation6 58 := by
  exact (positive_lex_of_descriptor s 717 permutation6 59 (by rfl)).trans ((lex_skipped s permutation6 58 59 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation6 58) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation6 58 by rw [image6_eq]; rfl))

theorem lex_6_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 718) (Sat.Literal.pos 717) (Sat.Literal.pos 58) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation6 58 (assignment s)
    (Sat.Literal.pos 718) (Sat.Literal.pos 717) (Sat.Literal.pos 58) (Sat.Literal.pos 43) (positive_of_descriptor s 718 (.lex permutation6 58) (by rfl)) (lex_6_58_prefix s) (positive_select s 58) (lex_6_58_image s)

theorem lex_6_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.pos 58), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation6 58 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 717) (Sat.Literal.pos 58) (Sat.Literal.pos 43) (lex_6_58_prefix s) (positive_select s 58) (lex_6_58_image s)

theorem lex_6_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.pos 717)] :=
  (lex_6_58_gate s).prop _ (List.Mem.head _)

theorem lex_6_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.neg 58), (Sat.Literal.pos 43)] :=
  (lex_6_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.pos 58), (Sat.Literal.neg 43)] :=
  (lex_6_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.neg 58), (Sat.Literal.neg 43), (Sat.Literal.pos 718)] :=
  (lex_6_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 717), (Sat.Literal.pos 58), (Sat.Literal.pos 43), (Sat.Literal.pos 718)] :=
  (lex_6_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 718) = lexBefore s permutation6 57 := by
  exact (positive_lex_of_descriptor s 718 permutation6 58 (by rfl)).trans ((lex_skipped s permutation6 57 58 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation6 57) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation6 57 by rw [image6_eq]; rfl))

theorem lex_6_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 719) (Sat.Literal.pos 718) (Sat.Literal.pos 57) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation6 57 (assignment s)
    (Sat.Literal.pos 719) (Sat.Literal.pos 718) (Sat.Literal.pos 57) (Sat.Literal.pos 39) (positive_of_descriptor s 719 (.lex permutation6 57) (by rfl)) (lex_6_57_prefix s) (positive_select s 57) (lex_6_57_image s)

theorem lex_6_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.pos 57), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation6 57 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 718) (Sat.Literal.pos 57) (Sat.Literal.pos 39) (lex_6_57_prefix s) (positive_select s 57) (lex_6_57_image s)

theorem lex_6_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.pos 718)] :=
  (lex_6_57_gate s).prop _ (List.Mem.head _)

theorem lex_6_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.neg 57), (Sat.Literal.pos 39)] :=
  (lex_6_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.pos 57), (Sat.Literal.neg 39)] :=
  (lex_6_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.neg 57), (Sat.Literal.neg 39), (Sat.Literal.pos 719)] :=
  (lex_6_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 718), (Sat.Literal.pos 57), (Sat.Literal.pos 39), (Sat.Literal.pos 719)] :=
  (lex_6_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_56_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 719) = lexBefore s permutation6 56 := by
  exact (positive_lex_of_descriptor s 719 permutation6 57 (by rfl)).trans ((lex_skipped s permutation6 56 57 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_56_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation6 56) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation6 56 by rw [image6_eq]; rfl))

theorem lex_6_56_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 720) (Sat.Literal.pos 719) (Sat.Literal.pos 56) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation6 56 (assignment s)
    (Sat.Literal.pos 720) (Sat.Literal.pos 719) (Sat.Literal.pos 56) (Sat.Literal.pos 35) (positive_of_descriptor s 720 (.lex permutation6 56) (by rfl)) (lex_6_56_prefix s) (positive_select s 56) (lex_6_56_image s)

theorem lex_6_56_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.pos 56), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation6 56 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 719) (Sat.Literal.pos 56) (Sat.Literal.pos 35) (lex_6_56_prefix s) (positive_select s 56) (lex_6_56_image s)

theorem lex_6_56_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.pos 719)] :=
  (lex_6_56_gate s).prop _ (List.Mem.head _)

theorem lex_6_56_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.neg 56), (Sat.Literal.pos 35)] :=
  (lex_6_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_56_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.pos 56), (Sat.Literal.neg 35)] :=
  (lex_6_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_56_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.neg 56), (Sat.Literal.neg 35), (Sat.Literal.pos 720)] :=
  (lex_6_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_56_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 719), (Sat.Literal.pos 56), (Sat.Literal.pos 35), (Sat.Literal.pos 720)] :=
  (lex_6_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 720) = lexBefore s permutation6 55 := by
  exact (positive_lex_of_descriptor s 720 permutation6 56 (by rfl)).trans ((lex_skipped s permutation6 55 56 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation6 55) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation6 55 by rw [image6_eq]; rfl))

theorem lex_6_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 721) (Sat.Literal.pos 720) (Sat.Literal.pos 55) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation6 55 (assignment s)
    (Sat.Literal.pos 721) (Sat.Literal.pos 720) (Sat.Literal.pos 55) (Sat.Literal.pos 31) (positive_of_descriptor s 721 (.lex permutation6 55) (by rfl)) (lex_6_55_prefix s) (positive_select s 55) (lex_6_55_image s)

theorem lex_6_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.pos 55), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation6 55 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 720) (Sat.Literal.pos 55) (Sat.Literal.pos 31) (lex_6_55_prefix s) (positive_select s 55) (lex_6_55_image s)

theorem lex_6_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.pos 720)] :=
  (lex_6_55_gate s).prop _ (List.Mem.head _)

theorem lex_6_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.neg 55), (Sat.Literal.pos 31)] :=
  (lex_6_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.pos 55), (Sat.Literal.neg 31)] :=
  (lex_6_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.neg 55), (Sat.Literal.neg 31), (Sat.Literal.pos 721)] :=
  (lex_6_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 720), (Sat.Literal.pos 55), (Sat.Literal.pos 31), (Sat.Literal.pos 721)] :=
  (lex_6_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 721) = lexBefore s permutation6 54 := by
  exact (positive_lex_of_descriptor s 721 permutation6 55 (by rfl)).trans ((lex_skipped s permutation6 54 55 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation6 54) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation6 54 by rw [image6_eq]; rfl))

theorem lex_6_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 722) (Sat.Literal.pos 721) (Sat.Literal.pos 54) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation6 54 (assignment s)
    (Sat.Literal.pos 722) (Sat.Literal.pos 721) (Sat.Literal.pos 54) (Sat.Literal.pos 27) (positive_of_descriptor s 722 (.lex permutation6 54) (by rfl)) (lex_6_54_prefix s) (positive_select s 54) (lex_6_54_image s)

theorem lex_6_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.pos 54), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation6 54 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 721) (Sat.Literal.pos 54) (Sat.Literal.pos 27) (lex_6_54_prefix s) (positive_select s 54) (lex_6_54_image s)

theorem lex_6_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.pos 721)] :=
  (lex_6_54_gate s).prop _ (List.Mem.head _)

theorem lex_6_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.neg 54), (Sat.Literal.pos 27)] :=
  (lex_6_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.pos 54), (Sat.Literal.neg 27)] :=
  (lex_6_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.neg 54), (Sat.Literal.neg 27), (Sat.Literal.pos 722)] :=
  (lex_6_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 721), (Sat.Literal.pos 54), (Sat.Literal.pos 27), (Sat.Literal.pos 722)] :=
  (lex_6_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 722) = lexBefore s permutation6 53 := by
  exact (positive_lex_of_descriptor s 722 permutation6 54 (by rfl)).trans ((lex_skipped s permutation6 53 54 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation6 53) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation6 53 by rw [image6_eq]; rfl))

theorem lex_6_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 723) (Sat.Literal.pos 722) (Sat.Literal.pos 53) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation6 53 (assignment s)
    (Sat.Literal.pos 723) (Sat.Literal.pos 722) (Sat.Literal.pos 53) (Sat.Literal.pos 23) (positive_of_descriptor s 723 (.lex permutation6 53) (by rfl)) (lex_6_53_prefix s) (positive_select s 53) (lex_6_53_image s)

theorem lex_6_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.pos 53), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation6 53 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 722) (Sat.Literal.pos 53) (Sat.Literal.pos 23) (lex_6_53_prefix s) (positive_select s 53) (lex_6_53_image s)

theorem lex_6_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.pos 722)] :=
  (lex_6_53_gate s).prop _ (List.Mem.head _)

theorem lex_6_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.neg 53), (Sat.Literal.pos 23)] :=
  (lex_6_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.pos 53), (Sat.Literal.neg 23)] :=
  (lex_6_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.neg 53), (Sat.Literal.neg 23), (Sat.Literal.pos 723)] :=
  (lex_6_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 722), (Sat.Literal.pos 53), (Sat.Literal.pos 23), (Sat.Literal.pos 723)] :=
  (lex_6_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 723) = lexBefore s permutation6 52 := by
  exact (positive_lex_of_descriptor s 723 permutation6 53 (by rfl)).trans ((lex_skipped s permutation6 52 53 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation6 52) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation6 52 by rw [image6_eq]; rfl))

theorem lex_6_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 724) (Sat.Literal.pos 723) (Sat.Literal.pos 52) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation6 52 (assignment s)
    (Sat.Literal.pos 724) (Sat.Literal.pos 723) (Sat.Literal.pos 52) (Sat.Literal.pos 19) (positive_of_descriptor s 724 (.lex permutation6 52) (by rfl)) (lex_6_52_prefix s) (positive_select s 52) (lex_6_52_image s)

theorem lex_6_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.pos 52), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation6 52 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 723) (Sat.Literal.pos 52) (Sat.Literal.pos 19) (lex_6_52_prefix s) (positive_select s 52) (lex_6_52_image s)

theorem lex_6_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.pos 723)] :=
  (lex_6_52_gate s).prop _ (List.Mem.head _)

theorem lex_6_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.neg 52), (Sat.Literal.pos 19)] :=
  (lex_6_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.pos 52), (Sat.Literal.neg 19)] :=
  (lex_6_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.neg 52), (Sat.Literal.neg 19), (Sat.Literal.pos 724)] :=
  (lex_6_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 723), (Sat.Literal.pos 52), (Sat.Literal.pos 19), (Sat.Literal.pos 724)] :=
  (lex_6_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 724) = lexBefore s permutation6 51 := by
  exact (positive_lex_of_descriptor s 724 permutation6 52 (by rfl)).trans ((lex_skipped s permutation6 51 52 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation6 51) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 64) = permuteMask permutation6 51 by rw [image6_eq]; rfl))

theorem lex_6_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 725) (Sat.Literal.pos 724) (Sat.Literal.pos 51) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation6 51 (assignment s)
    (Sat.Literal.pos 725) (Sat.Literal.pos 724) (Sat.Literal.pos 51) (Sat.Literal.pos 15) (positive_of_descriptor s 725 (.lex permutation6 51) (by rfl)) (lex_6_51_prefix s) (positive_select s 51) (lex_6_51_image s)

theorem lex_6_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.pos 51), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation6 51 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 724) (Sat.Literal.pos 51) (Sat.Literal.pos 15) (lex_6_51_prefix s) (positive_select s 51) (lex_6_51_image s)

theorem lex_6_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.pos 724)] :=
  (lex_6_51_gate s).prop _ (List.Mem.head _)

theorem lex_6_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.neg 51), (Sat.Literal.pos 15)] :=
  (lex_6_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.pos 51), (Sat.Literal.neg 15)] :=
  (lex_6_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.neg 51), (Sat.Literal.neg 15), (Sat.Literal.pos 725)] :=
  (lex_6_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 724), (Sat.Literal.pos 51), (Sat.Literal.pos 15), (Sat.Literal.pos 725)] :=
  (lex_6_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 725) = lexBefore s permutation6 50 := by
  exact (positive_lex_of_descriptor s 725 permutation6 51 (by rfl)).trans ((lex_skipped s permutation6 50 51 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation6 50) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation6 50 by rw [image6_eq]; rfl))

theorem lex_6_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 726) (Sat.Literal.pos 725) (Sat.Literal.pos 50) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation6 50 (assignment s)
    (Sat.Literal.pos 726) (Sat.Literal.pos 725) (Sat.Literal.pos 50) (Sat.Literal.pos 11) (positive_of_descriptor s 726 (.lex permutation6 50) (by rfl)) (lex_6_50_prefix s) (positive_select s 50) (lex_6_50_image s)

theorem lex_6_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.pos 50), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation6 50 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 725) (Sat.Literal.pos 50) (Sat.Literal.pos 11) (lex_6_50_prefix s) (positive_select s 50) (lex_6_50_image s)

theorem lex_6_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.pos 725)] :=
  (lex_6_50_gate s).prop _ (List.Mem.head _)

theorem lex_6_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.neg 50), (Sat.Literal.pos 11)] :=
  (lex_6_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.pos 50), (Sat.Literal.neg 11)] :=
  (lex_6_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.neg 50), (Sat.Literal.neg 11), (Sat.Literal.pos 726)] :=
  (lex_6_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 725), (Sat.Literal.pos 50), (Sat.Literal.pos 11), (Sat.Literal.pos 726)] :=
  (lex_6_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 726) = lexBefore s permutation6 49 := by
  exact (positive_lex_of_descriptor s 726 permutation6 50 (by rfl)).trans ((lex_skipped s permutation6 49 50 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation6 49) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 64) = permuteMask permutation6 49 by rw [image6_eq]; rfl))

theorem lex_6_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 727) (Sat.Literal.pos 726) (Sat.Literal.pos 49) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation6 49 (assignment s)
    (Sat.Literal.pos 727) (Sat.Literal.pos 726) (Sat.Literal.pos 49) (Sat.Literal.pos 7) (positive_of_descriptor s 727 (.lex permutation6 49) (by rfl)) (lex_6_49_prefix s) (positive_select s 49) (lex_6_49_image s)

theorem lex_6_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.pos 49), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation6 49 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 726) (Sat.Literal.pos 49) (Sat.Literal.pos 7) (lex_6_49_prefix s) (positive_select s 49) (lex_6_49_image s)

theorem lex_6_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.pos 726)] :=
  (lex_6_49_gate s).prop _ (List.Mem.head _)

theorem lex_6_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.neg 49), (Sat.Literal.pos 7)] :=
  (lex_6_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.pos 49), (Sat.Literal.neg 7)] :=
  (lex_6_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.neg 49), (Sat.Literal.neg 7), (Sat.Literal.pos 727)] :=
  (lex_6_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 726), (Sat.Literal.pos 49), (Sat.Literal.pos 7), (Sat.Literal.pos 727)] :=
  (lex_6_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_48_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 727) = lexBefore s permutation6 48 := by
  exact (positive_lex_of_descriptor s 727 permutation6 49 (by rfl)).trans ((lex_skipped s permutation6 48 49 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_48_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation6 48) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 64) = permuteMask permutation6 48 by rw [image6_eq]; rfl))

theorem lex_6_48_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 728) (Sat.Literal.pos 727) (Sat.Literal.pos 48) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation6 48 (assignment s)
    (Sat.Literal.pos 728) (Sat.Literal.pos 727) (Sat.Literal.pos 48) (Sat.Literal.pos 3) (positive_of_descriptor s 728 (.lex permutation6 48) (by rfl)) (lex_6_48_prefix s) (positive_select s 48) (lex_6_48_image s)

theorem lex_6_48_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.pos 48), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation6 48 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 727) (Sat.Literal.pos 48) (Sat.Literal.pos 3) (lex_6_48_prefix s) (positive_select s 48) (lex_6_48_image s)

theorem lex_6_48_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.pos 727)] :=
  (lex_6_48_gate s).prop _ (List.Mem.head _)

theorem lex_6_48_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.neg 48), (Sat.Literal.pos 3)] :=
  (lex_6_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_48_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.pos 48), (Sat.Literal.neg 3)] :=
  (lex_6_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_48_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.neg 48), (Sat.Literal.neg 3), (Sat.Literal.pos 728)] :=
  (lex_6_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_48_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 727), (Sat.Literal.pos 48), (Sat.Literal.pos 3), (Sat.Literal.pos 728)] :=
  (lex_6_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 728) = lexBefore s permutation6 47 := by
  exact (positive_lex_of_descriptor s 728 permutation6 48 (by rfl)).trans ((lex_skipped s permutation6 47 48 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation6 47) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation6 47 by rw [image6_eq]; rfl))

theorem lex_6_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 729) (Sat.Literal.pos 728) (Sat.Literal.pos 47) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation6 47 (assignment s)
    (Sat.Literal.pos 729) (Sat.Literal.pos 728) (Sat.Literal.pos 47) (Sat.Literal.pos 62) (positive_of_descriptor s 729 (.lex permutation6 47) (by rfl)) (lex_6_47_prefix s) (positive_select s 47) (lex_6_47_image s)

theorem lex_6_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.pos 47), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation6 47 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 728) (Sat.Literal.pos 47) (Sat.Literal.pos 62) (lex_6_47_prefix s) (positive_select s 47) (lex_6_47_image s)

theorem lex_6_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.pos 728)] :=
  (lex_6_47_gate s).prop _ (List.Mem.head _)

theorem lex_6_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.neg 47), (Sat.Literal.pos 62)] :=
  (lex_6_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.pos 47), (Sat.Literal.neg 62)] :=
  (lex_6_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.neg 47), (Sat.Literal.neg 62), (Sat.Literal.pos 729)] :=
  (lex_6_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 728), (Sat.Literal.pos 47), (Sat.Literal.pos 62), (Sat.Literal.pos 729)] :=
  (lex_6_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 729) = lexBefore s permutation6 46 := by
  exact (positive_lex_of_descriptor s 729 permutation6 47 (by rfl)).trans ((lex_skipped s permutation6 46 47 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation6 46) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation6 46 by rw [image6_eq]; rfl))

theorem lex_6_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 730) (Sat.Literal.pos 729) (Sat.Literal.pos 46) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation6 46 (assignment s)
    (Sat.Literal.pos 730) (Sat.Literal.pos 729) (Sat.Literal.pos 46) (Sat.Literal.pos 58) (positive_of_descriptor s 730 (.lex permutation6 46) (by rfl)) (lex_6_46_prefix s) (positive_select s 46) (lex_6_46_image s)

theorem lex_6_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.pos 46), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation6 46 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 729) (Sat.Literal.pos 46) (Sat.Literal.pos 58) (lex_6_46_prefix s) (positive_select s 46) (lex_6_46_image s)

theorem lex_6_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.pos 729)] :=
  (lex_6_46_gate s).prop _ (List.Mem.head _)

theorem lex_6_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.neg 46), (Sat.Literal.pos 58)] :=
  (lex_6_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.pos 46), (Sat.Literal.neg 58)] :=
  (lex_6_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.neg 46), (Sat.Literal.neg 58), (Sat.Literal.pos 730)] :=
  (lex_6_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 729), (Sat.Literal.pos 46), (Sat.Literal.pos 58), (Sat.Literal.pos 730)] :=
  (lex_6_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 730) = lexBefore s permutation6 45 := by
  exact (positive_lex_of_descriptor s 730 permutation6 46 (by rfl)).trans ((lex_skipped s permutation6 45 46 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation6 45) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation6 45 by rw [image6_eq]; rfl))

theorem lex_6_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 731) (Sat.Literal.pos 730) (Sat.Literal.pos 45) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation6 45 (assignment s)
    (Sat.Literal.pos 731) (Sat.Literal.pos 730) (Sat.Literal.pos 45) (Sat.Literal.pos 54) (positive_of_descriptor s 731 (.lex permutation6 45) (by rfl)) (lex_6_45_prefix s) (positive_select s 45) (lex_6_45_image s)

theorem lex_6_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.pos 45), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation6 45 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 730) (Sat.Literal.pos 45) (Sat.Literal.pos 54) (lex_6_45_prefix s) (positive_select s 45) (lex_6_45_image s)

theorem lex_6_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.pos 730)] :=
  (lex_6_45_gate s).prop _ (List.Mem.head _)

theorem lex_6_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.neg 45), (Sat.Literal.pos 54)] :=
  (lex_6_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.pos 45), (Sat.Literal.neg 54)] :=
  (lex_6_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.neg 45), (Sat.Literal.neg 54), (Sat.Literal.pos 731)] :=
  (lex_6_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 730), (Sat.Literal.pos 45), (Sat.Literal.pos 54), (Sat.Literal.pos 731)] :=
  (lex_6_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 731) = lexBefore s permutation6 44 := by
  exact (positive_lex_of_descriptor s 731 permutation6 45 (by rfl)).trans ((lex_skipped s permutation6 44 45 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation6 44) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation6 44 by rw [image6_eq]; rfl))

theorem lex_6_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 732) (Sat.Literal.pos 731) (Sat.Literal.pos 44) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation6 44 (assignment s)
    (Sat.Literal.pos 732) (Sat.Literal.pos 731) (Sat.Literal.pos 44) (Sat.Literal.pos 50) (positive_of_descriptor s 732 (.lex permutation6 44) (by rfl)) (lex_6_44_prefix s) (positive_select s 44) (lex_6_44_image s)

theorem lex_6_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.pos 44), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation6 44 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 731) (Sat.Literal.pos 44) (Sat.Literal.pos 50) (lex_6_44_prefix s) (positive_select s 44) (lex_6_44_image s)

theorem lex_6_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.pos 731)] :=
  (lex_6_44_gate s).prop _ (List.Mem.head _)

theorem lex_6_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.neg 44), (Sat.Literal.pos 50)] :=
  (lex_6_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.pos 44), (Sat.Literal.neg 50)] :=
  (lex_6_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.neg 44), (Sat.Literal.neg 50), (Sat.Literal.pos 732)] :=
  (lex_6_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 731), (Sat.Literal.pos 44), (Sat.Literal.pos 50), (Sat.Literal.pos 732)] :=
  (lex_6_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 732) = lexBefore s permutation6 43 := by
  exact (positive_lex_of_descriptor s 732 permutation6 44 (by rfl)).trans ((lex_skipped s permutation6 43 44 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation6 43) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation6 43 by rw [image6_eq]; rfl))

theorem lex_6_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 733) (Sat.Literal.pos 732) (Sat.Literal.pos 43) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation6 43 (assignment s)
    (Sat.Literal.pos 733) (Sat.Literal.pos 732) (Sat.Literal.pos 43) (Sat.Literal.pos 46) (positive_of_descriptor s 733 (.lex permutation6 43) (by rfl)) (lex_6_43_prefix s) (positive_select s 43) (lex_6_43_image s)

theorem lex_6_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.pos 43), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation6 43 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 732) (Sat.Literal.pos 43) (Sat.Literal.pos 46) (lex_6_43_prefix s) (positive_select s 43) (lex_6_43_image s)

theorem lex_6_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.pos 732)] :=
  (lex_6_43_gate s).prop _ (List.Mem.head _)

theorem lex_6_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.neg 43), (Sat.Literal.pos 46)] :=
  (lex_6_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.pos 43), (Sat.Literal.neg 46)] :=
  (lex_6_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.neg 43), (Sat.Literal.neg 46), (Sat.Literal.pos 733)] :=
  (lex_6_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 732), (Sat.Literal.pos 43), (Sat.Literal.pos 46), (Sat.Literal.pos 733)] :=
  (lex_6_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 733) = lexBefore s permutation6 41 := by
  exact (positive_lex_of_descriptor s 733 permutation6 43 (by rfl)).trans ((lex_skipped s permutation6 41 43 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 42 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation6 41) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation6 41 by rw [image6_eq]; rfl))

theorem lex_6_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 734) (Sat.Literal.pos 733) (Sat.Literal.pos 41) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation6 41 (assignment s)
    (Sat.Literal.pos 734) (Sat.Literal.pos 733) (Sat.Literal.pos 41) (Sat.Literal.pos 38) (positive_of_descriptor s 734 (.lex permutation6 41) (by rfl)) (lex_6_41_prefix s) (positive_select s 41) (lex_6_41_image s)

theorem lex_6_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.pos 41), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation6 41 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 733) (Sat.Literal.pos 41) (Sat.Literal.pos 38) (lex_6_41_prefix s) (positive_select s 41) (lex_6_41_image s)

theorem lex_6_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.pos 733)] :=
  (lex_6_41_gate s).prop _ (List.Mem.head _)

theorem lex_6_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.neg 41), (Sat.Literal.pos 38)] :=
  (lex_6_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.pos 41), (Sat.Literal.neg 38)] :=
  (lex_6_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.neg 41), (Sat.Literal.neg 38), (Sat.Literal.pos 734)] :=
  (lex_6_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 733), (Sat.Literal.pos 41), (Sat.Literal.pos 38), (Sat.Literal.pos 734)] :=
  (lex_6_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 734) = lexBefore s permutation6 40 := by
  exact (positive_lex_of_descriptor s 734 permutation6 41 (by rfl)).trans ((lex_skipped s permutation6 40 41 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation6 40) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation6 40 by rw [image6_eq]; rfl))

theorem lex_6_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 735) (Sat.Literal.pos 734) (Sat.Literal.pos 40) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation6 40 (assignment s)
    (Sat.Literal.pos 735) (Sat.Literal.pos 734) (Sat.Literal.pos 40) (Sat.Literal.pos 34) (positive_of_descriptor s 735 (.lex permutation6 40) (by rfl)) (lex_6_40_prefix s) (positive_select s 40) (lex_6_40_image s)

theorem lex_6_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.pos 40), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation6 40 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 734) (Sat.Literal.pos 40) (Sat.Literal.pos 34) (lex_6_40_prefix s) (positive_select s 40) (lex_6_40_image s)

theorem lex_6_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.pos 734)] :=
  (lex_6_40_gate s).prop _ (List.Mem.head _)

theorem lex_6_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.neg 40), (Sat.Literal.pos 34)] :=
  (lex_6_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.pos 40), (Sat.Literal.neg 34)] :=
  (lex_6_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.neg 40), (Sat.Literal.neg 34), (Sat.Literal.pos 735)] :=
  (lex_6_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 734), (Sat.Literal.pos 40), (Sat.Literal.pos 34), (Sat.Literal.pos 735)] :=
  (lex_6_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 735) = lexBefore s permutation6 39 := by
  exact (positive_lex_of_descriptor s 735 permutation6 40 (by rfl)).trans ((lex_skipped s permutation6 39 40 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation6 39) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation6 39 by rw [image6_eq]; rfl))

theorem lex_6_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 736) (Sat.Literal.pos 735) (Sat.Literal.pos 39) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation6 39 (assignment s)
    (Sat.Literal.pos 736) (Sat.Literal.pos 735) (Sat.Literal.pos 39) (Sat.Literal.pos 30) (positive_of_descriptor s 736 (.lex permutation6 39) (by rfl)) (lex_6_39_prefix s) (positive_select s 39) (lex_6_39_image s)

theorem lex_6_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.pos 39), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation6 39 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 735) (Sat.Literal.pos 39) (Sat.Literal.pos 30) (lex_6_39_prefix s) (positive_select s 39) (lex_6_39_image s)

theorem lex_6_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.pos 735)] :=
  (lex_6_39_gate s).prop _ (List.Mem.head _)

theorem lex_6_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.neg 39), (Sat.Literal.pos 30)] :=
  (lex_6_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.pos 39), (Sat.Literal.neg 30)] :=
  (lex_6_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.neg 39), (Sat.Literal.neg 30), (Sat.Literal.pos 736)] :=
  (lex_6_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 735), (Sat.Literal.pos 39), (Sat.Literal.pos 30), (Sat.Literal.pos 736)] :=
  (lex_6_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 736) = lexBefore s permutation6 38 := by
  exact (positive_lex_of_descriptor s 736 permutation6 39 (by rfl)).trans ((lex_skipped s permutation6 38 39 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation6 38) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation6 38 by rw [image6_eq]; rfl))

theorem lex_6_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 737) (Sat.Literal.pos 736) (Sat.Literal.pos 38) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation6 38 (assignment s)
    (Sat.Literal.pos 737) (Sat.Literal.pos 736) (Sat.Literal.pos 38) (Sat.Literal.pos 26) (positive_of_descriptor s 737 (.lex permutation6 38) (by rfl)) (lex_6_38_prefix s) (positive_select s 38) (lex_6_38_image s)

theorem lex_6_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.pos 38), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation6 38 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 736) (Sat.Literal.pos 38) (Sat.Literal.pos 26) (lex_6_38_prefix s) (positive_select s 38) (lex_6_38_image s)

theorem lex_6_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.pos 736)] :=
  (lex_6_38_gate s).prop _ (List.Mem.head _)

theorem lex_6_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.neg 38), (Sat.Literal.pos 26)] :=
  (lex_6_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.pos 38), (Sat.Literal.neg 26)] :=
  (lex_6_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.neg 38), (Sat.Literal.neg 26), (Sat.Literal.pos 737)] :=
  (lex_6_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 736), (Sat.Literal.pos 38), (Sat.Literal.pos 26), (Sat.Literal.pos 737)] :=
  (lex_6_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 737) = lexBefore s permutation6 37 := by
  exact (positive_lex_of_descriptor s 737 permutation6 38 (by rfl)).trans ((lex_skipped s permutation6 37 38 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation6 37) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation6 37 by rw [image6_eq]; rfl))

theorem lex_6_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 738) (Sat.Literal.pos 737) (Sat.Literal.pos 37) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation6 37 (assignment s)
    (Sat.Literal.pos 738) (Sat.Literal.pos 737) (Sat.Literal.pos 37) (Sat.Literal.pos 22) (positive_of_descriptor s 738 (.lex permutation6 37) (by rfl)) (lex_6_37_prefix s) (positive_select s 37) (lex_6_37_image s)

theorem lex_6_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.pos 37), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation6 37 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 737) (Sat.Literal.pos 37) (Sat.Literal.pos 22) (lex_6_37_prefix s) (positive_select s 37) (lex_6_37_image s)

theorem lex_6_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.pos 737)] :=
  (lex_6_37_gate s).prop _ (List.Mem.head _)

theorem lex_6_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.neg 37), (Sat.Literal.pos 22)] :=
  (lex_6_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.pos 37), (Sat.Literal.neg 22)] :=
  (lex_6_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.neg 37), (Sat.Literal.neg 22), (Sat.Literal.pos 738)] :=
  (lex_6_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 737), (Sat.Literal.pos 37), (Sat.Literal.pos 22), (Sat.Literal.pos 738)] :=
  (lex_6_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 738) = lexBefore s permutation6 36 := by
  exact (positive_lex_of_descriptor s 738 permutation6 37 (by rfl)).trans ((lex_skipped s permutation6 36 37 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation6 36) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation6 36 by rw [image6_eq]; rfl))

theorem lex_6_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 739) (Sat.Literal.pos 738) (Sat.Literal.pos 36) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation6 36 (assignment s)
    (Sat.Literal.pos 739) (Sat.Literal.pos 738) (Sat.Literal.pos 36) (Sat.Literal.pos 18) (positive_of_descriptor s 739 (.lex permutation6 36) (by rfl)) (lex_6_36_prefix s) (positive_select s 36) (lex_6_36_image s)

theorem lex_6_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.pos 36), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation6 36 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 738) (Sat.Literal.pos 36) (Sat.Literal.pos 18) (lex_6_36_prefix s) (positive_select s 36) (lex_6_36_image s)

theorem lex_6_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.pos 738)] :=
  (lex_6_36_gate s).prop _ (List.Mem.head _)

theorem lex_6_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.neg 36), (Sat.Literal.pos 18)] :=
  (lex_6_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.pos 36), (Sat.Literal.neg 18)] :=
  (lex_6_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.neg 36), (Sat.Literal.neg 18), (Sat.Literal.pos 739)] :=
  (lex_6_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 738), (Sat.Literal.pos 36), (Sat.Literal.pos 18), (Sat.Literal.pos 739)] :=
  (lex_6_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 739) = lexBefore s permutation6 35 := by
  exact (positive_lex_of_descriptor s 739 permutation6 36 (by rfl)).trans ((lex_skipped s permutation6 35 36 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation6 35) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation6 35 by rw [image6_eq]; rfl))

theorem lex_6_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 740) (Sat.Literal.pos 739) (Sat.Literal.pos 35) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation6 35 (assignment s)
    (Sat.Literal.pos 740) (Sat.Literal.pos 739) (Sat.Literal.pos 35) (Sat.Literal.pos 14) (positive_of_descriptor s 740 (.lex permutation6 35) (by rfl)) (lex_6_35_prefix s) (positive_select s 35) (lex_6_35_image s)

theorem lex_6_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.pos 35), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation6 35 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 739) (Sat.Literal.pos 35) (Sat.Literal.pos 14) (lex_6_35_prefix s) (positive_select s 35) (lex_6_35_image s)

theorem lex_6_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.pos 739)] :=
  (lex_6_35_gate s).prop _ (List.Mem.head _)

theorem lex_6_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.neg 35), (Sat.Literal.pos 14)] :=
  (lex_6_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.pos 35), (Sat.Literal.neg 14)] :=
  (lex_6_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.neg 35), (Sat.Literal.neg 14), (Sat.Literal.pos 740)] :=
  (lex_6_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 739), (Sat.Literal.pos 35), (Sat.Literal.pos 14), (Sat.Literal.pos 740)] :=
  (lex_6_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 740) = lexBefore s permutation6 34 := by
  exact (positive_lex_of_descriptor s 740 permutation6 35 (by rfl)).trans ((lex_skipped s permutation6 34 35 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation6 34) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation6 34 by rw [image6_eq]; rfl))

theorem lex_6_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 741) (Sat.Literal.pos 740) (Sat.Literal.pos 34) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation6 34 (assignment s)
    (Sat.Literal.pos 741) (Sat.Literal.pos 740) (Sat.Literal.pos 34) (Sat.Literal.pos 10) (positive_of_descriptor s 741 (.lex permutation6 34) (by rfl)) (lex_6_34_prefix s) (positive_select s 34) (lex_6_34_image s)

theorem lex_6_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.pos 34), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation6 34 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 740) (Sat.Literal.pos 34) (Sat.Literal.pos 10) (lex_6_34_prefix s) (positive_select s 34) (lex_6_34_image s)

theorem lex_6_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.pos 740)] :=
  (lex_6_34_gate s).prop _ (List.Mem.head _)

theorem lex_6_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.neg 34), (Sat.Literal.pos 10)] :=
  (lex_6_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.pos 34), (Sat.Literal.neg 10)] :=
  (lex_6_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.neg 34), (Sat.Literal.neg 10), (Sat.Literal.pos 741)] :=
  (lex_6_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 740), (Sat.Literal.pos 34), (Sat.Literal.pos 10), (Sat.Literal.pos 741)] :=
  (lex_6_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 741) = lexBefore s permutation6 33 := by
  exact (positive_lex_of_descriptor s 741 permutation6 34 (by rfl)).trans ((lex_skipped s permutation6 33 34 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation6 33) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation6 33 by rw [image6_eq]; rfl))

theorem lex_6_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 742) (Sat.Literal.pos 741) (Sat.Literal.pos 33) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation6 33 (assignment s)
    (Sat.Literal.pos 742) (Sat.Literal.pos 741) (Sat.Literal.pos 33) (Sat.Literal.pos 6) (positive_of_descriptor s 742 (.lex permutation6 33) (by rfl)) (lex_6_33_prefix s) (positive_select s 33) (lex_6_33_image s)

theorem lex_6_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.pos 33), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation6 33 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 741) (Sat.Literal.pos 33) (Sat.Literal.pos 6) (lex_6_33_prefix s) (positive_select s 33) (lex_6_33_image s)

theorem lex_6_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.pos 741)] :=
  (lex_6_33_gate s).prop _ (List.Mem.head _)

theorem lex_6_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.neg 33), (Sat.Literal.pos 6)] :=
  (lex_6_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.pos 33), (Sat.Literal.neg 6)] :=
  (lex_6_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.neg 33), (Sat.Literal.neg 6), (Sat.Literal.pos 742)] :=
  (lex_6_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 741), (Sat.Literal.pos 33), (Sat.Literal.pos 6), (Sat.Literal.pos 742)] :=
  (lex_6_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_32_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 742) = lexBefore s permutation6 32 := by
  exact (positive_lex_of_descriptor s 742 permutation6 33 (by rfl)).trans ((lex_skipped s permutation6 32 33 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_32_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation6 32) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation6 32 by rw [image6_eq]; rfl))

theorem lex_6_32_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 743) (Sat.Literal.pos 742) (Sat.Literal.pos 32) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation6 32 (assignment s)
    (Sat.Literal.pos 743) (Sat.Literal.pos 742) (Sat.Literal.pos 32) (Sat.Literal.pos 2) (positive_of_descriptor s 743 (.lex permutation6 32) (by rfl)) (lex_6_32_prefix s) (positive_select s 32) (lex_6_32_image s)

theorem lex_6_32_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.pos 32), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation6 32 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 742) (Sat.Literal.pos 32) (Sat.Literal.pos 2) (lex_6_32_prefix s) (positive_select s 32) (lex_6_32_image s)

theorem lex_6_32_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.pos 742)] :=
  (lex_6_32_gate s).prop _ (List.Mem.head _)

theorem lex_6_32_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.neg 32), (Sat.Literal.pos 2)] :=
  (lex_6_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_32_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.pos 32), (Sat.Literal.neg 2)] :=
  (lex_6_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_32_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.neg 32), (Sat.Literal.neg 2), (Sat.Literal.pos 743)] :=
  (lex_6_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_32_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 742), (Sat.Literal.pos 32), (Sat.Literal.pos 2), (Sat.Literal.pos 743)] :=
  (lex_6_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_31_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 743) = lexBefore s permutation6 31 := by
  exact (positive_lex_of_descriptor s 743 permutation6 32 (by rfl)).trans ((lex_skipped s permutation6 31 32 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_31_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation6 31) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation6 31 by rw [image6_eq]; rfl))

theorem lex_6_31_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 744) (Sat.Literal.pos 743) (Sat.Literal.pos 31) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation6 31 (assignment s)
    (Sat.Literal.pos 744) (Sat.Literal.pos 743) (Sat.Literal.pos 31) (Sat.Literal.pos 61) (positive_of_descriptor s 744 (.lex permutation6 31) (by rfl)) (lex_6_31_prefix s) (positive_select s 31) (lex_6_31_image s)

theorem lex_6_31_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.pos 31), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation6 31 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 743) (Sat.Literal.pos 31) (Sat.Literal.pos 61) (lex_6_31_prefix s) (positive_select s 31) (lex_6_31_image s)

theorem lex_6_31_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.pos 743)] :=
  (lex_6_31_gate s).prop _ (List.Mem.head _)

theorem lex_6_31_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.neg 31), (Sat.Literal.pos 61)] :=
  (lex_6_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_31_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.pos 31), (Sat.Literal.neg 61)] :=
  (lex_6_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_31_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.neg 31), (Sat.Literal.neg 61), (Sat.Literal.pos 744)] :=
  (lex_6_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_31_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 743), (Sat.Literal.pos 31), (Sat.Literal.pos 61), (Sat.Literal.pos 744)] :=
  (lex_6_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 744) = lexBefore s permutation6 30 := by
  exact (positive_lex_of_descriptor s 744 permutation6 31 (by rfl)).trans ((lex_skipped s permutation6 30 31 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation6 30) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation6 30 by rw [image6_eq]; rfl))

theorem lex_6_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 745) (Sat.Literal.pos 744) (Sat.Literal.pos 30) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation6 30 (assignment s)
    (Sat.Literal.pos 745) (Sat.Literal.pos 744) (Sat.Literal.pos 30) (Sat.Literal.pos 57) (positive_of_descriptor s 745 (.lex permutation6 30) (by rfl)) (lex_6_30_prefix s) (positive_select s 30) (lex_6_30_image s)

theorem lex_6_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.pos 30), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation6 30 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 744) (Sat.Literal.pos 30) (Sat.Literal.pos 57) (lex_6_30_prefix s) (positive_select s 30) (lex_6_30_image s)

theorem lex_6_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.pos 744)] :=
  (lex_6_30_gate s).prop _ (List.Mem.head _)

theorem lex_6_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.neg 30), (Sat.Literal.pos 57)] :=
  (lex_6_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.pos 30), (Sat.Literal.neg 57)] :=
  (lex_6_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.neg 30), (Sat.Literal.neg 57), (Sat.Literal.pos 745)] :=
  (lex_6_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 744), (Sat.Literal.pos 30), (Sat.Literal.pos 57), (Sat.Literal.pos 745)] :=
  (lex_6_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 745) = lexBefore s permutation6 29 := by
  exact (positive_lex_of_descriptor s 745 permutation6 30 (by rfl)).trans ((lex_skipped s permutation6 29 30 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation6 29) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation6 29 by rw [image6_eq]; rfl))

theorem lex_6_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 746) (Sat.Literal.pos 745) (Sat.Literal.pos 29) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation6 29 (assignment s)
    (Sat.Literal.pos 746) (Sat.Literal.pos 745) (Sat.Literal.pos 29) (Sat.Literal.pos 53) (positive_of_descriptor s 746 (.lex permutation6 29) (by rfl)) (lex_6_29_prefix s) (positive_select s 29) (lex_6_29_image s)

theorem lex_6_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.pos 29), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation6 29 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 745) (Sat.Literal.pos 29) (Sat.Literal.pos 53) (lex_6_29_prefix s) (positive_select s 29) (lex_6_29_image s)

theorem lex_6_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.pos 745)] :=
  (lex_6_29_gate s).prop _ (List.Mem.head _)

theorem lex_6_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.neg 29), (Sat.Literal.pos 53)] :=
  (lex_6_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.pos 29), (Sat.Literal.neg 53)] :=
  (lex_6_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.neg 29), (Sat.Literal.neg 53), (Sat.Literal.pos 746)] :=
  (lex_6_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 745), (Sat.Literal.pos 29), (Sat.Literal.pos 53), (Sat.Literal.pos 746)] :=
  (lex_6_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 746) = lexBefore s permutation6 28 := by
  exact (positive_lex_of_descriptor s 746 permutation6 29 (by rfl)).trans ((lex_skipped s permutation6 28 29 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation6 28) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation6 28 by rw [image6_eq]; rfl))

theorem lex_6_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 747) (Sat.Literal.pos 746) (Sat.Literal.pos 28) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation6 28 (assignment s)
    (Sat.Literal.pos 747) (Sat.Literal.pos 746) (Sat.Literal.pos 28) (Sat.Literal.pos 49) (positive_of_descriptor s 747 (.lex permutation6 28) (by rfl)) (lex_6_28_prefix s) (positive_select s 28) (lex_6_28_image s)

theorem lex_6_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.pos 28), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation6 28 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 746) (Sat.Literal.pos 28) (Sat.Literal.pos 49) (lex_6_28_prefix s) (positive_select s 28) (lex_6_28_image s)

theorem lex_6_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.pos 746)] :=
  (lex_6_28_gate s).prop _ (List.Mem.head _)

theorem lex_6_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.neg 28), (Sat.Literal.pos 49)] :=
  (lex_6_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.pos 28), (Sat.Literal.neg 49)] :=
  (lex_6_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.neg 28), (Sat.Literal.neg 49), (Sat.Literal.pos 747)] :=
  (lex_6_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 746), (Sat.Literal.pos 28), (Sat.Literal.pos 49), (Sat.Literal.pos 747)] :=
  (lex_6_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 747) = lexBefore s permutation6 27 := by
  exact (positive_lex_of_descriptor s 747 permutation6 28 (by rfl)).trans ((lex_skipped s permutation6 27 28 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation6 27) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation6 27 by rw [image6_eq]; rfl))

theorem lex_6_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 748) (Sat.Literal.pos 747) (Sat.Literal.pos 27) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation6 27 (assignment s)
    (Sat.Literal.pos 748) (Sat.Literal.pos 747) (Sat.Literal.pos 27) (Sat.Literal.pos 45) (positive_of_descriptor s 748 (.lex permutation6 27) (by rfl)) (lex_6_27_prefix s) (positive_select s 27) (lex_6_27_image s)

theorem lex_6_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.pos 27), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation6 27 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 747) (Sat.Literal.pos 27) (Sat.Literal.pos 45) (lex_6_27_prefix s) (positive_select s 27) (lex_6_27_image s)

theorem lex_6_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.pos 747)] :=
  (lex_6_27_gate s).prop _ (List.Mem.head _)

theorem lex_6_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.neg 27), (Sat.Literal.pos 45)] :=
  (lex_6_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.pos 27), (Sat.Literal.neg 45)] :=
  (lex_6_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.neg 27), (Sat.Literal.neg 45), (Sat.Literal.pos 748)] :=
  (lex_6_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 747), (Sat.Literal.pos 27), (Sat.Literal.pos 45), (Sat.Literal.pos 748)] :=
  (lex_6_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 748) = lexBefore s permutation6 26 := by
  exact (positive_lex_of_descriptor s 748 permutation6 27 (by rfl)).trans ((lex_skipped s permutation6 26 27 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation6 26) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation6 26 by rw [image6_eq]; rfl))

theorem lex_6_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 749) (Sat.Literal.pos 748) (Sat.Literal.pos 26) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation6 26 (assignment s)
    (Sat.Literal.pos 749) (Sat.Literal.pos 748) (Sat.Literal.pos 26) (Sat.Literal.pos 41) (positive_of_descriptor s 749 (.lex permutation6 26) (by rfl)) (lex_6_26_prefix s) (positive_select s 26) (lex_6_26_image s)

theorem lex_6_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.pos 26), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation6 26 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 748) (Sat.Literal.pos 26) (Sat.Literal.pos 41) (lex_6_26_prefix s) (positive_select s 26) (lex_6_26_image s)

theorem lex_6_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.pos 748)] :=
  (lex_6_26_gate s).prop _ (List.Mem.head _)

theorem lex_6_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.neg 26), (Sat.Literal.pos 41)] :=
  (lex_6_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.pos 26), (Sat.Literal.neg 41)] :=
  (lex_6_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.neg 26), (Sat.Literal.neg 41), (Sat.Literal.pos 749)] :=
  (lex_6_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 748), (Sat.Literal.pos 26), (Sat.Literal.pos 41), (Sat.Literal.pos 749)] :=
  (lex_6_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 749) = lexBefore s permutation6 25 := by
  exact (positive_lex_of_descriptor s 749 permutation6 26 (by rfl)).trans ((lex_skipped s permutation6 25 26 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation6 25) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation6 25 by rw [image6_eq]; rfl))

theorem lex_6_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 750) (Sat.Literal.pos 749) (Sat.Literal.pos 25) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation6 25 (assignment s)
    (Sat.Literal.pos 750) (Sat.Literal.pos 749) (Sat.Literal.pos 25) (Sat.Literal.pos 37) (positive_of_descriptor s 750 (.lex permutation6 25) (by rfl)) (lex_6_25_prefix s) (positive_select s 25) (lex_6_25_image s)

theorem lex_6_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.pos 25), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation6 25 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 749) (Sat.Literal.pos 25) (Sat.Literal.pos 37) (lex_6_25_prefix s) (positive_select s 25) (lex_6_25_image s)

theorem lex_6_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.pos 749)] :=
  (lex_6_25_gate s).prop _ (List.Mem.head _)

theorem lex_6_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.neg 25), (Sat.Literal.pos 37)] :=
  (lex_6_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.pos 25), (Sat.Literal.neg 37)] :=
  (lex_6_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.neg 25), (Sat.Literal.neg 37), (Sat.Literal.pos 750)] :=
  (lex_6_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 749), (Sat.Literal.pos 25), (Sat.Literal.pos 37), (Sat.Literal.pos 750)] :=
  (lex_6_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 750) = lexBefore s permutation6 24 := by
  exact (positive_lex_of_descriptor s 750 permutation6 25 (by rfl)).trans ((lex_skipped s permutation6 24 25 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation6 24) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation6 24 by rw [image6_eq]; rfl))

theorem lex_6_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 751) (Sat.Literal.pos 750) (Sat.Literal.pos 24) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation6 24 (assignment s)
    (Sat.Literal.pos 751) (Sat.Literal.pos 750) (Sat.Literal.pos 24) (Sat.Literal.pos 33) (positive_of_descriptor s 751 (.lex permutation6 24) (by rfl)) (lex_6_24_prefix s) (positive_select s 24) (lex_6_24_image s)

theorem lex_6_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.pos 24), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation6 24 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 750) (Sat.Literal.pos 24) (Sat.Literal.pos 33) (lex_6_24_prefix s) (positive_select s 24) (lex_6_24_image s)

theorem lex_6_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.pos 750)] :=
  (lex_6_24_gate s).prop _ (List.Mem.head _)

theorem lex_6_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.neg 24), (Sat.Literal.pos 33)] :=
  (lex_6_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.pos 24), (Sat.Literal.neg 33)] :=
  (lex_6_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.neg 24), (Sat.Literal.neg 33), (Sat.Literal.pos 751)] :=
  (lex_6_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 750), (Sat.Literal.pos 24), (Sat.Literal.pos 33), (Sat.Literal.pos 751)] :=
  (lex_6_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 751) = lexBefore s permutation6 23 := by
  exact (positive_lex_of_descriptor s 751 permutation6 24 (by rfl)).trans ((lex_skipped s permutation6 23 24 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation6 23) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation6 23 by rw [image6_eq]; rfl))

theorem lex_6_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 752) (Sat.Literal.pos 751) (Sat.Literal.pos 23) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation6 23 (assignment s)
    (Sat.Literal.pos 752) (Sat.Literal.pos 751) (Sat.Literal.pos 23) (Sat.Literal.pos 29) (positive_of_descriptor s 752 (.lex permutation6 23) (by rfl)) (lex_6_23_prefix s) (positive_select s 23) (lex_6_23_image s)

theorem lex_6_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.pos 23), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation6 23 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 751) (Sat.Literal.pos 23) (Sat.Literal.pos 29) (lex_6_23_prefix s) (positive_select s 23) (lex_6_23_image s)

theorem lex_6_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.pos 751)] :=
  (lex_6_23_gate s).prop _ (List.Mem.head _)

theorem lex_6_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.neg 23), (Sat.Literal.pos 29)] :=
  (lex_6_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.pos 23), (Sat.Literal.neg 29)] :=
  (lex_6_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.neg 23), (Sat.Literal.neg 29), (Sat.Literal.pos 752)] :=
  (lex_6_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 751), (Sat.Literal.pos 23), (Sat.Literal.pos 29), (Sat.Literal.pos 752)] :=
  (lex_6_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 752) = lexBefore s permutation6 22 := by
  exact (positive_lex_of_descriptor s 752 permutation6 23 (by rfl)).trans ((lex_skipped s permutation6 22 23 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation6 22) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation6 22 by rw [image6_eq]; rfl))

theorem lex_6_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 753) (Sat.Literal.pos 752) (Sat.Literal.pos 22) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation6 22 (assignment s)
    (Sat.Literal.pos 753) (Sat.Literal.pos 752) (Sat.Literal.pos 22) (Sat.Literal.pos 25) (positive_of_descriptor s 753 (.lex permutation6 22) (by rfl)) (lex_6_22_prefix s) (positive_select s 22) (lex_6_22_image s)

theorem lex_6_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.pos 22), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation6 22 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 752) (Sat.Literal.pos 22) (Sat.Literal.pos 25) (lex_6_22_prefix s) (positive_select s 22) (lex_6_22_image s)

theorem lex_6_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.pos 752)] :=
  (lex_6_22_gate s).prop _ (List.Mem.head _)

theorem lex_6_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.neg 22), (Sat.Literal.pos 25)] :=
  (lex_6_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.pos 22), (Sat.Literal.neg 25)] :=
  (lex_6_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.neg 22), (Sat.Literal.neg 25), (Sat.Literal.pos 753)] :=
  (lex_6_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 752), (Sat.Literal.pos 22), (Sat.Literal.pos 25), (Sat.Literal.pos 753)] :=
  (lex_6_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 753) = lexBefore s permutation6 20 := by
  exact (positive_lex_of_descriptor s 753 permutation6 22 (by rfl)).trans ((lex_skipped s permutation6 20 22 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 21 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation6 20) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation6 20 by rw [image6_eq]; rfl))

theorem lex_6_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 754) (Sat.Literal.pos 753) (Sat.Literal.pos 20) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation6 20 (assignment s)
    (Sat.Literal.pos 754) (Sat.Literal.pos 753) (Sat.Literal.pos 20) (Sat.Literal.pos 17) (positive_of_descriptor s 754 (.lex permutation6 20) (by rfl)) (lex_6_20_prefix s) (positive_select s 20) (lex_6_20_image s)

theorem lex_6_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.pos 20), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation6 20 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 753) (Sat.Literal.pos 20) (Sat.Literal.pos 17) (lex_6_20_prefix s) (positive_select s 20) (lex_6_20_image s)

theorem lex_6_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.pos 753)] :=
  (lex_6_20_gate s).prop _ (List.Mem.head _)

theorem lex_6_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.neg 20), (Sat.Literal.pos 17)] :=
  (lex_6_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.pos 20), (Sat.Literal.neg 17)] :=
  (lex_6_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.neg 20), (Sat.Literal.neg 17), (Sat.Literal.pos 754)] :=
  (lex_6_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 753), (Sat.Literal.pos 20), (Sat.Literal.pos 17), (Sat.Literal.pos 754)] :=
  (lex_6_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 754) = lexBefore s permutation6 19 := by
  exact (positive_lex_of_descriptor s 754 permutation6 20 (by rfl)).trans ((lex_skipped s permutation6 19 20 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation6 19) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation6 19 by rw [image6_eq]; rfl))

theorem lex_6_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 755) (Sat.Literal.pos 754) (Sat.Literal.pos 19) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation6 19 (assignment s)
    (Sat.Literal.pos 755) (Sat.Literal.pos 754) (Sat.Literal.pos 19) (Sat.Literal.pos 13) (positive_of_descriptor s 755 (.lex permutation6 19) (by rfl)) (lex_6_19_prefix s) (positive_select s 19) (lex_6_19_image s)

theorem lex_6_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.pos 19), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation6 19 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 754) (Sat.Literal.pos 19) (Sat.Literal.pos 13) (lex_6_19_prefix s) (positive_select s 19) (lex_6_19_image s)

theorem lex_6_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.pos 754)] :=
  (lex_6_19_gate s).prop _ (List.Mem.head _)

theorem lex_6_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.neg 19), (Sat.Literal.pos 13)] :=
  (lex_6_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.pos 19), (Sat.Literal.neg 13)] :=
  (lex_6_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.neg 19), (Sat.Literal.neg 13), (Sat.Literal.pos 755)] :=
  (lex_6_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 754), (Sat.Literal.pos 19), (Sat.Literal.pos 13), (Sat.Literal.pos 755)] :=
  (lex_6_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 755) = lexBefore s permutation6 18 := by
  exact (positive_lex_of_descriptor s 755 permutation6 19 (by rfl)).trans ((lex_skipped s permutation6 18 19 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation6 18) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation6 18 by rw [image6_eq]; rfl))

theorem lex_6_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 756) (Sat.Literal.pos 755) (Sat.Literal.pos 18) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation6 18 (assignment s)
    (Sat.Literal.pos 756) (Sat.Literal.pos 755) (Sat.Literal.pos 18) (Sat.Literal.pos 9) (positive_of_descriptor s 756 (.lex permutation6 18) (by rfl)) (lex_6_18_prefix s) (positive_select s 18) (lex_6_18_image s)

theorem lex_6_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.pos 18), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation6 18 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 755) (Sat.Literal.pos 18) (Sat.Literal.pos 9) (lex_6_18_prefix s) (positive_select s 18) (lex_6_18_image s)

theorem lex_6_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.pos 755)] :=
  (lex_6_18_gate s).prop _ (List.Mem.head _)

theorem lex_6_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.neg 18), (Sat.Literal.pos 9)] :=
  (lex_6_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.pos 18), (Sat.Literal.neg 9)] :=
  (lex_6_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.neg 18), (Sat.Literal.neg 9), (Sat.Literal.pos 756)] :=
  (lex_6_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 755), (Sat.Literal.pos 18), (Sat.Literal.pos 9), (Sat.Literal.pos 756)] :=
  (lex_6_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 756) = lexBefore s permutation6 17 := by
  exact (positive_lex_of_descriptor s 756 permutation6 18 (by rfl)).trans ((lex_skipped s permutation6 17 18 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation6 17) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation6 17 by rw [image6_eq]; rfl))

theorem lex_6_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 757) (Sat.Literal.pos 756) (Sat.Literal.pos 17) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation6 17 (assignment s)
    (Sat.Literal.pos 757) (Sat.Literal.pos 756) (Sat.Literal.pos 17) (Sat.Literal.pos 5) (positive_of_descriptor s 757 (.lex permutation6 17) (by rfl)) (lex_6_17_prefix s) (positive_select s 17) (lex_6_17_image s)

theorem lex_6_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.pos 17), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation6 17 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 756) (Sat.Literal.pos 17) (Sat.Literal.pos 5) (lex_6_17_prefix s) (positive_select s 17) (lex_6_17_image s)

theorem lex_6_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.pos 756)] :=
  (lex_6_17_gate s).prop _ (List.Mem.head _)

theorem lex_6_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.neg 17), (Sat.Literal.pos 5)] :=
  (lex_6_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.pos 17), (Sat.Literal.neg 5)] :=
  (lex_6_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.neg 17), (Sat.Literal.neg 5), (Sat.Literal.pos 757)] :=
  (lex_6_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 756), (Sat.Literal.pos 17), (Sat.Literal.pos 5), (Sat.Literal.pos 757)] :=
  (lex_6_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 757) = lexBefore s permutation6 16 := by
  exact (positive_lex_of_descriptor s 757 permutation6 17 (by rfl)).trans ((lex_skipped s permutation6 16 17 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation6 16) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 64) = permuteMask permutation6 16 by rw [image6_eq]; rfl))

theorem lex_6_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 758) (Sat.Literal.pos 757) (Sat.Literal.pos 16) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation6 16 (assignment s)
    (Sat.Literal.pos 758) (Sat.Literal.pos 757) (Sat.Literal.pos 16) (Sat.Literal.pos 1) (positive_of_descriptor s 758 (.lex permutation6 16) (by rfl)) (lex_6_16_prefix s) (positive_select s 16) (lex_6_16_image s)

theorem lex_6_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.pos 16), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation6 16 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 757) (Sat.Literal.pos 16) (Sat.Literal.pos 1) (lex_6_16_prefix s) (positive_select s 16) (lex_6_16_image s)

theorem lex_6_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.pos 757)] :=
  (lex_6_16_gate s).prop _ (List.Mem.head _)

theorem lex_6_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.neg 16), (Sat.Literal.pos 1)] :=
  (lex_6_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.pos 16), (Sat.Literal.neg 1)] :=
  (lex_6_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.neg 16), (Sat.Literal.neg 1), (Sat.Literal.pos 758)] :=
  (lex_6_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 757), (Sat.Literal.pos 16), (Sat.Literal.pos 1), (Sat.Literal.pos 758)] :=
  (lex_6_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_15_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 758) = lexBefore s permutation6 15 := by
  exact (positive_lex_of_descriptor s 758 permutation6 16 (by rfl)).trans ((lex_skipped s permutation6 15 16 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_15_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation6 15) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 64) = permuteMask permutation6 15 by rw [image6_eq]; rfl))

theorem lex_6_15_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 759) (Sat.Literal.pos 758) (Sat.Literal.pos 15) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation6 15 (assignment s)
    (Sat.Literal.pos 759) (Sat.Literal.pos 758) (Sat.Literal.pos 15) (Sat.Literal.pos 60) (positive_of_descriptor s 759 (.lex permutation6 15) (by rfl)) (lex_6_15_prefix s) (positive_select s 15) (lex_6_15_image s)

theorem lex_6_15_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.pos 15), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation6 15 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 758) (Sat.Literal.pos 15) (Sat.Literal.pos 60) (lex_6_15_prefix s) (positive_select s 15) (lex_6_15_image s)

theorem lex_6_15_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.pos 758)] :=
  (lex_6_15_gate s).prop _ (List.Mem.head _)

theorem lex_6_15_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.neg 15), (Sat.Literal.pos 60)] :=
  (lex_6_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_15_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.pos 15), (Sat.Literal.neg 60)] :=
  (lex_6_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_15_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.neg 15), (Sat.Literal.neg 60), (Sat.Literal.pos 759)] :=
  (lex_6_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_15_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 758), (Sat.Literal.pos 15), (Sat.Literal.pos 60), (Sat.Literal.pos 759)] :=
  (lex_6_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 759) = lexBefore s permutation6 14 := by
  exact (positive_lex_of_descriptor s 759 permutation6 15 (by rfl)).trans ((lex_skipped s permutation6 14 15 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation6 14) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 64) = permuteMask permutation6 14 by rw [image6_eq]; rfl))

theorem lex_6_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 760) (Sat.Literal.pos 759) (Sat.Literal.pos 14) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation6 14 (assignment s)
    (Sat.Literal.pos 760) (Sat.Literal.pos 759) (Sat.Literal.pos 14) (Sat.Literal.pos 56) (positive_of_descriptor s 760 (.lex permutation6 14) (by rfl)) (lex_6_14_prefix s) (positive_select s 14) (lex_6_14_image s)

theorem lex_6_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.pos 14), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation6 14 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 759) (Sat.Literal.pos 14) (Sat.Literal.pos 56) (lex_6_14_prefix s) (positive_select s 14) (lex_6_14_image s)

theorem lex_6_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.pos 759)] :=
  (lex_6_14_gate s).prop _ (List.Mem.head _)

theorem lex_6_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.neg 14), (Sat.Literal.pos 56)] :=
  (lex_6_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.pos 14), (Sat.Literal.neg 56)] :=
  (lex_6_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.neg 14), (Sat.Literal.neg 56), (Sat.Literal.pos 760)] :=
  (lex_6_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 759), (Sat.Literal.pos 14), (Sat.Literal.pos 56), (Sat.Literal.pos 760)] :=
  (lex_6_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 760) = lexBefore s permutation6 13 := by
  exact (positive_lex_of_descriptor s 760 permutation6 14 (by rfl)).trans ((lex_skipped s permutation6 13 14 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation6 13) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation6 13 by rw [image6_eq]; rfl))

theorem lex_6_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 761) (Sat.Literal.pos 760) (Sat.Literal.pos 13) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation6 13 (assignment s)
    (Sat.Literal.pos 761) (Sat.Literal.pos 760) (Sat.Literal.pos 13) (Sat.Literal.pos 52) (positive_of_descriptor s 761 (.lex permutation6 13) (by rfl)) (lex_6_13_prefix s) (positive_select s 13) (lex_6_13_image s)

theorem lex_6_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.pos 13), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation6 13 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 760) (Sat.Literal.pos 13) (Sat.Literal.pos 52) (lex_6_13_prefix s) (positive_select s 13) (lex_6_13_image s)

theorem lex_6_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.pos 760)] :=
  (lex_6_13_gate s).prop _ (List.Mem.head _)

theorem lex_6_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.neg 13), (Sat.Literal.pos 52)] :=
  (lex_6_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.pos 13), (Sat.Literal.neg 52)] :=
  (lex_6_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.neg 13), (Sat.Literal.neg 52), (Sat.Literal.pos 761)] :=
  (lex_6_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 760), (Sat.Literal.pos 13), (Sat.Literal.pos 52), (Sat.Literal.pos 761)] :=
  (lex_6_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 761) = lexBefore s permutation6 12 := by
  exact (positive_lex_of_descriptor s 761 permutation6 13 (by rfl)).trans ((lex_skipped s permutation6 12 13 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation6 12) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 64) = permuteMask permutation6 12 by rw [image6_eq]; rfl))

theorem lex_6_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 762) (Sat.Literal.pos 761) (Sat.Literal.pos 12) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation6 12 (assignment s)
    (Sat.Literal.pos 762) (Sat.Literal.pos 761) (Sat.Literal.pos 12) (Sat.Literal.pos 48) (positive_of_descriptor s 762 (.lex permutation6 12) (by rfl)) (lex_6_12_prefix s) (positive_select s 12) (lex_6_12_image s)

theorem lex_6_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.pos 12), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation6 12 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 761) (Sat.Literal.pos 12) (Sat.Literal.pos 48) (lex_6_12_prefix s) (positive_select s 12) (lex_6_12_image s)

theorem lex_6_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.pos 761)] :=
  (lex_6_12_gate s).prop _ (List.Mem.head _)

theorem lex_6_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.neg 12), (Sat.Literal.pos 48)] :=
  (lex_6_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.pos 12), (Sat.Literal.neg 48)] :=
  (lex_6_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.neg 12), (Sat.Literal.neg 48), (Sat.Literal.pos 762)] :=
  (lex_6_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 761), (Sat.Literal.pos 12), (Sat.Literal.pos 48), (Sat.Literal.pos 762)] :=
  (lex_6_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 762) = lexBefore s permutation6 11 := by
  exact (positive_lex_of_descriptor s 762 permutation6 12 (by rfl)).trans ((lex_skipped s permutation6 11 12 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation6 11) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation6 11 by rw [image6_eq]; rfl))

theorem lex_6_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 763) (Sat.Literal.pos 762) (Sat.Literal.pos 11) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation6 11 (assignment s)
    (Sat.Literal.pos 763) (Sat.Literal.pos 762) (Sat.Literal.pos 11) (Sat.Literal.pos 44) (positive_of_descriptor s 763 (.lex permutation6 11) (by rfl)) (lex_6_11_prefix s) (positive_select s 11) (lex_6_11_image s)

theorem lex_6_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.pos 11), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation6 11 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 762) (Sat.Literal.pos 11) (Sat.Literal.pos 44) (lex_6_11_prefix s) (positive_select s 11) (lex_6_11_image s)

theorem lex_6_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.pos 762)] :=
  (lex_6_11_gate s).prop _ (List.Mem.head _)

theorem lex_6_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.neg 11), (Sat.Literal.pos 44)] :=
  (lex_6_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.pos 11), (Sat.Literal.neg 44)] :=
  (lex_6_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.neg 11), (Sat.Literal.neg 44), (Sat.Literal.pos 763)] :=
  (lex_6_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 762), (Sat.Literal.pos 11), (Sat.Literal.pos 44), (Sat.Literal.pos 763)] :=
  (lex_6_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 763) = lexBefore s permutation6 10 := by
  exact (positive_lex_of_descriptor s 763 permutation6 11 (by rfl)).trans ((lex_skipped s permutation6 10 11 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation6 10) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation6 10 by rw [image6_eq]; rfl))

theorem lex_6_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 764) (Sat.Literal.pos 763) (Sat.Literal.pos 10) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation6 10 (assignment s)
    (Sat.Literal.pos 764) (Sat.Literal.pos 763) (Sat.Literal.pos 10) (Sat.Literal.pos 40) (positive_of_descriptor s 764 (.lex permutation6 10) (by rfl)) (lex_6_10_prefix s) (positive_select s 10) (lex_6_10_image s)

theorem lex_6_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.pos 10), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation6 10 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 763) (Sat.Literal.pos 10) (Sat.Literal.pos 40) (lex_6_10_prefix s) (positive_select s 10) (lex_6_10_image s)

theorem lex_6_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.pos 763)] :=
  (lex_6_10_gate s).prop _ (List.Mem.head _)

theorem lex_6_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.neg 10), (Sat.Literal.pos 40)] :=
  (lex_6_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.pos 10), (Sat.Literal.neg 40)] :=
  (lex_6_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.neg 10), (Sat.Literal.neg 40), (Sat.Literal.pos 764)] :=
  (lex_6_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 763), (Sat.Literal.pos 10), (Sat.Literal.pos 40), (Sat.Literal.pos 764)] :=
  (lex_6_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 764) = lexBefore s permutation6 9 := by
  exact (positive_lex_of_descriptor s 764 permutation6 10 (by rfl)).trans ((lex_skipped s permutation6 9 10 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation6 9) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation6 9 by rw [image6_eq]; rfl))

theorem lex_6_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 765) (Sat.Literal.pos 764) (Sat.Literal.pos 9) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation6 9 (assignment s)
    (Sat.Literal.pos 765) (Sat.Literal.pos 764) (Sat.Literal.pos 9) (Sat.Literal.pos 36) (positive_of_descriptor s 765 (.lex permutation6 9) (by rfl)) (lex_6_9_prefix s) (positive_select s 9) (lex_6_9_image s)

theorem lex_6_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.pos 9), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation6 9 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 764) (Sat.Literal.pos 9) (Sat.Literal.pos 36) (lex_6_9_prefix s) (positive_select s 9) (lex_6_9_image s)

theorem lex_6_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.pos 764)] :=
  (lex_6_9_gate s).prop _ (List.Mem.head _)

theorem lex_6_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.neg 9), (Sat.Literal.pos 36)] :=
  (lex_6_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.pos 9), (Sat.Literal.neg 36)] :=
  (lex_6_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.neg 9), (Sat.Literal.neg 36), (Sat.Literal.pos 765)] :=
  (lex_6_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 764), (Sat.Literal.pos 9), (Sat.Literal.pos 36), (Sat.Literal.pos 765)] :=
  (lex_6_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 765) = lexBefore s permutation6 8 := by
  exact (positive_lex_of_descriptor s 765 permutation6 9 (by rfl)).trans ((lex_skipped s permutation6 8 9 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation6 8) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 64) = permuteMask permutation6 8 by rw [image6_eq]; rfl))

theorem lex_6_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 766) (Sat.Literal.pos 765) (Sat.Literal.pos 8) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation6 8 (assignment s)
    (Sat.Literal.pos 766) (Sat.Literal.pos 765) (Sat.Literal.pos 8) (Sat.Literal.pos 32) (positive_of_descriptor s 766 (.lex permutation6 8) (by rfl)) (lex_6_8_prefix s) (positive_select s 8) (lex_6_8_image s)

theorem lex_6_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.pos 8), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation6 8 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 765) (Sat.Literal.pos 8) (Sat.Literal.pos 32) (lex_6_8_prefix s) (positive_select s 8) (lex_6_8_image s)

theorem lex_6_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.pos 765)] :=
  (lex_6_8_gate s).prop _ (List.Mem.head _)

theorem lex_6_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.neg 8), (Sat.Literal.pos 32)] :=
  (lex_6_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.pos 8), (Sat.Literal.neg 32)] :=
  (lex_6_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.neg 8), (Sat.Literal.neg 32), (Sat.Literal.pos 766)] :=
  (lex_6_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 765), (Sat.Literal.pos 8), (Sat.Literal.pos 32), (Sat.Literal.pos 766)] :=
  (lex_6_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_7_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 766) = lexBefore s permutation6 7 := by
  exact (positive_lex_of_descriptor s 766 permutation6 8 (by rfl)).trans ((lex_skipped s permutation6 7 8 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_7_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation6 7) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation6 7 by rw [image6_eq]; rfl))

theorem lex_6_7_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 767) (Sat.Literal.pos 766) (Sat.Literal.pos 7) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation6 7 (assignment s)
    (Sat.Literal.pos 767) (Sat.Literal.pos 766) (Sat.Literal.pos 7) (Sat.Literal.pos 28) (positive_of_descriptor s 767 (.lex permutation6 7) (by rfl)) (lex_6_7_prefix s) (positive_select s 7) (lex_6_7_image s)

theorem lex_6_7_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.pos 7), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation6 7 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 766) (Sat.Literal.pos 7) (Sat.Literal.pos 28) (lex_6_7_prefix s) (positive_select s 7) (lex_6_7_image s)

theorem lex_6_7_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.pos 766)] :=
  (lex_6_7_gate s).prop _ (List.Mem.head _)

theorem lex_6_7_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.neg 7), (Sat.Literal.pos 28)] :=
  (lex_6_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_7_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.pos 7), (Sat.Literal.neg 28)] :=
  (lex_6_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_7_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.neg 7), (Sat.Literal.neg 28), (Sat.Literal.pos 767)] :=
  (lex_6_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_7_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 766), (Sat.Literal.pos 7), (Sat.Literal.pos 28), (Sat.Literal.pos 767)] :=
  (lex_6_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 767) = lexBefore s permutation6 6 := by
  exact (positive_lex_of_descriptor s 767 permutation6 7 (by rfl)).trans ((lex_skipped s permutation6 6 7 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation6 6) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation6 6 by rw [image6_eq]; rfl))

theorem lex_6_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 768) (Sat.Literal.pos 767) (Sat.Literal.pos 6) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation6 6 (assignment s)
    (Sat.Literal.pos 768) (Sat.Literal.pos 767) (Sat.Literal.pos 6) (Sat.Literal.pos 24) (positive_of_descriptor s 768 (.lex permutation6 6) (by rfl)) (lex_6_6_prefix s) (positive_select s 6) (lex_6_6_image s)

theorem lex_6_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.pos 6), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation6 6 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 767) (Sat.Literal.pos 6) (Sat.Literal.pos 24) (lex_6_6_prefix s) (positive_select s 6) (lex_6_6_image s)

theorem lex_6_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.pos 767)] :=
  (lex_6_6_gate s).prop _ (List.Mem.head _)

theorem lex_6_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.neg 6), (Sat.Literal.pos 24)] :=
  (lex_6_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.pos 6), (Sat.Literal.neg 24)] :=
  (lex_6_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.neg 6), (Sat.Literal.neg 24), (Sat.Literal.pos 768)] :=
  (lex_6_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 767), (Sat.Literal.pos 6), (Sat.Literal.pos 24), (Sat.Literal.pos 768)] :=
  (lex_6_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 768) = lexBefore s permutation6 5 := by
  exact (positive_lex_of_descriptor s 768 permutation6 6 (by rfl)).trans ((lex_skipped s permutation6 5 6 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation6 5) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation6 5 by rw [image6_eq]; rfl))

theorem lex_6_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 769) (Sat.Literal.pos 768) (Sat.Literal.pos 5) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation6 5 (assignment s)
    (Sat.Literal.pos 769) (Sat.Literal.pos 768) (Sat.Literal.pos 5) (Sat.Literal.pos 20) (positive_of_descriptor s 769 (.lex permutation6 5) (by rfl)) (lex_6_5_prefix s) (positive_select s 5) (lex_6_5_image s)

theorem lex_6_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.pos 5), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation6 5 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 768) (Sat.Literal.pos 5) (Sat.Literal.pos 20) (lex_6_5_prefix s) (positive_select s 5) (lex_6_5_image s)

theorem lex_6_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.pos 768)] :=
  (lex_6_5_gate s).prop _ (List.Mem.head _)

theorem lex_6_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.neg 5), (Sat.Literal.pos 20)] :=
  (lex_6_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.pos 5), (Sat.Literal.neg 20)] :=
  (lex_6_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.neg 5), (Sat.Literal.neg 20), (Sat.Literal.pos 769)] :=
  (lex_6_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 768), (Sat.Literal.pos 5), (Sat.Literal.pos 20), (Sat.Literal.pos 769)] :=
  (lex_6_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 769) = lexBefore s permutation6 4 := by
  exact (positive_lex_of_descriptor s 769 permutation6 5 (by rfl)).trans ((lex_skipped s permutation6 4 5 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation6 4) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation6 4 by rw [image6_eq]; rfl))

theorem lex_6_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 770) (Sat.Literal.pos 769) (Sat.Literal.pos 4) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation6 4 (assignment s)
    (Sat.Literal.pos 770) (Sat.Literal.pos 769) (Sat.Literal.pos 4) (Sat.Literal.pos 16) (positive_of_descriptor s 770 (.lex permutation6 4) (by rfl)) (lex_6_4_prefix s) (positive_select s 4) (lex_6_4_image s)

theorem lex_6_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.pos 4), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation6 4 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 769) (Sat.Literal.pos 4) (Sat.Literal.pos 16) (lex_6_4_prefix s) (positive_select s 4) (lex_6_4_image s)

theorem lex_6_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.pos 769)] :=
  (lex_6_4_gate s).prop _ (List.Mem.head _)

theorem lex_6_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.neg 4), (Sat.Literal.pos 16)] :=
  (lex_6_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.pos 4), (Sat.Literal.neg 16)] :=
  (lex_6_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.neg 4), (Sat.Literal.neg 16), (Sat.Literal.pos 770)] :=
  (lex_6_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 769), (Sat.Literal.pos 4), (Sat.Literal.pos 16), (Sat.Literal.pos 770)] :=
  (lex_6_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_3_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 770) = lexBefore s permutation6 3 := by
  exact (positive_lex_of_descriptor s 770 permutation6 4 (by rfl)).trans ((lex_skipped s permutation6 3 4 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_3_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation6 3) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation6 3 by rw [image6_eq]; rfl))

theorem lex_6_3_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 771) (Sat.Literal.pos 770) (Sat.Literal.pos 3) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation6 3 (assignment s)
    (Sat.Literal.pos 771) (Sat.Literal.pos 770) (Sat.Literal.pos 3) (Sat.Literal.pos 12) (positive_of_descriptor s 771 (.lex permutation6 3) (by rfl)) (lex_6_3_prefix s) (positive_select s 3) (lex_6_3_image s)

theorem lex_6_3_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.pos 3), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation6 3 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 770) (Sat.Literal.pos 3) (Sat.Literal.pos 12) (lex_6_3_prefix s) (positive_select s 3) (lex_6_3_image s)

theorem lex_6_3_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.pos 770)] :=
  (lex_6_3_gate s).prop _ (List.Mem.head _)

theorem lex_6_3_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.neg 3), (Sat.Literal.pos 12)] :=
  (lex_6_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_3_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.pos 3), (Sat.Literal.neg 12)] :=
  (lex_6_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_3_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.neg 3), (Sat.Literal.neg 12), (Sat.Literal.pos 771)] :=
  (lex_6_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_3_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 770), (Sat.Literal.pos 3), (Sat.Literal.pos 12), (Sat.Literal.pos 771)] :=
  (lex_6_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 771) = lexBefore s permutation6 2 := by
  exact (positive_lex_of_descriptor s 771 permutation6 3 (by rfl)).trans ((lex_skipped s permutation6 2 3 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation6 2) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation6 2 by rw [image6_eq]; rfl))

theorem lex_6_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 772) (Sat.Literal.pos 771) (Sat.Literal.pos 2) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation6 2 (assignment s)
    (Sat.Literal.pos 772) (Sat.Literal.pos 771) (Sat.Literal.pos 2) (Sat.Literal.pos 8) (positive_of_descriptor s 772 (.lex permutation6 2) (by rfl)) (lex_6_2_prefix s) (positive_select s 2) (lex_6_2_image s)

theorem lex_6_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.pos 2), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation6 2 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 771) (Sat.Literal.pos 2) (Sat.Literal.pos 8) (lex_6_2_prefix s) (positive_select s 2) (lex_6_2_image s)

theorem lex_6_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.pos 771)] :=
  (lex_6_2_gate s).prop _ (List.Mem.head _)

theorem lex_6_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.neg 2), (Sat.Literal.pos 8)] :=
  (lex_6_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.pos 2), (Sat.Literal.neg 8)] :=
  (lex_6_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.neg 2), (Sat.Literal.neg 8), (Sat.Literal.pos 772)] :=
  (lex_6_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 771), (Sat.Literal.pos 2), (Sat.Literal.pos 8), (Sat.Literal.pos 772)] :=
  (lex_6_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_1_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 772) = lexBefore s permutation6 1 := by
  exact (positive_lex_of_descriptor s 772 permutation6 2 (by rfl)).trans ((lex_skipped s permutation6 1 2 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_1_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation6 1) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation6 1 by rw [image6_eq]; rfl))

theorem lex_6_1_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 773) (Sat.Literal.pos 772) (Sat.Literal.pos 1) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation6 1 (assignment s)
    (Sat.Literal.pos 773) (Sat.Literal.pos 772) (Sat.Literal.pos 1) (Sat.Literal.pos 4) (positive_of_descriptor s 773 (.lex permutation6 1) (by rfl)) (lex_6_1_prefix s) (positive_select s 1) (lex_6_1_image s)

theorem lex_6_1_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.pos 1), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation6 1 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 772) (Sat.Literal.pos 1) (Sat.Literal.pos 4) (lex_6_1_prefix s) (positive_select s 1) (lex_6_1_image s)

theorem lex_6_1_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 773), (Sat.Literal.pos 772)] :=
  (lex_6_1_gate s).prop _ (List.Mem.head _)

theorem lex_6_1_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 773), (Sat.Literal.neg 1), (Sat.Literal.pos 4)] :=
  (lex_6_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_1_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 773), (Sat.Literal.pos 1), (Sat.Literal.neg 4)] :=
  (lex_6_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_1_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.neg 1), (Sat.Literal.neg 4), (Sat.Literal.pos 773)] :=
  (lex_6_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_1_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 772), (Sat.Literal.pos 1), (Sat.Literal.pos 4), (Sat.Literal.pos 773)] :=
  (lex_6_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation7 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation7 62 (by intro j hj; rw [image7_eq]; exact fixedOnRange_spec image7 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_7_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation7 62) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation7 62 by rw [image7_eq]; rfl))

theorem lex_7_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 774) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation7 62 (assignment s)
    (Sat.Literal.pos 774) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 55) (positive_of_descriptor s 774 (.lex permutation7 62) (by rfl)) (lex_7_62_prefix s) (positive_select s 62) (lex_7_62_image s)

theorem lex_7_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation7 62 (hmax permutation7) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 55) (lex_7_62_prefix s) (positive_select s 62) (lex_7_62_image s)

theorem lex_7_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.neg 64)] :=
  (lex_7_62_gate s).prop _ (List.Mem.head _)

theorem lex_7_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.neg 62), (Sat.Literal.pos 55)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.pos 62), (Sat.Literal.neg 55)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 55), (Sat.Literal.pos 774)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 55), (Sat.Literal.pos 774)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 774) = lexBefore s permutation7 61 := by
  exact (positive_lex_of_descriptor s 774 permutation7 62 (by rfl)).trans ((lex_skipped s permutation7 61 62 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation7 61) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation7 61 by rw [image7_eq]; rfl))

theorem lex_7_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 775) (Sat.Literal.pos 774) (Sat.Literal.pos 61) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation7 61 (assignment s)
    (Sat.Literal.pos 775) (Sat.Literal.pos 774) (Sat.Literal.pos 61) (Sat.Literal.pos 47) (positive_of_descriptor s 775 (.lex permutation7 61) (by rfl)) (lex_7_61_prefix s) (positive_select s 61) (lex_7_61_image s)

theorem lex_7_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.pos 61), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation7 61 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 774) (Sat.Literal.pos 61) (Sat.Literal.pos 47) (lex_7_61_prefix s) (positive_select s 61) (lex_7_61_image s)

theorem lex_7_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.pos 774)] :=
  (lex_7_61_gate s).prop _ (List.Mem.head _)

theorem lex_7_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.neg 61), (Sat.Literal.pos 47)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.pos 61), (Sat.Literal.neg 47)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.neg 61), (Sat.Literal.neg 47), (Sat.Literal.pos 775)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 774), (Sat.Literal.pos 61), (Sat.Literal.pos 47), (Sat.Literal.pos 775)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_60_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 775) = lexBefore s permutation7 60 := by
  exact (positive_lex_of_descriptor s 775 permutation7 61 (by rfl)).trans ((lex_skipped s permutation7 60 61 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_60_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation7 60) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation7 60 by rw [image7_eq]; rfl))

theorem lex_7_60_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 776) (Sat.Literal.pos 775) (Sat.Literal.pos 60) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation7 60 (assignment s)
    (Sat.Literal.pos 776) (Sat.Literal.pos 775) (Sat.Literal.pos 60) (Sat.Literal.pos 39) (positive_of_descriptor s 776 (.lex permutation7 60) (by rfl)) (lex_7_60_prefix s) (positive_select s 60) (lex_7_60_image s)

theorem lex_7_60_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.pos 60), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation7 60 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 775) (Sat.Literal.pos 60) (Sat.Literal.pos 39) (lex_7_60_prefix s) (positive_select s 60) (lex_7_60_image s)

theorem lex_7_60_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.pos 775)] :=
  (lex_7_60_gate s).prop _ (List.Mem.head _)

theorem lex_7_60_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.neg 60), (Sat.Literal.pos 39)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_60_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.pos 60), (Sat.Literal.neg 39)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_60_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.neg 60), (Sat.Literal.neg 39), (Sat.Literal.pos 776)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_60_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 775), (Sat.Literal.pos 60), (Sat.Literal.pos 39), (Sat.Literal.pos 776)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 776) = lexBefore s permutation7 59 := by
  exact (positive_lex_of_descriptor s 776 permutation7 60 (by rfl)).trans ((lex_skipped s permutation7 59 60 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation7 59) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation7 59 by rw [image7_eq]; rfl))

theorem lex_7_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 777) (Sat.Literal.pos 776) (Sat.Literal.pos 59) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation7 59 (assignment s)
    (Sat.Literal.pos 777) (Sat.Literal.pos 776) (Sat.Literal.pos 59) (Sat.Literal.pos 31) (positive_of_descriptor s 777 (.lex permutation7 59) (by rfl)) (lex_7_59_prefix s) (positive_select s 59) (lex_7_59_image s)

theorem lex_7_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.pos 59), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation7 59 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 776) (Sat.Literal.pos 59) (Sat.Literal.pos 31) (lex_7_59_prefix s) (positive_select s 59) (lex_7_59_image s)

theorem lex_7_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.pos 776)] :=
  (lex_7_59_gate s).prop _ (List.Mem.head _)

theorem lex_7_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.neg 59), (Sat.Literal.pos 31)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.pos 59), (Sat.Literal.neg 31)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.neg 59), (Sat.Literal.neg 31), (Sat.Literal.pos 777)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 776), (Sat.Literal.pos 59), (Sat.Literal.pos 31), (Sat.Literal.pos 777)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 777) = lexBefore s permutation7 58 := by
  exact (positive_lex_of_descriptor s 777 permutation7 59 (by rfl)).trans ((lex_skipped s permutation7 58 59 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation7 58) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation7 58 by rw [image7_eq]; rfl))

theorem lex_7_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 778) (Sat.Literal.pos 777) (Sat.Literal.pos 58) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation7 58 (assignment s)
    (Sat.Literal.pos 778) (Sat.Literal.pos 777) (Sat.Literal.pos 58) (Sat.Literal.pos 23) (positive_of_descriptor s 778 (.lex permutation7 58) (by rfl)) (lex_7_58_prefix s) (positive_select s 58) (lex_7_58_image s)

theorem lex_7_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.pos 58), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation7 58 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 777) (Sat.Literal.pos 58) (Sat.Literal.pos 23) (lex_7_58_prefix s) (positive_select s 58) (lex_7_58_image s)

theorem lex_7_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.pos 777)] :=
  (lex_7_58_gate s).prop _ (List.Mem.head _)

theorem lex_7_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.neg 58), (Sat.Literal.pos 23)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.pos 58), (Sat.Literal.neg 23)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.neg 58), (Sat.Literal.neg 23), (Sat.Literal.pos 778)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 777), (Sat.Literal.pos 58), (Sat.Literal.pos 23), (Sat.Literal.pos 778)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 778) = lexBefore s permutation7 57 := by
  exact (positive_lex_of_descriptor s 778 permutation7 58 (by rfl)).trans ((lex_skipped s permutation7 57 58 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation7 57) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 64) = permuteMask permutation7 57 by rw [image7_eq]; rfl))

theorem lex_7_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 779) (Sat.Literal.pos 778) (Sat.Literal.pos 57) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation7 57 (assignment s)
    (Sat.Literal.pos 779) (Sat.Literal.pos 778) (Sat.Literal.pos 57) (Sat.Literal.pos 15) (positive_of_descriptor s 779 (.lex permutation7 57) (by rfl)) (lex_7_57_prefix s) (positive_select s 57) (lex_7_57_image s)

theorem lex_7_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.pos 57), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation7 57 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 778) (Sat.Literal.pos 57) (Sat.Literal.pos 15) (lex_7_57_prefix s) (positive_select s 57) (lex_7_57_image s)

theorem lex_7_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.pos 778)] :=
  (lex_7_57_gate s).prop _ (List.Mem.head _)

theorem lex_7_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.neg 57), (Sat.Literal.pos 15)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.pos 57), (Sat.Literal.neg 15)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.neg 57), (Sat.Literal.neg 15), (Sat.Literal.pos 779)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 778), (Sat.Literal.pos 57), (Sat.Literal.pos 15), (Sat.Literal.pos 779)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_56_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 779) = lexBefore s permutation7 56 := by
  exact (positive_lex_of_descriptor s 779 permutation7 57 (by rfl)).trans ((lex_skipped s permutation7 56 57 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_56_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation7 56) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 64) = permuteMask permutation7 56 by rw [image7_eq]; rfl))

theorem lex_7_56_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 780) (Sat.Literal.pos 779) (Sat.Literal.pos 56) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation7 56 (assignment s)
    (Sat.Literal.pos 780) (Sat.Literal.pos 779) (Sat.Literal.pos 56) (Sat.Literal.pos 7) (positive_of_descriptor s 780 (.lex permutation7 56) (by rfl)) (lex_7_56_prefix s) (positive_select s 56) (lex_7_56_image s)

theorem lex_7_56_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.pos 56), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation7 56 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 779) (Sat.Literal.pos 56) (Sat.Literal.pos 7) (lex_7_56_prefix s) (positive_select s 56) (lex_7_56_image s)

theorem lex_7_56_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.pos 779)] :=
  (lex_7_56_gate s).prop _ (List.Mem.head _)

theorem lex_7_56_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.neg 56), (Sat.Literal.pos 7)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_56_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.pos 56), (Sat.Literal.neg 7)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_56_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.neg 56), (Sat.Literal.neg 7), (Sat.Literal.pos 780)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_56_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 779), (Sat.Literal.pos 56), (Sat.Literal.pos 7), (Sat.Literal.pos 780)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 780) = lexBefore s permutation7 55 := by
  exact (positive_lex_of_descriptor s 780 permutation7 56 (by rfl)).trans ((lex_skipped s permutation7 55 56 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation7 55) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation7 55 by rw [image7_eq]; rfl))

theorem lex_7_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 781) (Sat.Literal.pos 780) (Sat.Literal.pos 55) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation7 55 (assignment s)
    (Sat.Literal.pos 781) (Sat.Literal.pos 780) (Sat.Literal.pos 55) (Sat.Literal.pos 62) (positive_of_descriptor s 781 (.lex permutation7 55) (by rfl)) (lex_7_55_prefix s) (positive_select s 55) (lex_7_55_image s)

theorem lex_7_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.pos 55), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation7 55 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 780) (Sat.Literal.pos 55) (Sat.Literal.pos 62) (lex_7_55_prefix s) (positive_select s 55) (lex_7_55_image s)

theorem lex_7_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.pos 780)] :=
  (lex_7_55_gate s).prop _ (List.Mem.head _)

theorem lex_7_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.neg 55), (Sat.Literal.pos 62)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.pos 55), (Sat.Literal.neg 62)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.neg 55), (Sat.Literal.neg 62), (Sat.Literal.pos 781)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 780), (Sat.Literal.pos 55), (Sat.Literal.pos 62), (Sat.Literal.pos 781)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 781) = lexBefore s permutation7 53 := by
  exact (positive_lex_of_descriptor s 781 permutation7 55 (by rfl)).trans ((lex_skipped s permutation7 53 55 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 54 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation7 53) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation7 53 by rw [image7_eq]; rfl))

theorem lex_7_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 782) (Sat.Literal.pos 781) (Sat.Literal.pos 53) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation7 53 (assignment s)
    (Sat.Literal.pos 782) (Sat.Literal.pos 781) (Sat.Literal.pos 53) (Sat.Literal.pos 46) (positive_of_descriptor s 782 (.lex permutation7 53) (by rfl)) (lex_7_53_prefix s) (positive_select s 53) (lex_7_53_image s)

theorem lex_7_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.pos 53), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation7 53 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 781) (Sat.Literal.pos 53) (Sat.Literal.pos 46) (lex_7_53_prefix s) (positive_select s 53) (lex_7_53_image s)

theorem lex_7_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.pos 781)] :=
  (lex_7_53_gate s).prop _ (List.Mem.head _)

theorem lex_7_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.neg 53), (Sat.Literal.pos 46)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.pos 53), (Sat.Literal.neg 46)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.neg 53), (Sat.Literal.neg 46), (Sat.Literal.pos 782)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 781), (Sat.Literal.pos 53), (Sat.Literal.pos 46), (Sat.Literal.pos 782)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 782) = lexBefore s permutation7 52 := by
  exact (positive_lex_of_descriptor s 782 permutation7 53 (by rfl)).trans ((lex_skipped s permutation7 52 53 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation7 52) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation7 52 by rw [image7_eq]; rfl))

theorem lex_7_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 783) (Sat.Literal.pos 782) (Sat.Literal.pos 52) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation7 52 (assignment s)
    (Sat.Literal.pos 783) (Sat.Literal.pos 782) (Sat.Literal.pos 52) (Sat.Literal.pos 38) (positive_of_descriptor s 783 (.lex permutation7 52) (by rfl)) (lex_7_52_prefix s) (positive_select s 52) (lex_7_52_image s)

theorem lex_7_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.pos 52), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation7 52 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 782) (Sat.Literal.pos 52) (Sat.Literal.pos 38) (lex_7_52_prefix s) (positive_select s 52) (lex_7_52_image s)

theorem lex_7_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.pos 782)] :=
  (lex_7_52_gate s).prop _ (List.Mem.head _)

theorem lex_7_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.neg 52), (Sat.Literal.pos 38)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.pos 52), (Sat.Literal.neg 38)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.neg 52), (Sat.Literal.neg 38), (Sat.Literal.pos 783)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 782), (Sat.Literal.pos 52), (Sat.Literal.pos 38), (Sat.Literal.pos 783)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 783) = lexBefore s permutation7 51 := by
  exact (positive_lex_of_descriptor s 783 permutation7 52 (by rfl)).trans ((lex_skipped s permutation7 51 52 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation7 51) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation7 51 by rw [image7_eq]; rfl))

theorem lex_7_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 784) (Sat.Literal.pos 783) (Sat.Literal.pos 51) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation7 51 (assignment s)
    (Sat.Literal.pos 784) (Sat.Literal.pos 783) (Sat.Literal.pos 51) (Sat.Literal.pos 30) (positive_of_descriptor s 784 (.lex permutation7 51) (by rfl)) (lex_7_51_prefix s) (positive_select s 51) (lex_7_51_image s)

theorem lex_7_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.pos 51), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation7 51 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 783) (Sat.Literal.pos 51) (Sat.Literal.pos 30) (lex_7_51_prefix s) (positive_select s 51) (lex_7_51_image s)

theorem lex_7_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.pos 783)] :=
  (lex_7_51_gate s).prop _ (List.Mem.head _)

theorem lex_7_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.neg 51), (Sat.Literal.pos 30)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.pos 51), (Sat.Literal.neg 30)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.neg 51), (Sat.Literal.neg 30), (Sat.Literal.pos 784)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 783), (Sat.Literal.pos 51), (Sat.Literal.pos 30), (Sat.Literal.pos 784)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 784) = lexBefore s permutation7 50 := by
  exact (positive_lex_of_descriptor s 784 permutation7 51 (by rfl)).trans ((lex_skipped s permutation7 50 51 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation7 50) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation7 50 by rw [image7_eq]; rfl))

theorem lex_7_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 785) (Sat.Literal.pos 784) (Sat.Literal.pos 50) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation7 50 (assignment s)
    (Sat.Literal.pos 785) (Sat.Literal.pos 784) (Sat.Literal.pos 50) (Sat.Literal.pos 22) (positive_of_descriptor s 785 (.lex permutation7 50) (by rfl)) (lex_7_50_prefix s) (positive_select s 50) (lex_7_50_image s)

theorem lex_7_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.pos 50), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation7 50 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 784) (Sat.Literal.pos 50) (Sat.Literal.pos 22) (lex_7_50_prefix s) (positive_select s 50) (lex_7_50_image s)

theorem lex_7_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.pos 784)] :=
  (lex_7_50_gate s).prop _ (List.Mem.head _)

theorem lex_7_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.neg 50), (Sat.Literal.pos 22)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.pos 50), (Sat.Literal.neg 22)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.neg 50), (Sat.Literal.neg 22), (Sat.Literal.pos 785)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 784), (Sat.Literal.pos 50), (Sat.Literal.pos 22), (Sat.Literal.pos 785)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 785) = lexBefore s permutation7 49 := by
  exact (positive_lex_of_descriptor s 785 permutation7 50 (by rfl)).trans ((lex_skipped s permutation7 49 50 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation7 49) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation7 49 by rw [image7_eq]; rfl))

theorem lex_7_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 786) (Sat.Literal.pos 785) (Sat.Literal.pos 49) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation7 49 (assignment s)
    (Sat.Literal.pos 786) (Sat.Literal.pos 785) (Sat.Literal.pos 49) (Sat.Literal.pos 14) (positive_of_descriptor s 786 (.lex permutation7 49) (by rfl)) (lex_7_49_prefix s) (positive_select s 49) (lex_7_49_image s)

theorem lex_7_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.pos 49), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation7 49 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 785) (Sat.Literal.pos 49) (Sat.Literal.pos 14) (lex_7_49_prefix s) (positive_select s 49) (lex_7_49_image s)

theorem lex_7_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.pos 785)] :=
  (lex_7_49_gate s).prop _ (List.Mem.head _)

theorem lex_7_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.neg 49), (Sat.Literal.pos 14)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.pos 49), (Sat.Literal.neg 14)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.neg 49), (Sat.Literal.neg 14), (Sat.Literal.pos 786)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 785), (Sat.Literal.pos 49), (Sat.Literal.pos 14), (Sat.Literal.pos 786)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_48_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 786) = lexBefore s permutation7 48 := by
  exact (positive_lex_of_descriptor s 786 permutation7 49 (by rfl)).trans ((lex_skipped s permutation7 48 49 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_48_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation7 48) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation7 48 by rw [image7_eq]; rfl))

theorem lex_7_48_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 787) (Sat.Literal.pos 786) (Sat.Literal.pos 48) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation7 48 (assignment s)
    (Sat.Literal.pos 787) (Sat.Literal.pos 786) (Sat.Literal.pos 48) (Sat.Literal.pos 6) (positive_of_descriptor s 787 (.lex permutation7 48) (by rfl)) (lex_7_48_prefix s) (positive_select s 48) (lex_7_48_image s)

theorem lex_7_48_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.pos 48), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation7 48 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 786) (Sat.Literal.pos 48) (Sat.Literal.pos 6) (lex_7_48_prefix s) (positive_select s 48) (lex_7_48_image s)

theorem lex_7_48_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.pos 786)] :=
  (lex_7_48_gate s).prop _ (List.Mem.head _)

theorem lex_7_48_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.neg 48), (Sat.Literal.pos 6)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_48_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.pos 48), (Sat.Literal.neg 6)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_48_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.neg 48), (Sat.Literal.neg 6), (Sat.Literal.pos 787)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_48_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 786), (Sat.Literal.pos 48), (Sat.Literal.pos 6), (Sat.Literal.pos 787)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 787) = lexBefore s permutation7 47 := by
  exact (positive_lex_of_descriptor s 787 permutation7 48 (by rfl)).trans ((lex_skipped s permutation7 47 48 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation7 47) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation7 47 by rw [image7_eq]; rfl))

theorem lex_7_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 788) (Sat.Literal.pos 787) (Sat.Literal.pos 47) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation7 47 (assignment s)
    (Sat.Literal.pos 788) (Sat.Literal.pos 787) (Sat.Literal.pos 47) (Sat.Literal.pos 61) (positive_of_descriptor s 788 (.lex permutation7 47) (by rfl)) (lex_7_47_prefix s) (positive_select s 47) (lex_7_47_image s)

theorem lex_7_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.pos 47), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation7 47 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 787) (Sat.Literal.pos 47) (Sat.Literal.pos 61) (lex_7_47_prefix s) (positive_select s 47) (lex_7_47_image s)

theorem lex_7_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.pos 787)] :=
  (lex_7_47_gate s).prop _ (List.Mem.head _)

theorem lex_7_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.neg 47), (Sat.Literal.pos 61)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.pos 47), (Sat.Literal.neg 61)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.neg 47), (Sat.Literal.neg 61), (Sat.Literal.pos 788)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 787), (Sat.Literal.pos 47), (Sat.Literal.pos 61), (Sat.Literal.pos 788)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 788) = lexBefore s permutation7 46 := by
  exact (positive_lex_of_descriptor s 788 permutation7 47 (by rfl)).trans ((lex_skipped s permutation7 46 47 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation7 46) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation7 46 by rw [image7_eq]; rfl))

theorem lex_7_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 789) (Sat.Literal.pos 788) (Sat.Literal.pos 46) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation7 46 (assignment s)
    (Sat.Literal.pos 789) (Sat.Literal.pos 788) (Sat.Literal.pos 46) (Sat.Literal.pos 53) (positive_of_descriptor s 789 (.lex permutation7 46) (by rfl)) (lex_7_46_prefix s) (positive_select s 46) (lex_7_46_image s)

theorem lex_7_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.pos 46), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation7 46 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 788) (Sat.Literal.pos 46) (Sat.Literal.pos 53) (lex_7_46_prefix s) (positive_select s 46) (lex_7_46_image s)

theorem lex_7_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.pos 788)] :=
  (lex_7_46_gate s).prop _ (List.Mem.head _)

theorem lex_7_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.neg 46), (Sat.Literal.pos 53)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.pos 46), (Sat.Literal.neg 53)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.neg 46), (Sat.Literal.neg 53), (Sat.Literal.pos 789)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 788), (Sat.Literal.pos 46), (Sat.Literal.pos 53), (Sat.Literal.pos 789)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 789) = lexBefore s permutation7 44 := by
  exact (positive_lex_of_descriptor s 789 permutation7 46 (by rfl)).trans ((lex_skipped s permutation7 44 46 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 45 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation7 44) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation7 44 by rw [image7_eq]; rfl))

theorem lex_7_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 790) (Sat.Literal.pos 789) (Sat.Literal.pos 44) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation7 44 (assignment s)
    (Sat.Literal.pos 790) (Sat.Literal.pos 789) (Sat.Literal.pos 44) (Sat.Literal.pos 37) (positive_of_descriptor s 790 (.lex permutation7 44) (by rfl)) (lex_7_44_prefix s) (positive_select s 44) (lex_7_44_image s)

theorem lex_7_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.pos 44), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation7 44 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 789) (Sat.Literal.pos 44) (Sat.Literal.pos 37) (lex_7_44_prefix s) (positive_select s 44) (lex_7_44_image s)

theorem lex_7_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.pos 789)] :=
  (lex_7_44_gate s).prop _ (List.Mem.head _)

theorem lex_7_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.neg 44), (Sat.Literal.pos 37)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.pos 44), (Sat.Literal.neg 37)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.neg 44), (Sat.Literal.neg 37), (Sat.Literal.pos 790)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 789), (Sat.Literal.pos 44), (Sat.Literal.pos 37), (Sat.Literal.pos 790)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 790) = lexBefore s permutation7 43 := by
  exact (positive_lex_of_descriptor s 790 permutation7 44 (by rfl)).trans ((lex_skipped s permutation7 43 44 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation7 43) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation7 43 by rw [image7_eq]; rfl))

theorem lex_7_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 791) (Sat.Literal.pos 790) (Sat.Literal.pos 43) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation7 43 (assignment s)
    (Sat.Literal.pos 791) (Sat.Literal.pos 790) (Sat.Literal.pos 43) (Sat.Literal.pos 29) (positive_of_descriptor s 791 (.lex permutation7 43) (by rfl)) (lex_7_43_prefix s) (positive_select s 43) (lex_7_43_image s)

theorem lex_7_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.pos 43), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation7 43 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 790) (Sat.Literal.pos 43) (Sat.Literal.pos 29) (lex_7_43_prefix s) (positive_select s 43) (lex_7_43_image s)

theorem lex_7_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.pos 790)] :=
  (lex_7_43_gate s).prop _ (List.Mem.head _)

theorem lex_7_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.neg 43), (Sat.Literal.pos 29)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 791), (Sat.Literal.pos 43), (Sat.Literal.neg 29)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.neg 43), (Sat.Literal.neg 29), (Sat.Literal.pos 791)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 790), (Sat.Literal.pos 43), (Sat.Literal.pos 29), (Sat.Literal.pos 791)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_5_22_gate

end Crown.CertificateSixData
