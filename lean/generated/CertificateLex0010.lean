import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_7_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3524) = lexBefore s permutation7 150 := by
  exact (positive_lex_of_descriptor s 3524 permutation7 151 (by rfl)).trans ((lex_skipped s permutation7 150 151 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation7 150) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation7 150 by rw [image7_eq]; rfl))

theorem lex_7_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3525) (Sat.Literal.pos 3524) (Sat.Literal.pos 150) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation7 150 (assignment s)
    (Sat.Literal.pos 3525) (Sat.Literal.pos 3524) (Sat.Literal.pos 150) (Sat.Literal.pos 45) (positive_of_descriptor s 3525 (.lex permutation7 150) (by rfl)) (lex_7_150_prefix s) (positive_select s 150) (lex_7_150_image s)

theorem lex_7_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.pos 150), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation7 150 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3524) (Sat.Literal.pos 150) (Sat.Literal.pos 45) (lex_7_150_prefix s) (positive_select s 150) (lex_7_150_image s)

theorem lex_7_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.pos 3524)] :=
  (lex_7_150_gate s).prop _ (List.Mem.head _)

theorem lex_7_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.neg 150), (Sat.Literal.pos 45)] :=
  (lex_7_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.pos 150), (Sat.Literal.neg 45)] :=
  (lex_7_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.neg 150), (Sat.Literal.neg 45), (Sat.Literal.pos 3525)] :=
  (lex_7_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.pos 150), (Sat.Literal.pos 45), (Sat.Literal.pos 3525)] :=
  (lex_7_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3525) = lexBefore s permutation7 149 := by
  exact (positive_lex_of_descriptor s 3525 permutation7 150 (by rfl)).trans ((lex_skipped s permutation7 149 150 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation7 149) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation7 149 by rw [image7_eq]; rfl))

theorem lex_7_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3526) (Sat.Literal.pos 3525) (Sat.Literal.pos 149) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation7 149 (assignment s)
    (Sat.Literal.pos 3526) (Sat.Literal.pos 3525) (Sat.Literal.pos 149) (Sat.Literal.pos 43) (positive_of_descriptor s 3526 (.lex permutation7 149) (by rfl)) (lex_7_149_prefix s) (positive_select s 149) (lex_7_149_image s)

theorem lex_7_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.pos 149), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation7 149 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3525) (Sat.Literal.pos 149) (Sat.Literal.pos 43) (lex_7_149_prefix s) (positive_select s 149) (lex_7_149_image s)

theorem lex_7_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.pos 3525)] :=
  (lex_7_149_gate s).prop _ (List.Mem.head _)

theorem lex_7_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.neg 149), (Sat.Literal.pos 43)] :=
  (lex_7_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.pos 149), (Sat.Literal.neg 43)] :=
  (lex_7_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.neg 149), (Sat.Literal.neg 43), (Sat.Literal.pos 3526)] :=
  (lex_7_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3525), (Sat.Literal.pos 149), (Sat.Literal.pos 43), (Sat.Literal.pos 3526)] :=
  (lex_7_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3526) = lexBefore s permutation7 148 := by
  exact (positive_lex_of_descriptor s 3526 permutation7 149 (by rfl)).trans ((lex_skipped s permutation7 148 149 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation7 148) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation7 148 by rw [image7_eq]; rfl))

theorem lex_7_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3527) (Sat.Literal.pos 3526) (Sat.Literal.pos 148) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation7 148 (assignment s)
    (Sat.Literal.pos 3527) (Sat.Literal.pos 3526) (Sat.Literal.pos 148) (Sat.Literal.pos 41) (positive_of_descriptor s 3527 (.lex permutation7 148) (by rfl)) (lex_7_148_prefix s) (positive_select s 148) (lex_7_148_image s)

theorem lex_7_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.pos 148), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation7 148 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3526) (Sat.Literal.pos 148) (Sat.Literal.pos 41) (lex_7_148_prefix s) (positive_select s 148) (lex_7_148_image s)

theorem lex_7_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.pos 3526)] :=
  (lex_7_148_gate s).prop _ (List.Mem.head _)

theorem lex_7_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.neg 148), (Sat.Literal.pos 41)] :=
  (lex_7_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.pos 148), (Sat.Literal.neg 41)] :=
  (lex_7_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.neg 148), (Sat.Literal.neg 41), (Sat.Literal.pos 3527)] :=
  (lex_7_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3526), (Sat.Literal.pos 148), (Sat.Literal.pos 41), (Sat.Literal.pos 3527)] :=
  (lex_7_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3527) = lexBefore s permutation7 147 := by
  exact (positive_lex_of_descriptor s 3527 permutation7 148 (by rfl)).trans ((lex_skipped s permutation7 147 148 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation7 147) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation7 147 by rw [image7_eq]; rfl))

theorem lex_7_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3528) (Sat.Literal.pos 3527) (Sat.Literal.pos 147) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation7 147 (assignment s)
    (Sat.Literal.pos 3528) (Sat.Literal.pos 3527) (Sat.Literal.pos 147) (Sat.Literal.pos 39) (positive_of_descriptor s 3528 (.lex permutation7 147) (by rfl)) (lex_7_147_prefix s) (positive_select s 147) (lex_7_147_image s)

theorem lex_7_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.pos 147), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation7 147 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3527) (Sat.Literal.pos 147) (Sat.Literal.pos 39) (lex_7_147_prefix s) (positive_select s 147) (lex_7_147_image s)

theorem lex_7_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.pos 3527)] :=
  (lex_7_147_gate s).prop _ (List.Mem.head _)

theorem lex_7_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.neg 147), (Sat.Literal.pos 39)] :=
  (lex_7_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.pos 147), (Sat.Literal.neg 39)] :=
  (lex_7_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.neg 147), (Sat.Literal.neg 39), (Sat.Literal.pos 3528)] :=
  (lex_7_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3527), (Sat.Literal.pos 147), (Sat.Literal.pos 39), (Sat.Literal.pos 3528)] :=
  (lex_7_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3528) = lexBefore s permutation7 146 := by
  exact (positive_lex_of_descriptor s 3528 permutation7 147 (by rfl)).trans ((lex_skipped s permutation7 146 147 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation7 146) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation7 146 by rw [image7_eq]; rfl))

theorem lex_7_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3529) (Sat.Literal.pos 3528) (Sat.Literal.pos 146) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation7 146 (assignment s)
    (Sat.Literal.pos 3529) (Sat.Literal.pos 3528) (Sat.Literal.pos 146) (Sat.Literal.pos 37) (positive_of_descriptor s 3529 (.lex permutation7 146) (by rfl)) (lex_7_146_prefix s) (positive_select s 146) (lex_7_146_image s)

theorem lex_7_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.pos 146), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation7 146 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3528) (Sat.Literal.pos 146) (Sat.Literal.pos 37) (lex_7_146_prefix s) (positive_select s 146) (lex_7_146_image s)

theorem lex_7_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.pos 3528)] :=
  (lex_7_146_gate s).prop _ (List.Mem.head _)

theorem lex_7_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.neg 146), (Sat.Literal.pos 37)] :=
  (lex_7_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.pos 146), (Sat.Literal.neg 37)] :=
  (lex_7_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.neg 146), (Sat.Literal.neg 37), (Sat.Literal.pos 3529)] :=
  (lex_7_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3528), (Sat.Literal.pos 146), (Sat.Literal.pos 37), (Sat.Literal.pos 3529)] :=
  (lex_7_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3529) = lexBefore s permutation7 145 := by
  exact (positive_lex_of_descriptor s 3529 permutation7 146 (by rfl)).trans ((lex_skipped s permutation7 145 146 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation7 145) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation7 145 by rw [image7_eq]; rfl))

theorem lex_7_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3530) (Sat.Literal.pos 3529) (Sat.Literal.pos 145) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation7 145 (assignment s)
    (Sat.Literal.pos 3530) (Sat.Literal.pos 3529) (Sat.Literal.pos 145) (Sat.Literal.pos 35) (positive_of_descriptor s 3530 (.lex permutation7 145) (by rfl)) (lex_7_145_prefix s) (positive_select s 145) (lex_7_145_image s)

theorem lex_7_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.pos 145), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation7 145 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3529) (Sat.Literal.pos 145) (Sat.Literal.pos 35) (lex_7_145_prefix s) (positive_select s 145) (lex_7_145_image s)

theorem lex_7_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.pos 3529)] :=
  (lex_7_145_gate s).prop _ (List.Mem.head _)

theorem lex_7_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.neg 145), (Sat.Literal.pos 35)] :=
  (lex_7_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.pos 145), (Sat.Literal.neg 35)] :=
  (lex_7_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.neg 145), (Sat.Literal.neg 35), (Sat.Literal.pos 3530)] :=
  (lex_7_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3529), (Sat.Literal.pos 145), (Sat.Literal.pos 35), (Sat.Literal.pos 3530)] :=
  (lex_7_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3530) = lexBefore s permutation7 144 := by
  exact (positive_lex_of_descriptor s 3530 permutation7 145 (by rfl)).trans ((lex_skipped s permutation7 144 145 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation7 144) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation7 144 by rw [image7_eq]; rfl))

theorem lex_7_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3531) (Sat.Literal.pos 3530) (Sat.Literal.pos 144) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation7 144 (assignment s)
    (Sat.Literal.pos 3531) (Sat.Literal.pos 3530) (Sat.Literal.pos 144) (Sat.Literal.pos 33) (positive_of_descriptor s 3531 (.lex permutation7 144) (by rfl)) (lex_7_144_prefix s) (positive_select s 144) (lex_7_144_image s)

theorem lex_7_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.pos 144), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation7 144 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3530) (Sat.Literal.pos 144) (Sat.Literal.pos 33) (lex_7_144_prefix s) (positive_select s 144) (lex_7_144_image s)

theorem lex_7_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.pos 3530)] :=
  (lex_7_144_gate s).prop _ (List.Mem.head _)

theorem lex_7_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.neg 144), (Sat.Literal.pos 33)] :=
  (lex_7_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.pos 144), (Sat.Literal.neg 33)] :=
  (lex_7_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.neg 144), (Sat.Literal.neg 33), (Sat.Literal.pos 3531)] :=
  (lex_7_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3530), (Sat.Literal.pos 144), (Sat.Literal.pos 33), (Sat.Literal.pos 3531)] :=
  (lex_7_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3531) = lexBefore s permutation7 143 := by
  exact (positive_lex_of_descriptor s 3531 permutation7 144 (by rfl)).trans ((lex_skipped s permutation7 143 144 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation7 143) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation7 143 by rw [image7_eq]; rfl))

theorem lex_7_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3532) (Sat.Literal.pos 3531) (Sat.Literal.pos 143) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation7 143 (assignment s)
    (Sat.Literal.pos 3532) (Sat.Literal.pos 3531) (Sat.Literal.pos 143) (Sat.Literal.pos 31) (positive_of_descriptor s 3532 (.lex permutation7 143) (by rfl)) (lex_7_143_prefix s) (positive_select s 143) (lex_7_143_image s)

theorem lex_7_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.pos 143), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation7 143 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3531) (Sat.Literal.pos 143) (Sat.Literal.pos 31) (lex_7_143_prefix s) (positive_select s 143) (lex_7_143_image s)

theorem lex_7_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.pos 3531)] :=
  (lex_7_143_gate s).prop _ (List.Mem.head _)

theorem lex_7_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.neg 143), (Sat.Literal.pos 31)] :=
  (lex_7_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.pos 143), (Sat.Literal.neg 31)] :=
  (lex_7_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.neg 143), (Sat.Literal.neg 31), (Sat.Literal.pos 3532)] :=
  (lex_7_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3531), (Sat.Literal.pos 143), (Sat.Literal.pos 31), (Sat.Literal.pos 3532)] :=
  (lex_7_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3532) = lexBefore s permutation7 142 := by
  exact (positive_lex_of_descriptor s 3532 permutation7 143 (by rfl)).trans ((lex_skipped s permutation7 142 143 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation7 142) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation7 142 by rw [image7_eq]; rfl))

theorem lex_7_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3533) (Sat.Literal.pos 3532) (Sat.Literal.pos 142) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation7 142 (assignment s)
    (Sat.Literal.pos 3533) (Sat.Literal.pos 3532) (Sat.Literal.pos 142) (Sat.Literal.pos 29) (positive_of_descriptor s 3533 (.lex permutation7 142) (by rfl)) (lex_7_142_prefix s) (positive_select s 142) (lex_7_142_image s)

theorem lex_7_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.pos 142), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation7 142 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3532) (Sat.Literal.pos 142) (Sat.Literal.pos 29) (lex_7_142_prefix s) (positive_select s 142) (lex_7_142_image s)

theorem lex_7_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.pos 3532)] :=
  (lex_7_142_gate s).prop _ (List.Mem.head _)

theorem lex_7_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.neg 142), (Sat.Literal.pos 29)] :=
  (lex_7_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.pos 142), (Sat.Literal.neg 29)] :=
  (lex_7_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.neg 142), (Sat.Literal.neg 29), (Sat.Literal.pos 3533)] :=
  (lex_7_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3532), (Sat.Literal.pos 142), (Sat.Literal.pos 29), (Sat.Literal.pos 3533)] :=
  (lex_7_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3533) = lexBefore s permutation7 141 := by
  exact (positive_lex_of_descriptor s 3533 permutation7 142 (by rfl)).trans ((lex_skipped s permutation7 141 142 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation7 141) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation7 141 by rw [image7_eq]; rfl))

theorem lex_7_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3534) (Sat.Literal.pos 3533) (Sat.Literal.pos 141) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation7 141 (assignment s)
    (Sat.Literal.pos 3534) (Sat.Literal.pos 3533) (Sat.Literal.pos 141) (Sat.Literal.pos 27) (positive_of_descriptor s 3534 (.lex permutation7 141) (by rfl)) (lex_7_141_prefix s) (positive_select s 141) (lex_7_141_image s)

theorem lex_7_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.pos 141), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation7 141 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3533) (Sat.Literal.pos 141) (Sat.Literal.pos 27) (lex_7_141_prefix s) (positive_select s 141) (lex_7_141_image s)

theorem lex_7_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.pos 3533)] :=
  (lex_7_141_gate s).prop _ (List.Mem.head _)

theorem lex_7_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.neg 141), (Sat.Literal.pos 27)] :=
  (lex_7_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.pos 141), (Sat.Literal.neg 27)] :=
  (lex_7_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.neg 141), (Sat.Literal.neg 27), (Sat.Literal.pos 3534)] :=
  (lex_7_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3533), (Sat.Literal.pos 141), (Sat.Literal.pos 27), (Sat.Literal.pos 3534)] :=
  (lex_7_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3534) = lexBefore s permutation7 140 := by
  exact (positive_lex_of_descriptor s 3534 permutation7 141 (by rfl)).trans ((lex_skipped s permutation7 140 141 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation7 140) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation7 140 by rw [image7_eq]; rfl))

theorem lex_7_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3535) (Sat.Literal.pos 3534) (Sat.Literal.pos 140) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation7 140 (assignment s)
    (Sat.Literal.pos 3535) (Sat.Literal.pos 3534) (Sat.Literal.pos 140) (Sat.Literal.pos 25) (positive_of_descriptor s 3535 (.lex permutation7 140) (by rfl)) (lex_7_140_prefix s) (positive_select s 140) (lex_7_140_image s)

theorem lex_7_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.pos 140), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation7 140 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3534) (Sat.Literal.pos 140) (Sat.Literal.pos 25) (lex_7_140_prefix s) (positive_select s 140) (lex_7_140_image s)

theorem lex_7_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.pos 3534)] :=
  (lex_7_140_gate s).prop _ (List.Mem.head _)

theorem lex_7_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.neg 140), (Sat.Literal.pos 25)] :=
  (lex_7_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.pos 140), (Sat.Literal.neg 25)] :=
  (lex_7_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.neg 140), (Sat.Literal.neg 25), (Sat.Literal.pos 3535)] :=
  (lex_7_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3534), (Sat.Literal.pos 140), (Sat.Literal.pos 25), (Sat.Literal.pos 3535)] :=
  (lex_7_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3535) = lexBefore s permutation7 139 := by
  exact (positive_lex_of_descriptor s 3535 permutation7 140 (by rfl)).trans ((lex_skipped s permutation7 139 140 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation7 139) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation7 139 by rw [image7_eq]; rfl))

theorem lex_7_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3536) (Sat.Literal.pos 3535) (Sat.Literal.pos 139) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation7 139 (assignment s)
    (Sat.Literal.pos 3536) (Sat.Literal.pos 3535) (Sat.Literal.pos 139) (Sat.Literal.pos 23) (positive_of_descriptor s 3536 (.lex permutation7 139) (by rfl)) (lex_7_139_prefix s) (positive_select s 139) (lex_7_139_image s)

theorem lex_7_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.pos 139), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation7 139 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3535) (Sat.Literal.pos 139) (Sat.Literal.pos 23) (lex_7_139_prefix s) (positive_select s 139) (lex_7_139_image s)

theorem lex_7_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.pos 3535)] :=
  (lex_7_139_gate s).prop _ (List.Mem.head _)

theorem lex_7_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.neg 139), (Sat.Literal.pos 23)] :=
  (lex_7_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.pos 139), (Sat.Literal.neg 23)] :=
  (lex_7_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.neg 139), (Sat.Literal.neg 23), (Sat.Literal.pos 3536)] :=
  (lex_7_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3535), (Sat.Literal.pos 139), (Sat.Literal.pos 23), (Sat.Literal.pos 3536)] :=
  (lex_7_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3536) = lexBefore s permutation7 138 := by
  exact (positive_lex_of_descriptor s 3536 permutation7 139 (by rfl)).trans ((lex_skipped s permutation7 138 139 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation7 138) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation7 138 by rw [image7_eq]; rfl))

theorem lex_7_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3537) (Sat.Literal.pos 3536) (Sat.Literal.pos 138) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation7 138 (assignment s)
    (Sat.Literal.pos 3537) (Sat.Literal.pos 3536) (Sat.Literal.pos 138) (Sat.Literal.pos 21) (positive_of_descriptor s 3537 (.lex permutation7 138) (by rfl)) (lex_7_138_prefix s) (positive_select s 138) (lex_7_138_image s)

theorem lex_7_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.pos 138), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation7 138 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3536) (Sat.Literal.pos 138) (Sat.Literal.pos 21) (lex_7_138_prefix s) (positive_select s 138) (lex_7_138_image s)

theorem lex_7_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.pos 3536)] :=
  (lex_7_138_gate s).prop _ (List.Mem.head _)

theorem lex_7_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.neg 138), (Sat.Literal.pos 21)] :=
  (lex_7_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.pos 138), (Sat.Literal.neg 21)] :=
  (lex_7_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.neg 138), (Sat.Literal.neg 21), (Sat.Literal.pos 3537)] :=
  (lex_7_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3536), (Sat.Literal.pos 138), (Sat.Literal.pos 21), (Sat.Literal.pos 3537)] :=
  (lex_7_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3537) = lexBefore s permutation7 137 := by
  exact (positive_lex_of_descriptor s 3537 permutation7 138 (by rfl)).trans ((lex_skipped s permutation7 137 138 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation7 137) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation7 137 by rw [image7_eq]; rfl))

theorem lex_7_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3538) (Sat.Literal.pos 3537) (Sat.Literal.pos 137) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation7 137 (assignment s)
    (Sat.Literal.pos 3538) (Sat.Literal.pos 3537) (Sat.Literal.pos 137) (Sat.Literal.pos 19) (positive_of_descriptor s 3538 (.lex permutation7 137) (by rfl)) (lex_7_137_prefix s) (positive_select s 137) (lex_7_137_image s)

theorem lex_7_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.pos 137), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation7 137 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3537) (Sat.Literal.pos 137) (Sat.Literal.pos 19) (lex_7_137_prefix s) (positive_select s 137) (lex_7_137_image s)

theorem lex_7_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.pos 3537)] :=
  (lex_7_137_gate s).prop _ (List.Mem.head _)

theorem lex_7_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.neg 137), (Sat.Literal.pos 19)] :=
  (lex_7_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.pos 137), (Sat.Literal.neg 19)] :=
  (lex_7_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.neg 137), (Sat.Literal.neg 19), (Sat.Literal.pos 3538)] :=
  (lex_7_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3537), (Sat.Literal.pos 137), (Sat.Literal.pos 19), (Sat.Literal.pos 3538)] :=
  (lex_7_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3538) = lexBefore s permutation7 136 := by
  exact (positive_lex_of_descriptor s 3538 permutation7 137 (by rfl)).trans ((lex_skipped s permutation7 136 137 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation7 136) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation7 136 by rw [image7_eq]; rfl))

theorem lex_7_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3539) (Sat.Literal.pos 3538) (Sat.Literal.pos 136) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation7 136 (assignment s)
    (Sat.Literal.pos 3539) (Sat.Literal.pos 3538) (Sat.Literal.pos 136) (Sat.Literal.pos 17) (positive_of_descriptor s 3539 (.lex permutation7 136) (by rfl)) (lex_7_136_prefix s) (positive_select s 136) (lex_7_136_image s)

theorem lex_7_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.pos 136), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation7 136 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3538) (Sat.Literal.pos 136) (Sat.Literal.pos 17) (lex_7_136_prefix s) (positive_select s 136) (lex_7_136_image s)

theorem lex_7_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.pos 3538)] :=
  (lex_7_136_gate s).prop _ (List.Mem.head _)

theorem lex_7_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.neg 136), (Sat.Literal.pos 17)] :=
  (lex_7_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.pos 136), (Sat.Literal.neg 17)] :=
  (lex_7_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.neg 136), (Sat.Literal.neg 17), (Sat.Literal.pos 3539)] :=
  (lex_7_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3538), (Sat.Literal.pos 136), (Sat.Literal.pos 17), (Sat.Literal.pos 3539)] :=
  (lex_7_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3539) = lexBefore s permutation7 135 := by
  exact (positive_lex_of_descriptor s 3539 permutation7 136 (by rfl)).trans ((lex_skipped s permutation7 135 136 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation7 135) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation7 135 by rw [image7_eq]; rfl))

theorem lex_7_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3540) (Sat.Literal.pos 3539) (Sat.Literal.pos 135) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation7 135 (assignment s)
    (Sat.Literal.pos 3540) (Sat.Literal.pos 3539) (Sat.Literal.pos 135) (Sat.Literal.pos 15) (positive_of_descriptor s 3540 (.lex permutation7 135) (by rfl)) (lex_7_135_prefix s) (positive_select s 135) (lex_7_135_image s)

theorem lex_7_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.pos 135), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation7 135 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3539) (Sat.Literal.pos 135) (Sat.Literal.pos 15) (lex_7_135_prefix s) (positive_select s 135) (lex_7_135_image s)

theorem lex_7_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.pos 3539)] :=
  (lex_7_135_gate s).prop _ (List.Mem.head _)

theorem lex_7_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.neg 135), (Sat.Literal.pos 15)] :=
  (lex_7_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.pos 135), (Sat.Literal.neg 15)] :=
  (lex_7_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.neg 135), (Sat.Literal.neg 15), (Sat.Literal.pos 3540)] :=
  (lex_7_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3539), (Sat.Literal.pos 135), (Sat.Literal.pos 15), (Sat.Literal.pos 3540)] :=
  (lex_7_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3540) = lexBefore s permutation7 134 := by
  exact (positive_lex_of_descriptor s 3540 permutation7 135 (by rfl)).trans ((lex_skipped s permutation7 134 135 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation7 134) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation7 134 by rw [image7_eq]; rfl))

theorem lex_7_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3541) (Sat.Literal.pos 3540) (Sat.Literal.pos 134) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation7 134 (assignment s)
    (Sat.Literal.pos 3541) (Sat.Literal.pos 3540) (Sat.Literal.pos 134) (Sat.Literal.pos 13) (positive_of_descriptor s 3541 (.lex permutation7 134) (by rfl)) (lex_7_134_prefix s) (positive_select s 134) (lex_7_134_image s)

theorem lex_7_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.pos 134), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation7 134 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3540) (Sat.Literal.pos 134) (Sat.Literal.pos 13) (lex_7_134_prefix s) (positive_select s 134) (lex_7_134_image s)

theorem lex_7_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.pos 3540)] :=
  (lex_7_134_gate s).prop _ (List.Mem.head _)

theorem lex_7_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.neg 134), (Sat.Literal.pos 13)] :=
  (lex_7_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.pos 134), (Sat.Literal.neg 13)] :=
  (lex_7_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.neg 134), (Sat.Literal.neg 13), (Sat.Literal.pos 3541)] :=
  (lex_7_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3540), (Sat.Literal.pos 134), (Sat.Literal.pos 13), (Sat.Literal.pos 3541)] :=
  (lex_7_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3541) = lexBefore s permutation7 133 := by
  exact (positive_lex_of_descriptor s 3541 permutation7 134 (by rfl)).trans ((lex_skipped s permutation7 133 134 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation7 133) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation7 133 by rw [image7_eq]; rfl))

theorem lex_7_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3542) (Sat.Literal.pos 3541) (Sat.Literal.pos 133) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation7 133 (assignment s)
    (Sat.Literal.pos 3542) (Sat.Literal.pos 3541) (Sat.Literal.pos 133) (Sat.Literal.pos 11) (positive_of_descriptor s 3542 (.lex permutation7 133) (by rfl)) (lex_7_133_prefix s) (positive_select s 133) (lex_7_133_image s)

theorem lex_7_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.pos 133), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation7 133 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3541) (Sat.Literal.pos 133) (Sat.Literal.pos 11) (lex_7_133_prefix s) (positive_select s 133) (lex_7_133_image s)

theorem lex_7_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.pos 3541)] :=
  (lex_7_133_gate s).prop _ (List.Mem.head _)

theorem lex_7_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.neg 133), (Sat.Literal.pos 11)] :=
  (lex_7_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.pos 133), (Sat.Literal.neg 11)] :=
  (lex_7_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.neg 133), (Sat.Literal.neg 11), (Sat.Literal.pos 3542)] :=
  (lex_7_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3541), (Sat.Literal.pos 133), (Sat.Literal.pos 11), (Sat.Literal.pos 3542)] :=
  (lex_7_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3542) = lexBefore s permutation7 132 := by
  exact (positive_lex_of_descriptor s 3542 permutation7 133 (by rfl)).trans ((lex_skipped s permutation7 132 133 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation7 132) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation7 132 by rw [image7_eq]; rfl))

theorem lex_7_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3543) (Sat.Literal.pos 3542) (Sat.Literal.pos 132) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation7 132 (assignment s)
    (Sat.Literal.pos 3543) (Sat.Literal.pos 3542) (Sat.Literal.pos 132) (Sat.Literal.pos 9) (positive_of_descriptor s 3543 (.lex permutation7 132) (by rfl)) (lex_7_132_prefix s) (positive_select s 132) (lex_7_132_image s)

theorem lex_7_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.pos 132), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation7 132 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3542) (Sat.Literal.pos 132) (Sat.Literal.pos 9) (lex_7_132_prefix s) (positive_select s 132) (lex_7_132_image s)

theorem lex_7_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.pos 3542)] :=
  (lex_7_132_gate s).prop _ (List.Mem.head _)

theorem lex_7_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.neg 132), (Sat.Literal.pos 9)] :=
  (lex_7_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.pos 132), (Sat.Literal.neg 9)] :=
  (lex_7_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.neg 132), (Sat.Literal.neg 9), (Sat.Literal.pos 3543)] :=
  (lex_7_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3542), (Sat.Literal.pos 132), (Sat.Literal.pos 9), (Sat.Literal.pos 3543)] :=
  (lex_7_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3543) = lexBefore s permutation7 131 := by
  exact (positive_lex_of_descriptor s 3543 permutation7 132 (by rfl)).trans ((lex_skipped s permutation7 131 132 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation7 131) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation7 131 by rw [image7_eq]; rfl))

theorem lex_7_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3544) (Sat.Literal.pos 3543) (Sat.Literal.pos 131) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation7 131 (assignment s)
    (Sat.Literal.pos 3544) (Sat.Literal.pos 3543) (Sat.Literal.pos 131) (Sat.Literal.pos 7) (positive_of_descriptor s 3544 (.lex permutation7 131) (by rfl)) (lex_7_131_prefix s) (positive_select s 131) (lex_7_131_image s)

theorem lex_7_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.pos 131), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation7 131 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3543) (Sat.Literal.pos 131) (Sat.Literal.pos 7) (lex_7_131_prefix s) (positive_select s 131) (lex_7_131_image s)

theorem lex_7_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.pos 3543)] :=
  (lex_7_131_gate s).prop _ (List.Mem.head _)

theorem lex_7_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.neg 131), (Sat.Literal.pos 7)] :=
  (lex_7_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.pos 131), (Sat.Literal.neg 7)] :=
  (lex_7_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.neg 131), (Sat.Literal.neg 7), (Sat.Literal.pos 3544)] :=
  (lex_7_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3543), (Sat.Literal.pos 131), (Sat.Literal.pos 7), (Sat.Literal.pos 3544)] :=
  (lex_7_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3544) = lexBefore s permutation7 130 := by
  exact (positive_lex_of_descriptor s 3544 permutation7 131 (by rfl)).trans ((lex_skipped s permutation7 130 131 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation7 130) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation7 130 by rw [image7_eq]; rfl))

theorem lex_7_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3545) (Sat.Literal.pos 3544) (Sat.Literal.pos 130) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation7 130 (assignment s)
    (Sat.Literal.pos 3545) (Sat.Literal.pos 3544) (Sat.Literal.pos 130) (Sat.Literal.pos 5) (positive_of_descriptor s 3545 (.lex permutation7 130) (by rfl)) (lex_7_130_prefix s) (positive_select s 130) (lex_7_130_image s)

theorem lex_7_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.pos 130), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation7 130 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3544) (Sat.Literal.pos 130) (Sat.Literal.pos 5) (lex_7_130_prefix s) (positive_select s 130) (lex_7_130_image s)

theorem lex_7_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.pos 3544)] :=
  (lex_7_130_gate s).prop _ (List.Mem.head _)

theorem lex_7_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.neg 130), (Sat.Literal.pos 5)] :=
  (lex_7_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.pos 130), (Sat.Literal.neg 5)] :=
  (lex_7_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.neg 130), (Sat.Literal.neg 5), (Sat.Literal.pos 3545)] :=
  (lex_7_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3544), (Sat.Literal.pos 130), (Sat.Literal.pos 5), (Sat.Literal.pos 3545)] :=
  (lex_7_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3545) = lexBefore s permutation7 129 := by
  exact (positive_lex_of_descriptor s 3545 permutation7 130 (by rfl)).trans ((lex_skipped s permutation7 129 130 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation7 129) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation7 129 by rw [image7_eq]; rfl))

theorem lex_7_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3546) (Sat.Literal.pos 3545) (Sat.Literal.pos 129) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation7 129 (assignment s)
    (Sat.Literal.pos 3546) (Sat.Literal.pos 3545) (Sat.Literal.pos 129) (Sat.Literal.pos 3) (positive_of_descriptor s 3546 (.lex permutation7 129) (by rfl)) (lex_7_129_prefix s) (positive_select s 129) (lex_7_129_image s)

theorem lex_7_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.pos 129), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation7 129 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3545) (Sat.Literal.pos 129) (Sat.Literal.pos 3) (lex_7_129_prefix s) (positive_select s 129) (lex_7_129_image s)

theorem lex_7_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.pos 3545)] :=
  (lex_7_129_gate s).prop _ (List.Mem.head _)

theorem lex_7_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.neg 129), (Sat.Literal.pos 3)] :=
  (lex_7_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.pos 129), (Sat.Literal.neg 3)] :=
  (lex_7_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.neg 129), (Sat.Literal.neg 3), (Sat.Literal.pos 3546)] :=
  (lex_7_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3545), (Sat.Literal.pos 129), (Sat.Literal.pos 3), (Sat.Literal.pos 3546)] :=
  (lex_7_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3546) = lexBefore s permutation7 128 := by
  exact (positive_lex_of_descriptor s 3546 permutation7 129 (by rfl)).trans ((lex_skipped s permutation7 128 129 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation7 128) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation7 128 by rw [image7_eq]; rfl))

theorem lex_7_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3547) (Sat.Literal.pos 3546) (Sat.Literal.pos 128) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation7 128 (assignment s)
    (Sat.Literal.pos 3547) (Sat.Literal.pos 3546) (Sat.Literal.pos 128) (Sat.Literal.pos 1) (positive_of_descriptor s 3547 (.lex permutation7 128) (by rfl)) (lex_7_128_prefix s) (positive_select s 128) (lex_7_128_image s)

theorem lex_7_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.pos 128), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation7 128 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3546) (Sat.Literal.pos 128) (Sat.Literal.pos 1) (lex_7_128_prefix s) (positive_select s 128) (lex_7_128_image s)

theorem lex_7_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.pos 3546)] :=
  (lex_7_128_gate s).prop _ (List.Mem.head _)

theorem lex_7_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.neg 128), (Sat.Literal.pos 1)] :=
  (lex_7_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.pos 128), (Sat.Literal.neg 1)] :=
  (lex_7_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.neg 128), (Sat.Literal.neg 1), (Sat.Literal.pos 3547)] :=
  (lex_7_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3546), (Sat.Literal.pos 128), (Sat.Literal.pos 1), (Sat.Literal.pos 3547)] :=
  (lex_7_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3547) = lexBefore s permutation7 127 := by
  exact (positive_lex_of_descriptor s 3547 permutation7 128 (by rfl)).trans ((lex_skipped s permutation7 127 128 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation7 127) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation7 127 by rw [image7_eq]; rfl))

theorem lex_7_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3548) (Sat.Literal.pos 3547) (Sat.Literal.pos 127) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation7 127 (assignment s)
    (Sat.Literal.pos 3548) (Sat.Literal.pos 3547) (Sat.Literal.pos 127) (Sat.Literal.pos 254) (positive_of_descriptor s 3548 (.lex permutation7 127) (by rfl)) (lex_7_127_prefix s) (positive_select s 127) (lex_7_127_image s)

theorem lex_7_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.pos 127), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation7 127 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3547) (Sat.Literal.pos 127) (Sat.Literal.pos 254) (lex_7_127_prefix s) (positive_select s 127) (lex_7_127_image s)

theorem lex_7_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.pos 3547)] :=
  (lex_7_127_gate s).prop _ (List.Mem.head _)

theorem lex_7_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.neg 127), (Sat.Literal.pos 254)] :=
  (lex_7_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.pos 127), (Sat.Literal.neg 254)] :=
  (lex_7_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.neg 127), (Sat.Literal.neg 254), (Sat.Literal.pos 3548)] :=
  (lex_7_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3547), (Sat.Literal.pos 127), (Sat.Literal.pos 254), (Sat.Literal.pos 3548)] :=
  (lex_7_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3548) = lexBefore s permutation7 126 := by
  exact (positive_lex_of_descriptor s 3548 permutation7 127 (by rfl)).trans ((lex_skipped s permutation7 126 127 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation7 126) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation7 126 by rw [image7_eq]; rfl))

theorem lex_7_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3549) (Sat.Literal.pos 3548) (Sat.Literal.pos 126) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation7 126 (assignment s)
    (Sat.Literal.pos 3549) (Sat.Literal.pos 3548) (Sat.Literal.pos 126) (Sat.Literal.pos 252) (positive_of_descriptor s 3549 (.lex permutation7 126) (by rfl)) (lex_7_126_prefix s) (positive_select s 126) (lex_7_126_image s)

theorem lex_7_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.pos 126), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation7 126 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3548) (Sat.Literal.pos 126) (Sat.Literal.pos 252) (lex_7_126_prefix s) (positive_select s 126) (lex_7_126_image s)

theorem lex_7_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.pos 3548)] :=
  (lex_7_126_gate s).prop _ (List.Mem.head _)

theorem lex_7_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.neg 126), (Sat.Literal.pos 252)] :=
  (lex_7_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.pos 126), (Sat.Literal.neg 252)] :=
  (lex_7_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.neg 126), (Sat.Literal.neg 252), (Sat.Literal.pos 3549)] :=
  (lex_7_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3548), (Sat.Literal.pos 126), (Sat.Literal.pos 252), (Sat.Literal.pos 3549)] :=
  (lex_7_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3549) = lexBefore s permutation7 125 := by
  exact (positive_lex_of_descriptor s 3549 permutation7 126 (by rfl)).trans ((lex_skipped s permutation7 125 126 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation7 125) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation7 125 by rw [image7_eq]; rfl))

theorem lex_7_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3550) (Sat.Literal.pos 3549) (Sat.Literal.pos 125) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation7 125 (assignment s)
    (Sat.Literal.pos 3550) (Sat.Literal.pos 3549) (Sat.Literal.pos 125) (Sat.Literal.pos 250) (positive_of_descriptor s 3550 (.lex permutation7 125) (by rfl)) (lex_7_125_prefix s) (positive_select s 125) (lex_7_125_image s)

theorem lex_7_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.pos 125), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation7 125 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3549) (Sat.Literal.pos 125) (Sat.Literal.pos 250) (lex_7_125_prefix s) (positive_select s 125) (lex_7_125_image s)

theorem lex_7_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.pos 3549)] :=
  (lex_7_125_gate s).prop _ (List.Mem.head _)

theorem lex_7_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.neg 125), (Sat.Literal.pos 250)] :=
  (lex_7_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.pos 125), (Sat.Literal.neg 250)] :=
  (lex_7_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.neg 125), (Sat.Literal.neg 250), (Sat.Literal.pos 3550)] :=
  (lex_7_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3549), (Sat.Literal.pos 125), (Sat.Literal.pos 250), (Sat.Literal.pos 3550)] :=
  (lex_7_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3550) = lexBefore s permutation7 124 := by
  exact (positive_lex_of_descriptor s 3550 permutation7 125 (by rfl)).trans ((lex_skipped s permutation7 124 125 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation7 124) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation7 124 by rw [image7_eq]; rfl))

theorem lex_7_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3551) (Sat.Literal.pos 3550) (Sat.Literal.pos 124) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation7 124 (assignment s)
    (Sat.Literal.pos 3551) (Sat.Literal.pos 3550) (Sat.Literal.pos 124) (Sat.Literal.pos 248) (positive_of_descriptor s 3551 (.lex permutation7 124) (by rfl)) (lex_7_124_prefix s) (positive_select s 124) (lex_7_124_image s)

theorem lex_7_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.pos 124), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation7 124 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3550) (Sat.Literal.pos 124) (Sat.Literal.pos 248) (lex_7_124_prefix s) (positive_select s 124) (lex_7_124_image s)

theorem lex_7_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.pos 3550)] :=
  (lex_7_124_gate s).prop _ (List.Mem.head _)

theorem lex_7_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.neg 124), (Sat.Literal.pos 248)] :=
  (lex_7_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.pos 124), (Sat.Literal.neg 248)] :=
  (lex_7_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.neg 124), (Sat.Literal.neg 248), (Sat.Literal.pos 3551)] :=
  (lex_7_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3550), (Sat.Literal.pos 124), (Sat.Literal.pos 248), (Sat.Literal.pos 3551)] :=
  (lex_7_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3551) = lexBefore s permutation7 123 := by
  exact (positive_lex_of_descriptor s 3551 permutation7 124 (by rfl)).trans ((lex_skipped s permutation7 123 124 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation7 123) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation7 123 by rw [image7_eq]; rfl))

theorem lex_7_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3552) (Sat.Literal.pos 3551) (Sat.Literal.pos 123) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation7 123 (assignment s)
    (Sat.Literal.pos 3552) (Sat.Literal.pos 3551) (Sat.Literal.pos 123) (Sat.Literal.pos 246) (positive_of_descriptor s 3552 (.lex permutation7 123) (by rfl)) (lex_7_123_prefix s) (positive_select s 123) (lex_7_123_image s)

theorem lex_7_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.pos 123), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation7 123 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3551) (Sat.Literal.pos 123) (Sat.Literal.pos 246) (lex_7_123_prefix s) (positive_select s 123) (lex_7_123_image s)

theorem lex_7_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.pos 3551)] :=
  (lex_7_123_gate s).prop _ (List.Mem.head _)

theorem lex_7_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.neg 123), (Sat.Literal.pos 246)] :=
  (lex_7_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.pos 123), (Sat.Literal.neg 246)] :=
  (lex_7_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.neg 123), (Sat.Literal.neg 246), (Sat.Literal.pos 3552)] :=
  (lex_7_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3551), (Sat.Literal.pos 123), (Sat.Literal.pos 246), (Sat.Literal.pos 3552)] :=
  (lex_7_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3552) = lexBefore s permutation7 122 := by
  exact (positive_lex_of_descriptor s 3552 permutation7 123 (by rfl)).trans ((lex_skipped s permutation7 122 123 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation7 122) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation7 122 by rw [image7_eq]; rfl))

theorem lex_7_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3553) (Sat.Literal.pos 3552) (Sat.Literal.pos 122) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation7 122 (assignment s)
    (Sat.Literal.pos 3553) (Sat.Literal.pos 3552) (Sat.Literal.pos 122) (Sat.Literal.pos 244) (positive_of_descriptor s 3553 (.lex permutation7 122) (by rfl)) (lex_7_122_prefix s) (positive_select s 122) (lex_7_122_image s)

theorem lex_7_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.pos 122), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation7 122 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3552) (Sat.Literal.pos 122) (Sat.Literal.pos 244) (lex_7_122_prefix s) (positive_select s 122) (lex_7_122_image s)

theorem lex_7_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.pos 3552)] :=
  (lex_7_122_gate s).prop _ (List.Mem.head _)

theorem lex_7_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.neg 122), (Sat.Literal.pos 244)] :=
  (lex_7_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.pos 122), (Sat.Literal.neg 244)] :=
  (lex_7_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.neg 122), (Sat.Literal.neg 244), (Sat.Literal.pos 3553)] :=
  (lex_7_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3552), (Sat.Literal.pos 122), (Sat.Literal.pos 244), (Sat.Literal.pos 3553)] :=
  (lex_7_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3553) = lexBefore s permutation7 121 := by
  exact (positive_lex_of_descriptor s 3553 permutation7 122 (by rfl)).trans ((lex_skipped s permutation7 121 122 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation7 121) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation7 121 by rw [image7_eq]; rfl))

theorem lex_7_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3554) (Sat.Literal.pos 3553) (Sat.Literal.pos 121) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation7 121 (assignment s)
    (Sat.Literal.pos 3554) (Sat.Literal.pos 3553) (Sat.Literal.pos 121) (Sat.Literal.pos 242) (positive_of_descriptor s 3554 (.lex permutation7 121) (by rfl)) (lex_7_121_prefix s) (positive_select s 121) (lex_7_121_image s)

theorem lex_7_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.pos 121), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation7 121 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3553) (Sat.Literal.pos 121) (Sat.Literal.pos 242) (lex_7_121_prefix s) (positive_select s 121) (lex_7_121_image s)

theorem lex_7_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.pos 3553)] :=
  (lex_7_121_gate s).prop _ (List.Mem.head _)

theorem lex_7_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.neg 121), (Sat.Literal.pos 242)] :=
  (lex_7_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.pos 121), (Sat.Literal.neg 242)] :=
  (lex_7_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.neg 121), (Sat.Literal.neg 242), (Sat.Literal.pos 3554)] :=
  (lex_7_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3553), (Sat.Literal.pos 121), (Sat.Literal.pos 242), (Sat.Literal.pos 3554)] :=
  (lex_7_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3554) = lexBefore s permutation7 120 := by
  exact (positive_lex_of_descriptor s 3554 permutation7 121 (by rfl)).trans ((lex_skipped s permutation7 120 121 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation7 120) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation7 120 by rw [image7_eq]; rfl))

theorem lex_7_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3555) (Sat.Literal.pos 3554) (Sat.Literal.pos 120) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation7 120 (assignment s)
    (Sat.Literal.pos 3555) (Sat.Literal.pos 3554) (Sat.Literal.pos 120) (Sat.Literal.pos 240) (positive_of_descriptor s 3555 (.lex permutation7 120) (by rfl)) (lex_7_120_prefix s) (positive_select s 120) (lex_7_120_image s)

theorem lex_7_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.pos 120), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation7 120 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3554) (Sat.Literal.pos 120) (Sat.Literal.pos 240) (lex_7_120_prefix s) (positive_select s 120) (lex_7_120_image s)

theorem lex_7_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.pos 3554)] :=
  (lex_7_120_gate s).prop _ (List.Mem.head _)

theorem lex_7_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.neg 120), (Sat.Literal.pos 240)] :=
  (lex_7_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.pos 120), (Sat.Literal.neg 240)] :=
  (lex_7_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.neg 120), (Sat.Literal.neg 240), (Sat.Literal.pos 3555)] :=
  (lex_7_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3554), (Sat.Literal.pos 120), (Sat.Literal.pos 240), (Sat.Literal.pos 3555)] :=
  (lex_7_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3555) = lexBefore s permutation7 119 := by
  exact (positive_lex_of_descriptor s 3555 permutation7 120 (by rfl)).trans ((lex_skipped s permutation7 119 120 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation7 119) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation7 119 by rw [image7_eq]; rfl))

theorem lex_7_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3556) (Sat.Literal.pos 3555) (Sat.Literal.pos 119) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation7 119 (assignment s)
    (Sat.Literal.pos 3556) (Sat.Literal.pos 3555) (Sat.Literal.pos 119) (Sat.Literal.pos 238) (positive_of_descriptor s 3556 (.lex permutation7 119) (by rfl)) (lex_7_119_prefix s) (positive_select s 119) (lex_7_119_image s)

theorem lex_7_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.pos 119), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation7 119 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3555) (Sat.Literal.pos 119) (Sat.Literal.pos 238) (lex_7_119_prefix s) (positive_select s 119) (lex_7_119_image s)

theorem lex_7_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.pos 3555)] :=
  (lex_7_119_gate s).prop _ (List.Mem.head _)

theorem lex_7_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.neg 119), (Sat.Literal.pos 238)] :=
  (lex_7_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.pos 119), (Sat.Literal.neg 238)] :=
  (lex_7_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.neg 119), (Sat.Literal.neg 238), (Sat.Literal.pos 3556)] :=
  (lex_7_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3555), (Sat.Literal.pos 119), (Sat.Literal.pos 238), (Sat.Literal.pos 3556)] :=
  (lex_7_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3556) = lexBefore s permutation7 118 := by
  exact (positive_lex_of_descriptor s 3556 permutation7 119 (by rfl)).trans ((lex_skipped s permutation7 118 119 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation7 118) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation7 118 by rw [image7_eq]; rfl))

theorem lex_7_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3557) (Sat.Literal.pos 3556) (Sat.Literal.pos 118) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation7 118 (assignment s)
    (Sat.Literal.pos 3557) (Sat.Literal.pos 3556) (Sat.Literal.pos 118) (Sat.Literal.pos 236) (positive_of_descriptor s 3557 (.lex permutation7 118) (by rfl)) (lex_7_118_prefix s) (positive_select s 118) (lex_7_118_image s)

theorem lex_7_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.pos 118), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation7 118 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3556) (Sat.Literal.pos 118) (Sat.Literal.pos 236) (lex_7_118_prefix s) (positive_select s 118) (lex_7_118_image s)

theorem lex_7_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.pos 3556)] :=
  (lex_7_118_gate s).prop _ (List.Mem.head _)

theorem lex_7_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.neg 118), (Sat.Literal.pos 236)] :=
  (lex_7_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.pos 118), (Sat.Literal.neg 236)] :=
  (lex_7_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.neg 118), (Sat.Literal.neg 236), (Sat.Literal.pos 3557)] :=
  (lex_7_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3556), (Sat.Literal.pos 118), (Sat.Literal.pos 236), (Sat.Literal.pos 3557)] :=
  (lex_7_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3557) = lexBefore s permutation7 117 := by
  exact (positive_lex_of_descriptor s 3557 permutation7 118 (by rfl)).trans ((lex_skipped s permutation7 117 118 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation7 117) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation7 117 by rw [image7_eq]; rfl))

theorem lex_7_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3558) (Sat.Literal.pos 3557) (Sat.Literal.pos 117) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation7 117 (assignment s)
    (Sat.Literal.pos 3558) (Sat.Literal.pos 3557) (Sat.Literal.pos 117) (Sat.Literal.pos 234) (positive_of_descriptor s 3558 (.lex permutation7 117) (by rfl)) (lex_7_117_prefix s) (positive_select s 117) (lex_7_117_image s)

theorem lex_7_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.pos 117), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation7 117 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3557) (Sat.Literal.pos 117) (Sat.Literal.pos 234) (lex_7_117_prefix s) (positive_select s 117) (lex_7_117_image s)

theorem lex_7_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.pos 3557)] :=
  (lex_7_117_gate s).prop _ (List.Mem.head _)

theorem lex_7_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.neg 117), (Sat.Literal.pos 234)] :=
  (lex_7_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.pos 117), (Sat.Literal.neg 234)] :=
  (lex_7_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.neg 117), (Sat.Literal.neg 234), (Sat.Literal.pos 3558)] :=
  (lex_7_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3557), (Sat.Literal.pos 117), (Sat.Literal.pos 234), (Sat.Literal.pos 3558)] :=
  (lex_7_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3558) = lexBefore s permutation7 116 := by
  exact (positive_lex_of_descriptor s 3558 permutation7 117 (by rfl)).trans ((lex_skipped s permutation7 116 117 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation7 116) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation7 116 by rw [image7_eq]; rfl))

theorem lex_7_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3559) (Sat.Literal.pos 3558) (Sat.Literal.pos 116) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation7 116 (assignment s)
    (Sat.Literal.pos 3559) (Sat.Literal.pos 3558) (Sat.Literal.pos 116) (Sat.Literal.pos 232) (positive_of_descriptor s 3559 (.lex permutation7 116) (by rfl)) (lex_7_116_prefix s) (positive_select s 116) (lex_7_116_image s)

theorem lex_7_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.pos 116), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation7 116 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3558) (Sat.Literal.pos 116) (Sat.Literal.pos 232) (lex_7_116_prefix s) (positive_select s 116) (lex_7_116_image s)

theorem lex_7_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.pos 3558)] :=
  (lex_7_116_gate s).prop _ (List.Mem.head _)

theorem lex_7_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.neg 116), (Sat.Literal.pos 232)] :=
  (lex_7_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.pos 116), (Sat.Literal.neg 232)] :=
  (lex_7_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.neg 116), (Sat.Literal.neg 232), (Sat.Literal.pos 3559)] :=
  (lex_7_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3558), (Sat.Literal.pos 116), (Sat.Literal.pos 232), (Sat.Literal.pos 3559)] :=
  (lex_7_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3559) = lexBefore s permutation7 115 := by
  exact (positive_lex_of_descriptor s 3559 permutation7 116 (by rfl)).trans ((lex_skipped s permutation7 115 116 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation7 115) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation7 115 by rw [image7_eq]; rfl))

theorem lex_7_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3560) (Sat.Literal.pos 3559) (Sat.Literal.pos 115) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation7 115 (assignment s)
    (Sat.Literal.pos 3560) (Sat.Literal.pos 3559) (Sat.Literal.pos 115) (Sat.Literal.pos 230) (positive_of_descriptor s 3560 (.lex permutation7 115) (by rfl)) (lex_7_115_prefix s) (positive_select s 115) (lex_7_115_image s)

theorem lex_7_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.pos 115), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation7 115 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3559) (Sat.Literal.pos 115) (Sat.Literal.pos 230) (lex_7_115_prefix s) (positive_select s 115) (lex_7_115_image s)

theorem lex_7_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.pos 3559)] :=
  (lex_7_115_gate s).prop _ (List.Mem.head _)

theorem lex_7_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.neg 115), (Sat.Literal.pos 230)] :=
  (lex_7_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.pos 115), (Sat.Literal.neg 230)] :=
  (lex_7_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.neg 115), (Sat.Literal.neg 230), (Sat.Literal.pos 3560)] :=
  (lex_7_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3559), (Sat.Literal.pos 115), (Sat.Literal.pos 230), (Sat.Literal.pos 3560)] :=
  (lex_7_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3560) = lexBefore s permutation7 114 := by
  exact (positive_lex_of_descriptor s 3560 permutation7 115 (by rfl)).trans ((lex_skipped s permutation7 114 115 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation7 114) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation7 114 by rw [image7_eq]; rfl))

theorem lex_7_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3561) (Sat.Literal.pos 3560) (Sat.Literal.pos 114) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation7 114 (assignment s)
    (Sat.Literal.pos 3561) (Sat.Literal.pos 3560) (Sat.Literal.pos 114) (Sat.Literal.pos 228) (positive_of_descriptor s 3561 (.lex permutation7 114) (by rfl)) (lex_7_114_prefix s) (positive_select s 114) (lex_7_114_image s)

theorem lex_7_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.pos 114), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation7 114 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3560) (Sat.Literal.pos 114) (Sat.Literal.pos 228) (lex_7_114_prefix s) (positive_select s 114) (lex_7_114_image s)

theorem lex_7_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.pos 3560)] :=
  (lex_7_114_gate s).prop _ (List.Mem.head _)

theorem lex_7_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.neg 114), (Sat.Literal.pos 228)] :=
  (lex_7_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.pos 114), (Sat.Literal.neg 228)] :=
  (lex_7_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.neg 114), (Sat.Literal.neg 228), (Sat.Literal.pos 3561)] :=
  (lex_7_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3560), (Sat.Literal.pos 114), (Sat.Literal.pos 228), (Sat.Literal.pos 3561)] :=
  (lex_7_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3561) = lexBefore s permutation7 113 := by
  exact (positive_lex_of_descriptor s 3561 permutation7 114 (by rfl)).trans ((lex_skipped s permutation7 113 114 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation7 113) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation7 113 by rw [image7_eq]; rfl))

theorem lex_7_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3562) (Sat.Literal.pos 3561) (Sat.Literal.pos 113) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation7 113 (assignment s)
    (Sat.Literal.pos 3562) (Sat.Literal.pos 3561) (Sat.Literal.pos 113) (Sat.Literal.pos 226) (positive_of_descriptor s 3562 (.lex permutation7 113) (by rfl)) (lex_7_113_prefix s) (positive_select s 113) (lex_7_113_image s)

theorem lex_7_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.pos 113), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation7 113 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3561) (Sat.Literal.pos 113) (Sat.Literal.pos 226) (lex_7_113_prefix s) (positive_select s 113) (lex_7_113_image s)

theorem lex_7_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.pos 3561)] :=
  (lex_7_113_gate s).prop _ (List.Mem.head _)

theorem lex_7_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.neg 113), (Sat.Literal.pos 226)] :=
  (lex_7_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.pos 113), (Sat.Literal.neg 226)] :=
  (lex_7_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.neg 113), (Sat.Literal.neg 226), (Sat.Literal.pos 3562)] :=
  (lex_7_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3561), (Sat.Literal.pos 113), (Sat.Literal.pos 226), (Sat.Literal.pos 3562)] :=
  (lex_7_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3562) = lexBefore s permutation7 112 := by
  exact (positive_lex_of_descriptor s 3562 permutation7 113 (by rfl)).trans ((lex_skipped s permutation7 112 113 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation7 112) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation7 112 by rw [image7_eq]; rfl))

theorem lex_7_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3563) (Sat.Literal.pos 3562) (Sat.Literal.pos 112) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation7 112 (assignment s)
    (Sat.Literal.pos 3563) (Sat.Literal.pos 3562) (Sat.Literal.pos 112) (Sat.Literal.pos 224) (positive_of_descriptor s 3563 (.lex permutation7 112) (by rfl)) (lex_7_112_prefix s) (positive_select s 112) (lex_7_112_image s)

theorem lex_7_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.pos 112), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation7 112 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3562) (Sat.Literal.pos 112) (Sat.Literal.pos 224) (lex_7_112_prefix s) (positive_select s 112) (lex_7_112_image s)

theorem lex_7_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.pos 3562)] :=
  (lex_7_112_gate s).prop _ (List.Mem.head _)

theorem lex_7_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.neg 112), (Sat.Literal.pos 224)] :=
  (lex_7_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.pos 112), (Sat.Literal.neg 224)] :=
  (lex_7_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.neg 112), (Sat.Literal.neg 224), (Sat.Literal.pos 3563)] :=
  (lex_7_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3562), (Sat.Literal.pos 112), (Sat.Literal.pos 224), (Sat.Literal.pos 3563)] :=
  (lex_7_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3563) = lexBefore s permutation7 111 := by
  exact (positive_lex_of_descriptor s 3563 permutation7 112 (by rfl)).trans ((lex_skipped s permutation7 111 112 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation7 111) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation7 111 by rw [image7_eq]; rfl))

theorem lex_7_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3564) (Sat.Literal.pos 3563) (Sat.Literal.pos 111) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation7 111 (assignment s)
    (Sat.Literal.pos 3564) (Sat.Literal.pos 3563) (Sat.Literal.pos 111) (Sat.Literal.pos 222) (positive_of_descriptor s 3564 (.lex permutation7 111) (by rfl)) (lex_7_111_prefix s) (positive_select s 111) (lex_7_111_image s)

theorem lex_7_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.pos 111), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation7 111 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3563) (Sat.Literal.pos 111) (Sat.Literal.pos 222) (lex_7_111_prefix s) (positive_select s 111) (lex_7_111_image s)

theorem lex_7_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.pos 3563)] :=
  (lex_7_111_gate s).prop _ (List.Mem.head _)

theorem lex_7_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.neg 111), (Sat.Literal.pos 222)] :=
  (lex_7_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.pos 111), (Sat.Literal.neg 222)] :=
  (lex_7_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.neg 111), (Sat.Literal.neg 222), (Sat.Literal.pos 3564)] :=
  (lex_7_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3563), (Sat.Literal.pos 111), (Sat.Literal.pos 222), (Sat.Literal.pos 3564)] :=
  (lex_7_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3564) = lexBefore s permutation7 110 := by
  exact (positive_lex_of_descriptor s 3564 permutation7 111 (by rfl)).trans ((lex_skipped s permutation7 110 111 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation7 110) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation7 110 by rw [image7_eq]; rfl))

theorem lex_7_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3565) (Sat.Literal.pos 3564) (Sat.Literal.pos 110) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation7 110 (assignment s)
    (Sat.Literal.pos 3565) (Sat.Literal.pos 3564) (Sat.Literal.pos 110) (Sat.Literal.pos 220) (positive_of_descriptor s 3565 (.lex permutation7 110) (by rfl)) (lex_7_110_prefix s) (positive_select s 110) (lex_7_110_image s)

theorem lex_7_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.pos 110), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation7 110 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3564) (Sat.Literal.pos 110) (Sat.Literal.pos 220) (lex_7_110_prefix s) (positive_select s 110) (lex_7_110_image s)

theorem lex_7_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.pos 3564)] :=
  (lex_7_110_gate s).prop _ (List.Mem.head _)

theorem lex_7_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.neg 110), (Sat.Literal.pos 220)] :=
  (lex_7_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.pos 110), (Sat.Literal.neg 220)] :=
  (lex_7_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.neg 110), (Sat.Literal.neg 220), (Sat.Literal.pos 3565)] :=
  (lex_7_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3564), (Sat.Literal.pos 110), (Sat.Literal.pos 220), (Sat.Literal.pos 3565)] :=
  (lex_7_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3565) = lexBefore s permutation7 109 := by
  exact (positive_lex_of_descriptor s 3565 permutation7 110 (by rfl)).trans ((lex_skipped s permutation7 109 110 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation7 109) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation7 109 by rw [image7_eq]; rfl))

theorem lex_7_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3566) (Sat.Literal.pos 3565) (Sat.Literal.pos 109) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation7 109 (assignment s)
    (Sat.Literal.pos 3566) (Sat.Literal.pos 3565) (Sat.Literal.pos 109) (Sat.Literal.pos 218) (positive_of_descriptor s 3566 (.lex permutation7 109) (by rfl)) (lex_7_109_prefix s) (positive_select s 109) (lex_7_109_image s)

theorem lex_7_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.pos 109), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation7 109 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3565) (Sat.Literal.pos 109) (Sat.Literal.pos 218) (lex_7_109_prefix s) (positive_select s 109) (lex_7_109_image s)

theorem lex_7_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.pos 3565)] :=
  (lex_7_109_gate s).prop _ (List.Mem.head _)

theorem lex_7_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.neg 109), (Sat.Literal.pos 218)] :=
  (lex_7_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.pos 109), (Sat.Literal.neg 218)] :=
  (lex_7_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.neg 109), (Sat.Literal.neg 218), (Sat.Literal.pos 3566)] :=
  (lex_7_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3565), (Sat.Literal.pos 109), (Sat.Literal.pos 218), (Sat.Literal.pos 3566)] :=
  (lex_7_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3566) = lexBefore s permutation7 108 := by
  exact (positive_lex_of_descriptor s 3566 permutation7 109 (by rfl)).trans ((lex_skipped s permutation7 108 109 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation7 108) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation7 108 by rw [image7_eq]; rfl))

theorem lex_7_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3567) (Sat.Literal.pos 3566) (Sat.Literal.pos 108) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation7 108 (assignment s)
    (Sat.Literal.pos 3567) (Sat.Literal.pos 3566) (Sat.Literal.pos 108) (Sat.Literal.pos 216) (positive_of_descriptor s 3567 (.lex permutation7 108) (by rfl)) (lex_7_108_prefix s) (positive_select s 108) (lex_7_108_image s)

theorem lex_7_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.pos 108), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation7 108 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3566) (Sat.Literal.pos 108) (Sat.Literal.pos 216) (lex_7_108_prefix s) (positive_select s 108) (lex_7_108_image s)

theorem lex_7_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.pos 3566)] :=
  (lex_7_108_gate s).prop _ (List.Mem.head _)

theorem lex_7_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.neg 108), (Sat.Literal.pos 216)] :=
  (lex_7_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.pos 108), (Sat.Literal.neg 216)] :=
  (lex_7_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.neg 108), (Sat.Literal.neg 216), (Sat.Literal.pos 3567)] :=
  (lex_7_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3566), (Sat.Literal.pos 108), (Sat.Literal.pos 216), (Sat.Literal.pos 3567)] :=
  (lex_7_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3567) = lexBefore s permutation7 107 := by
  exact (positive_lex_of_descriptor s 3567 permutation7 108 (by rfl)).trans ((lex_skipped s permutation7 107 108 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation7 107) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation7 107 by rw [image7_eq]; rfl))

theorem lex_7_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3568) (Sat.Literal.pos 3567) (Sat.Literal.pos 107) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation7 107 (assignment s)
    (Sat.Literal.pos 3568) (Sat.Literal.pos 3567) (Sat.Literal.pos 107) (Sat.Literal.pos 214) (positive_of_descriptor s 3568 (.lex permutation7 107) (by rfl)) (lex_7_107_prefix s) (positive_select s 107) (lex_7_107_image s)

theorem lex_7_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.pos 107), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation7 107 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3567) (Sat.Literal.pos 107) (Sat.Literal.pos 214) (lex_7_107_prefix s) (positive_select s 107) (lex_7_107_image s)

theorem lex_7_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.pos 3567)] :=
  (lex_7_107_gate s).prop _ (List.Mem.head _)

theorem lex_7_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.neg 107), (Sat.Literal.pos 214)] :=
  (lex_7_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.pos 107), (Sat.Literal.neg 214)] :=
  (lex_7_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.neg 107), (Sat.Literal.neg 214), (Sat.Literal.pos 3568)] :=
  (lex_7_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3567), (Sat.Literal.pos 107), (Sat.Literal.pos 214), (Sat.Literal.pos 3568)] :=
  (lex_7_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3568) = lexBefore s permutation7 106 := by
  exact (positive_lex_of_descriptor s 3568 permutation7 107 (by rfl)).trans ((lex_skipped s permutation7 106 107 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation7 106) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation7 106 by rw [image7_eq]; rfl))

theorem lex_7_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3569) (Sat.Literal.pos 3568) (Sat.Literal.pos 106) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation7 106 (assignment s)
    (Sat.Literal.pos 3569) (Sat.Literal.pos 3568) (Sat.Literal.pos 106) (Sat.Literal.pos 212) (positive_of_descriptor s 3569 (.lex permutation7 106) (by rfl)) (lex_7_106_prefix s) (positive_select s 106) (lex_7_106_image s)

theorem lex_7_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.pos 106), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation7 106 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3568) (Sat.Literal.pos 106) (Sat.Literal.pos 212) (lex_7_106_prefix s) (positive_select s 106) (lex_7_106_image s)

theorem lex_7_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.pos 3568)] :=
  (lex_7_106_gate s).prop _ (List.Mem.head _)

theorem lex_7_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.neg 106), (Sat.Literal.pos 212)] :=
  (lex_7_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.pos 106), (Sat.Literal.neg 212)] :=
  (lex_7_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.neg 106), (Sat.Literal.neg 212), (Sat.Literal.pos 3569)] :=
  (lex_7_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3568), (Sat.Literal.pos 106), (Sat.Literal.pos 212), (Sat.Literal.pos 3569)] :=
  (lex_7_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3569) = lexBefore s permutation7 105 := by
  exact (positive_lex_of_descriptor s 3569 permutation7 106 (by rfl)).trans ((lex_skipped s permutation7 105 106 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation7 105) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation7 105 by rw [image7_eq]; rfl))

theorem lex_7_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3570) (Sat.Literal.pos 3569) (Sat.Literal.pos 105) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation7 105 (assignment s)
    (Sat.Literal.pos 3570) (Sat.Literal.pos 3569) (Sat.Literal.pos 105) (Sat.Literal.pos 210) (positive_of_descriptor s 3570 (.lex permutation7 105) (by rfl)) (lex_7_105_prefix s) (positive_select s 105) (lex_7_105_image s)

theorem lex_7_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.pos 105), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation7 105 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3569) (Sat.Literal.pos 105) (Sat.Literal.pos 210) (lex_7_105_prefix s) (positive_select s 105) (lex_7_105_image s)

theorem lex_7_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.pos 3569)] :=
  (lex_7_105_gate s).prop _ (List.Mem.head _)

theorem lex_7_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.neg 105), (Sat.Literal.pos 210)] :=
  (lex_7_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.pos 105), (Sat.Literal.neg 210)] :=
  (lex_7_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.neg 105), (Sat.Literal.neg 210), (Sat.Literal.pos 3570)] :=
  (lex_7_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3569), (Sat.Literal.pos 105), (Sat.Literal.pos 210), (Sat.Literal.pos 3570)] :=
  (lex_7_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3570) = lexBefore s permutation7 104 := by
  exact (positive_lex_of_descriptor s 3570 permutation7 105 (by rfl)).trans ((lex_skipped s permutation7 104 105 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation7 104) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation7 104 by rw [image7_eq]; rfl))

theorem lex_7_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3571) (Sat.Literal.pos 3570) (Sat.Literal.pos 104) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation7 104 (assignment s)
    (Sat.Literal.pos 3571) (Sat.Literal.pos 3570) (Sat.Literal.pos 104) (Sat.Literal.pos 208) (positive_of_descriptor s 3571 (.lex permutation7 104) (by rfl)) (lex_7_104_prefix s) (positive_select s 104) (lex_7_104_image s)

theorem lex_7_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.pos 104), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation7 104 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3570) (Sat.Literal.pos 104) (Sat.Literal.pos 208) (lex_7_104_prefix s) (positive_select s 104) (lex_7_104_image s)

theorem lex_7_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.pos 3570)] :=
  (lex_7_104_gate s).prop _ (List.Mem.head _)

theorem lex_7_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.neg 104), (Sat.Literal.pos 208)] :=
  (lex_7_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.pos 104), (Sat.Literal.neg 208)] :=
  (lex_7_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.neg 104), (Sat.Literal.neg 208), (Sat.Literal.pos 3571)] :=
  (lex_7_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3570), (Sat.Literal.pos 104), (Sat.Literal.pos 208), (Sat.Literal.pos 3571)] :=
  (lex_7_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3571) = lexBefore s permutation7 103 := by
  exact (positive_lex_of_descriptor s 3571 permutation7 104 (by rfl)).trans ((lex_skipped s permutation7 103 104 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation7 103) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation7 103 by rw [image7_eq]; rfl))

theorem lex_7_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3572) (Sat.Literal.pos 3571) (Sat.Literal.pos 103) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation7 103 (assignment s)
    (Sat.Literal.pos 3572) (Sat.Literal.pos 3571) (Sat.Literal.pos 103) (Sat.Literal.pos 206) (positive_of_descriptor s 3572 (.lex permutation7 103) (by rfl)) (lex_7_103_prefix s) (positive_select s 103) (lex_7_103_image s)

theorem lex_7_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.pos 103), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation7 103 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3571) (Sat.Literal.pos 103) (Sat.Literal.pos 206) (lex_7_103_prefix s) (positive_select s 103) (lex_7_103_image s)

theorem lex_7_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.pos 3571)] :=
  (lex_7_103_gate s).prop _ (List.Mem.head _)

theorem lex_7_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.neg 103), (Sat.Literal.pos 206)] :=
  (lex_7_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.pos 103), (Sat.Literal.neg 206)] :=
  (lex_7_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.neg 103), (Sat.Literal.neg 206), (Sat.Literal.pos 3572)] :=
  (lex_7_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3571), (Sat.Literal.pos 103), (Sat.Literal.pos 206), (Sat.Literal.pos 3572)] :=
  (lex_7_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3572) = lexBefore s permutation7 102 := by
  exact (positive_lex_of_descriptor s 3572 permutation7 103 (by rfl)).trans ((lex_skipped s permutation7 102 103 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation7 102) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation7 102 by rw [image7_eq]; rfl))

theorem lex_7_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3573) (Sat.Literal.pos 3572) (Sat.Literal.pos 102) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation7 102 (assignment s)
    (Sat.Literal.pos 3573) (Sat.Literal.pos 3572) (Sat.Literal.pos 102) (Sat.Literal.pos 204) (positive_of_descriptor s 3573 (.lex permutation7 102) (by rfl)) (lex_7_102_prefix s) (positive_select s 102) (lex_7_102_image s)

theorem lex_7_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.pos 102), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation7 102 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3572) (Sat.Literal.pos 102) (Sat.Literal.pos 204) (lex_7_102_prefix s) (positive_select s 102) (lex_7_102_image s)

theorem lex_7_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.pos 3572)] :=
  (lex_7_102_gate s).prop _ (List.Mem.head _)

theorem lex_7_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.neg 102), (Sat.Literal.pos 204)] :=
  (lex_7_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.pos 102), (Sat.Literal.neg 204)] :=
  (lex_7_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.neg 102), (Sat.Literal.neg 204), (Sat.Literal.pos 3573)] :=
  (lex_7_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3572), (Sat.Literal.pos 102), (Sat.Literal.pos 204), (Sat.Literal.pos 3573)] :=
  (lex_7_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3573) = lexBefore s permutation7 101 := by
  exact (positive_lex_of_descriptor s 3573 permutation7 102 (by rfl)).trans ((lex_skipped s permutation7 101 102 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation7 101) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation7 101 by rw [image7_eq]; rfl))

theorem lex_7_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3574) (Sat.Literal.pos 3573) (Sat.Literal.pos 101) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation7 101 (assignment s)
    (Sat.Literal.pos 3574) (Sat.Literal.pos 3573) (Sat.Literal.pos 101) (Sat.Literal.pos 202) (positive_of_descriptor s 3574 (.lex permutation7 101) (by rfl)) (lex_7_101_prefix s) (positive_select s 101) (lex_7_101_image s)

theorem lex_7_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.pos 101), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation7 101 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3573) (Sat.Literal.pos 101) (Sat.Literal.pos 202) (lex_7_101_prefix s) (positive_select s 101) (lex_7_101_image s)

theorem lex_7_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.pos 3573)] :=
  (lex_7_101_gate s).prop _ (List.Mem.head _)

theorem lex_7_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.neg 101), (Sat.Literal.pos 202)] :=
  (lex_7_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.pos 101), (Sat.Literal.neg 202)] :=
  (lex_7_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.neg 101), (Sat.Literal.neg 202), (Sat.Literal.pos 3574)] :=
  (lex_7_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3573), (Sat.Literal.pos 101), (Sat.Literal.pos 202), (Sat.Literal.pos 3574)] :=
  (lex_7_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3574) = lexBefore s permutation7 100 := by
  exact (positive_lex_of_descriptor s 3574 permutation7 101 (by rfl)).trans ((lex_skipped s permutation7 100 101 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation7 100) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation7 100 by rw [image7_eq]; rfl))

theorem lex_7_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3575) (Sat.Literal.pos 3574) (Sat.Literal.pos 100) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation7 100 (assignment s)
    (Sat.Literal.pos 3575) (Sat.Literal.pos 3574) (Sat.Literal.pos 100) (Sat.Literal.pos 200) (positive_of_descriptor s 3575 (.lex permutation7 100) (by rfl)) (lex_7_100_prefix s) (positive_select s 100) (lex_7_100_image s)

theorem lex_7_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.pos 100), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation7 100 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3574) (Sat.Literal.pos 100) (Sat.Literal.pos 200) (lex_7_100_prefix s) (positive_select s 100) (lex_7_100_image s)

theorem lex_7_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.pos 3574)] :=
  (lex_7_100_gate s).prop _ (List.Mem.head _)

theorem lex_7_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.neg 100), (Sat.Literal.pos 200)] :=
  (lex_7_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.pos 100), (Sat.Literal.neg 200)] :=
  (lex_7_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.neg 100), (Sat.Literal.neg 200), (Sat.Literal.pos 3575)] :=
  (lex_7_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3574), (Sat.Literal.pos 100), (Sat.Literal.pos 200), (Sat.Literal.pos 3575)] :=
  (lex_7_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3575) = lexBefore s permutation7 99 := by
  exact (positive_lex_of_descriptor s 3575 permutation7 100 (by rfl)).trans ((lex_skipped s permutation7 99 100 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation7 99) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation7 99 by rw [image7_eq]; rfl))

theorem lex_7_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3576) (Sat.Literal.pos 3575) (Sat.Literal.pos 99) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation7 99 (assignment s)
    (Sat.Literal.pos 3576) (Sat.Literal.pos 3575) (Sat.Literal.pos 99) (Sat.Literal.pos 198) (positive_of_descriptor s 3576 (.lex permutation7 99) (by rfl)) (lex_7_99_prefix s) (positive_select s 99) (lex_7_99_image s)

theorem lex_7_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.pos 99), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation7 99 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3575) (Sat.Literal.pos 99) (Sat.Literal.pos 198) (lex_7_99_prefix s) (positive_select s 99) (lex_7_99_image s)

theorem lex_7_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.pos 3575)] :=
  (lex_7_99_gate s).prop _ (List.Mem.head _)

theorem lex_7_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.neg 99), (Sat.Literal.pos 198)] :=
  (lex_7_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.pos 99), (Sat.Literal.neg 198)] :=
  (lex_7_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.neg 99), (Sat.Literal.neg 198), (Sat.Literal.pos 3576)] :=
  (lex_7_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3575), (Sat.Literal.pos 99), (Sat.Literal.pos 198), (Sat.Literal.pos 3576)] :=
  (lex_7_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3576) = lexBefore s permutation7 98 := by
  exact (positive_lex_of_descriptor s 3576 permutation7 99 (by rfl)).trans ((lex_skipped s permutation7 98 99 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation7 98) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation7 98 by rw [image7_eq]; rfl))

theorem lex_7_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3577) (Sat.Literal.pos 3576) (Sat.Literal.pos 98) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation7 98 (assignment s)
    (Sat.Literal.pos 3577) (Sat.Literal.pos 3576) (Sat.Literal.pos 98) (Sat.Literal.pos 196) (positive_of_descriptor s 3577 (.lex permutation7 98) (by rfl)) (lex_7_98_prefix s) (positive_select s 98) (lex_7_98_image s)

theorem lex_7_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.pos 98), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation7 98 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3576) (Sat.Literal.pos 98) (Sat.Literal.pos 196) (lex_7_98_prefix s) (positive_select s 98) (lex_7_98_image s)

theorem lex_7_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.pos 3576)] :=
  (lex_7_98_gate s).prop _ (List.Mem.head _)

theorem lex_7_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.neg 98), (Sat.Literal.pos 196)] :=
  (lex_7_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.pos 98), (Sat.Literal.neg 196)] :=
  (lex_7_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.neg 98), (Sat.Literal.neg 196), (Sat.Literal.pos 3577)] :=
  (lex_7_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3576), (Sat.Literal.pos 98), (Sat.Literal.pos 196), (Sat.Literal.pos 3577)] :=
  (lex_7_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3577) = lexBefore s permutation7 97 := by
  exact (positive_lex_of_descriptor s 3577 permutation7 98 (by rfl)).trans ((lex_skipped s permutation7 97 98 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation7 97) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation7 97 by rw [image7_eq]; rfl))

theorem lex_7_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3578) (Sat.Literal.pos 3577) (Sat.Literal.pos 97) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation7 97 (assignment s)
    (Sat.Literal.pos 3578) (Sat.Literal.pos 3577) (Sat.Literal.pos 97) (Sat.Literal.pos 194) (positive_of_descriptor s 3578 (.lex permutation7 97) (by rfl)) (lex_7_97_prefix s) (positive_select s 97) (lex_7_97_image s)

theorem lex_7_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.pos 97), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation7 97 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3577) (Sat.Literal.pos 97) (Sat.Literal.pos 194) (lex_7_97_prefix s) (positive_select s 97) (lex_7_97_image s)

theorem lex_7_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.pos 3577)] :=
  (lex_7_97_gate s).prop _ (List.Mem.head _)

theorem lex_7_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.neg 97), (Sat.Literal.pos 194)] :=
  (lex_7_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.pos 97), (Sat.Literal.neg 194)] :=
  (lex_7_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.neg 97), (Sat.Literal.neg 194), (Sat.Literal.pos 3578)] :=
  (lex_7_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3577), (Sat.Literal.pos 97), (Sat.Literal.pos 194), (Sat.Literal.pos 3578)] :=
  (lex_7_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3578) = lexBefore s permutation7 96 := by
  exact (positive_lex_of_descriptor s 3578 permutation7 97 (by rfl)).trans ((lex_skipped s permutation7 96 97 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation7 96) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation7 96 by rw [image7_eq]; rfl))

theorem lex_7_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3579) (Sat.Literal.pos 3578) (Sat.Literal.pos 96) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation7 96 (assignment s)
    (Sat.Literal.pos 3579) (Sat.Literal.pos 3578) (Sat.Literal.pos 96) (Sat.Literal.pos 192) (positive_of_descriptor s 3579 (.lex permutation7 96) (by rfl)) (lex_7_96_prefix s) (positive_select s 96) (lex_7_96_image s)

theorem lex_7_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.pos 96), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation7 96 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3578) (Sat.Literal.pos 96) (Sat.Literal.pos 192) (lex_7_96_prefix s) (positive_select s 96) (lex_7_96_image s)

theorem lex_7_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.pos 3578)] :=
  (lex_7_96_gate s).prop _ (List.Mem.head _)

theorem lex_7_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.neg 96), (Sat.Literal.pos 192)] :=
  (lex_7_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.pos 96), (Sat.Literal.neg 192)] :=
  (lex_7_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.neg 96), (Sat.Literal.neg 192), (Sat.Literal.pos 3579)] :=
  (lex_7_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3578), (Sat.Literal.pos 96), (Sat.Literal.pos 192), (Sat.Literal.pos 3579)] :=
  (lex_7_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3579) = lexBefore s permutation7 95 := by
  exact (positive_lex_of_descriptor s 3579 permutation7 96 (by rfl)).trans ((lex_skipped s permutation7 95 96 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation7 95) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation7 95 by rw [image7_eq]; rfl))

theorem lex_7_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3580) (Sat.Literal.pos 3579) (Sat.Literal.pos 95) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation7 95 (assignment s)
    (Sat.Literal.pos 3580) (Sat.Literal.pos 3579) (Sat.Literal.pos 95) (Sat.Literal.pos 190) (positive_of_descriptor s 3580 (.lex permutation7 95) (by rfl)) (lex_7_95_prefix s) (positive_select s 95) (lex_7_95_image s)

theorem lex_7_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.pos 95), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation7 95 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3579) (Sat.Literal.pos 95) (Sat.Literal.pos 190) (lex_7_95_prefix s) (positive_select s 95) (lex_7_95_image s)

theorem lex_7_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.pos 3579)] :=
  (lex_7_95_gate s).prop _ (List.Mem.head _)

theorem lex_7_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.neg 95), (Sat.Literal.pos 190)] :=
  (lex_7_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.pos 95), (Sat.Literal.neg 190)] :=
  (lex_7_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.neg 95), (Sat.Literal.neg 190), (Sat.Literal.pos 3580)] :=
  (lex_7_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3579), (Sat.Literal.pos 95), (Sat.Literal.pos 190), (Sat.Literal.pos 3580)] :=
  (lex_7_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3580) = lexBefore s permutation7 94 := by
  exact (positive_lex_of_descriptor s 3580 permutation7 95 (by rfl)).trans ((lex_skipped s permutation7 94 95 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation7 94) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation7 94 by rw [image7_eq]; rfl))

theorem lex_7_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3581) (Sat.Literal.pos 3580) (Sat.Literal.pos 94) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation7 94 (assignment s)
    (Sat.Literal.pos 3581) (Sat.Literal.pos 3580) (Sat.Literal.pos 94) (Sat.Literal.pos 188) (positive_of_descriptor s 3581 (.lex permutation7 94) (by rfl)) (lex_7_94_prefix s) (positive_select s 94) (lex_7_94_image s)

theorem lex_7_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.pos 94), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation7 94 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3580) (Sat.Literal.pos 94) (Sat.Literal.pos 188) (lex_7_94_prefix s) (positive_select s 94) (lex_7_94_image s)

theorem lex_7_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.pos 3580)] :=
  (lex_7_94_gate s).prop _ (List.Mem.head _)

theorem lex_7_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.neg 94), (Sat.Literal.pos 188)] :=
  (lex_7_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.pos 94), (Sat.Literal.neg 188)] :=
  (lex_7_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.neg 94), (Sat.Literal.neg 188), (Sat.Literal.pos 3581)] :=
  (lex_7_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3580), (Sat.Literal.pos 94), (Sat.Literal.pos 188), (Sat.Literal.pos 3581)] :=
  (lex_7_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3581) = lexBefore s permutation7 93 := by
  exact (positive_lex_of_descriptor s 3581 permutation7 94 (by rfl)).trans ((lex_skipped s permutation7 93 94 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation7 93) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation7 93 by rw [image7_eq]; rfl))

theorem lex_7_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3582) (Sat.Literal.pos 3581) (Sat.Literal.pos 93) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation7 93 (assignment s)
    (Sat.Literal.pos 3582) (Sat.Literal.pos 3581) (Sat.Literal.pos 93) (Sat.Literal.pos 186) (positive_of_descriptor s 3582 (.lex permutation7 93) (by rfl)) (lex_7_93_prefix s) (positive_select s 93) (lex_7_93_image s)

theorem lex_7_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.pos 93), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation7 93 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3581) (Sat.Literal.pos 93) (Sat.Literal.pos 186) (lex_7_93_prefix s) (positive_select s 93) (lex_7_93_image s)

theorem lex_7_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.pos 3581)] :=
  (lex_7_93_gate s).prop _ (List.Mem.head _)

theorem lex_7_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.neg 93), (Sat.Literal.pos 186)] :=
  (lex_7_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.pos 93), (Sat.Literal.neg 186)] :=
  (lex_7_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.neg 93), (Sat.Literal.neg 186), (Sat.Literal.pos 3582)] :=
  (lex_7_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3581), (Sat.Literal.pos 93), (Sat.Literal.pos 186), (Sat.Literal.pos 3582)] :=
  (lex_7_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3582) = lexBefore s permutation7 92 := by
  exact (positive_lex_of_descriptor s 3582 permutation7 93 (by rfl)).trans ((lex_skipped s permutation7 92 93 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation7 92) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation7 92 by rw [image7_eq]; rfl))

theorem lex_7_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3583) (Sat.Literal.pos 3582) (Sat.Literal.pos 92) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation7 92 (assignment s)
    (Sat.Literal.pos 3583) (Sat.Literal.pos 3582) (Sat.Literal.pos 92) (Sat.Literal.pos 184) (positive_of_descriptor s 3583 (.lex permutation7 92) (by rfl)) (lex_7_92_prefix s) (positive_select s 92) (lex_7_92_image s)

theorem lex_7_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.pos 92), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation7 92 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3582) (Sat.Literal.pos 92) (Sat.Literal.pos 184) (lex_7_92_prefix s) (positive_select s 92) (lex_7_92_image s)

theorem lex_7_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.pos 3582)] :=
  (lex_7_92_gate s).prop _ (List.Mem.head _)

theorem lex_7_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.neg 92), (Sat.Literal.pos 184)] :=
  (lex_7_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.pos 92), (Sat.Literal.neg 184)] :=
  (lex_7_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.neg 92), (Sat.Literal.neg 184), (Sat.Literal.pos 3583)] :=
  (lex_7_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3582), (Sat.Literal.pos 92), (Sat.Literal.pos 184), (Sat.Literal.pos 3583)] :=
  (lex_7_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3583) = lexBefore s permutation7 91 := by
  exact (positive_lex_of_descriptor s 3583 permutation7 92 (by rfl)).trans ((lex_skipped s permutation7 91 92 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation7 91) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation7 91 by rw [image7_eq]; rfl))

theorem lex_7_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3584) (Sat.Literal.pos 3583) (Sat.Literal.pos 91) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation7 91 (assignment s)
    (Sat.Literal.pos 3584) (Sat.Literal.pos 3583) (Sat.Literal.pos 91) (Sat.Literal.pos 182) (positive_of_descriptor s 3584 (.lex permutation7 91) (by rfl)) (lex_7_91_prefix s) (positive_select s 91) (lex_7_91_image s)

theorem lex_7_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.pos 91), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation7 91 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3583) (Sat.Literal.pos 91) (Sat.Literal.pos 182) (lex_7_91_prefix s) (positive_select s 91) (lex_7_91_image s)

theorem lex_7_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.pos 3583)] :=
  (lex_7_91_gate s).prop _ (List.Mem.head _)

theorem lex_7_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.neg 91), (Sat.Literal.pos 182)] :=
  (lex_7_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.pos 91), (Sat.Literal.neg 182)] :=
  (lex_7_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.neg 91), (Sat.Literal.neg 182), (Sat.Literal.pos 3584)] :=
  (lex_7_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3583), (Sat.Literal.pos 91), (Sat.Literal.pos 182), (Sat.Literal.pos 3584)] :=
  (lex_7_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3584) = lexBefore s permutation7 90 := by
  exact (positive_lex_of_descriptor s 3584 permutation7 91 (by rfl)).trans ((lex_skipped s permutation7 90 91 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation7 90) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation7 90 by rw [image7_eq]; rfl))

theorem lex_7_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3585) (Sat.Literal.pos 3584) (Sat.Literal.pos 90) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation7 90 (assignment s)
    (Sat.Literal.pos 3585) (Sat.Literal.pos 3584) (Sat.Literal.pos 90) (Sat.Literal.pos 180) (positive_of_descriptor s 3585 (.lex permutation7 90) (by rfl)) (lex_7_90_prefix s) (positive_select s 90) (lex_7_90_image s)

theorem lex_7_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.pos 90), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation7 90 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3584) (Sat.Literal.pos 90) (Sat.Literal.pos 180) (lex_7_90_prefix s) (positive_select s 90) (lex_7_90_image s)

theorem lex_7_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.pos 3584)] :=
  (lex_7_90_gate s).prop _ (List.Mem.head _)

theorem lex_7_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.neg 90), (Sat.Literal.pos 180)] :=
  (lex_7_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.pos 90), (Sat.Literal.neg 180)] :=
  (lex_7_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.neg 90), (Sat.Literal.neg 180), (Sat.Literal.pos 3585)] :=
  (lex_7_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3584), (Sat.Literal.pos 90), (Sat.Literal.pos 180), (Sat.Literal.pos 3585)] :=
  (lex_7_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3585) = lexBefore s permutation7 89 := by
  exact (positive_lex_of_descriptor s 3585 permutation7 90 (by rfl)).trans ((lex_skipped s permutation7 89 90 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation7 89) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation7 89 by rw [image7_eq]; rfl))

theorem lex_7_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3586) (Sat.Literal.pos 3585) (Sat.Literal.pos 89) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation7 89 (assignment s)
    (Sat.Literal.pos 3586) (Sat.Literal.pos 3585) (Sat.Literal.pos 89) (Sat.Literal.pos 178) (positive_of_descriptor s 3586 (.lex permutation7 89) (by rfl)) (lex_7_89_prefix s) (positive_select s 89) (lex_7_89_image s)

theorem lex_7_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.pos 89), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation7 89 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3585) (Sat.Literal.pos 89) (Sat.Literal.pos 178) (lex_7_89_prefix s) (positive_select s 89) (lex_7_89_image s)

theorem lex_7_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.pos 3585)] :=
  (lex_7_89_gate s).prop _ (List.Mem.head _)

theorem lex_7_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.neg 89), (Sat.Literal.pos 178)] :=
  (lex_7_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.pos 89), (Sat.Literal.neg 178)] :=
  (lex_7_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.neg 89), (Sat.Literal.neg 178), (Sat.Literal.pos 3586)] :=
  (lex_7_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3585), (Sat.Literal.pos 89), (Sat.Literal.pos 178), (Sat.Literal.pos 3586)] :=
  (lex_7_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3586) = lexBefore s permutation7 88 := by
  exact (positive_lex_of_descriptor s 3586 permutation7 89 (by rfl)).trans ((lex_skipped s permutation7 88 89 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation7 88) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation7 88 by rw [image7_eq]; rfl))

theorem lex_7_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3587) (Sat.Literal.pos 3586) (Sat.Literal.pos 88) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation7 88 (assignment s)
    (Sat.Literal.pos 3587) (Sat.Literal.pos 3586) (Sat.Literal.pos 88) (Sat.Literal.pos 176) (positive_of_descriptor s 3587 (.lex permutation7 88) (by rfl)) (lex_7_88_prefix s) (positive_select s 88) (lex_7_88_image s)

theorem lex_7_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.pos 88), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation7 88 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3586) (Sat.Literal.pos 88) (Sat.Literal.pos 176) (lex_7_88_prefix s) (positive_select s 88) (lex_7_88_image s)

theorem lex_7_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.pos 3586)] :=
  (lex_7_88_gate s).prop _ (List.Mem.head _)

theorem lex_7_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.neg 88), (Sat.Literal.pos 176)] :=
  (lex_7_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.pos 88), (Sat.Literal.neg 176)] :=
  (lex_7_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.neg 88), (Sat.Literal.neg 176), (Sat.Literal.pos 3587)] :=
  (lex_7_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3586), (Sat.Literal.pos 88), (Sat.Literal.pos 176), (Sat.Literal.pos 3587)] :=
  (lex_7_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3587) = lexBefore s permutation7 87 := by
  exact (positive_lex_of_descriptor s 3587 permutation7 88 (by rfl)).trans ((lex_skipped s permutation7 87 88 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation7 87) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation7 87 by rw [image7_eq]; rfl))

theorem lex_7_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3588) (Sat.Literal.pos 3587) (Sat.Literal.pos 87) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation7 87 (assignment s)
    (Sat.Literal.pos 3588) (Sat.Literal.pos 3587) (Sat.Literal.pos 87) (Sat.Literal.pos 174) (positive_of_descriptor s 3588 (.lex permutation7 87) (by rfl)) (lex_7_87_prefix s) (positive_select s 87) (lex_7_87_image s)

theorem lex_7_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.pos 87), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation7 87 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3587) (Sat.Literal.pos 87) (Sat.Literal.pos 174) (lex_7_87_prefix s) (positive_select s 87) (lex_7_87_image s)

theorem lex_7_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.pos 3587)] :=
  (lex_7_87_gate s).prop _ (List.Mem.head _)

theorem lex_7_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.neg 87), (Sat.Literal.pos 174)] :=
  (lex_7_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.pos 87), (Sat.Literal.neg 174)] :=
  (lex_7_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.neg 87), (Sat.Literal.neg 174), (Sat.Literal.pos 3588)] :=
  (lex_7_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3587), (Sat.Literal.pos 87), (Sat.Literal.pos 174), (Sat.Literal.pos 3588)] :=
  (lex_7_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3588) = lexBefore s permutation7 86 := by
  exact (positive_lex_of_descriptor s 3588 permutation7 87 (by rfl)).trans ((lex_skipped s permutation7 86 87 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation7 86) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation7 86 by rw [image7_eq]; rfl))

theorem lex_7_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3589) (Sat.Literal.pos 3588) (Sat.Literal.pos 86) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation7 86 (assignment s)
    (Sat.Literal.pos 3589) (Sat.Literal.pos 3588) (Sat.Literal.pos 86) (Sat.Literal.pos 172) (positive_of_descriptor s 3589 (.lex permutation7 86) (by rfl)) (lex_7_86_prefix s) (positive_select s 86) (lex_7_86_image s)

theorem lex_7_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.pos 86), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation7 86 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3588) (Sat.Literal.pos 86) (Sat.Literal.pos 172) (lex_7_86_prefix s) (positive_select s 86) (lex_7_86_image s)

theorem lex_7_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.pos 3588)] :=
  (lex_7_86_gate s).prop _ (List.Mem.head _)

theorem lex_7_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.neg 86), (Sat.Literal.pos 172)] :=
  (lex_7_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.pos 86), (Sat.Literal.neg 172)] :=
  (lex_7_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.neg 86), (Sat.Literal.neg 172), (Sat.Literal.pos 3589)] :=
  (lex_7_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3588), (Sat.Literal.pos 86), (Sat.Literal.pos 172), (Sat.Literal.pos 3589)] :=
  (lex_7_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3589) = lexBefore s permutation7 85 := by
  exact (positive_lex_of_descriptor s 3589 permutation7 86 (by rfl)).trans ((lex_skipped s permutation7 85 86 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation7 85) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation7 85 by rw [image7_eq]; rfl))

theorem lex_7_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3590) (Sat.Literal.pos 3589) (Sat.Literal.pos 85) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation7 85 (assignment s)
    (Sat.Literal.pos 3590) (Sat.Literal.pos 3589) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (positive_of_descriptor s 3590 (.lex permutation7 85) (by rfl)) (lex_7_85_prefix s) (positive_select s 85) (lex_7_85_image s)

theorem lex_7_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation7 85 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3589) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (lex_7_85_prefix s) (positive_select s 85) (lex_7_85_image s)

theorem lex_7_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.pos 3589)] :=
  (lex_7_85_gate s).prop _ (List.Mem.head _)

theorem lex_7_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.neg 85), (Sat.Literal.pos 170)] :=
  (lex_7_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] :=
  (lex_7_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.neg 85), (Sat.Literal.neg 170), (Sat.Literal.pos 3590)] :=
  (lex_7_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3589), (Sat.Literal.pos 85), (Sat.Literal.pos 170), (Sat.Literal.pos 3590)] :=
  (lex_7_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3590) = lexBefore s permutation7 84 := by
  exact (positive_lex_of_descriptor s 3590 permutation7 85 (by rfl)).trans ((lex_skipped s permutation7 84 85 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation7 84) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation7 84 by rw [image7_eq]; rfl))

theorem lex_7_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3591) (Sat.Literal.pos 3590) (Sat.Literal.pos 84) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation7 84 (assignment s)
    (Sat.Literal.pos 3591) (Sat.Literal.pos 3590) (Sat.Literal.pos 84) (Sat.Literal.pos 168) (positive_of_descriptor s 3591 (.lex permutation7 84) (by rfl)) (lex_7_84_prefix s) (positive_select s 84) (lex_7_84_image s)

theorem lex_7_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.pos 84), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation7 84 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3590) (Sat.Literal.pos 84) (Sat.Literal.pos 168) (lex_7_84_prefix s) (positive_select s 84) (lex_7_84_image s)

theorem lex_7_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.pos 3590)] :=
  (lex_7_84_gate s).prop _ (List.Mem.head _)

theorem lex_7_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.neg 84), (Sat.Literal.pos 168)] :=
  (lex_7_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.pos 84), (Sat.Literal.neg 168)] :=
  (lex_7_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.neg 84), (Sat.Literal.neg 168), (Sat.Literal.pos 3591)] :=
  (lex_7_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3590), (Sat.Literal.pos 84), (Sat.Literal.pos 168), (Sat.Literal.pos 3591)] :=
  (lex_7_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3591) = lexBefore s permutation7 83 := by
  exact (positive_lex_of_descriptor s 3591 permutation7 84 (by rfl)).trans ((lex_skipped s permutation7 83 84 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation7 83) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation7 83 by rw [image7_eq]; rfl))

theorem lex_7_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3592) (Sat.Literal.pos 3591) (Sat.Literal.pos 83) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation7 83 (assignment s)
    (Sat.Literal.pos 3592) (Sat.Literal.pos 3591) (Sat.Literal.pos 83) (Sat.Literal.pos 166) (positive_of_descriptor s 3592 (.lex permutation7 83) (by rfl)) (lex_7_83_prefix s) (positive_select s 83) (lex_7_83_image s)

theorem lex_7_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.pos 83), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation7 83 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3591) (Sat.Literal.pos 83) (Sat.Literal.pos 166) (lex_7_83_prefix s) (positive_select s 83) (lex_7_83_image s)

theorem lex_7_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.pos 3591)] :=
  (lex_7_83_gate s).prop _ (List.Mem.head _)

theorem lex_7_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.neg 83), (Sat.Literal.pos 166)] :=
  (lex_7_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.pos 83), (Sat.Literal.neg 166)] :=
  (lex_7_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.neg 83), (Sat.Literal.neg 166), (Sat.Literal.pos 3592)] :=
  (lex_7_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3591), (Sat.Literal.pos 83), (Sat.Literal.pos 166), (Sat.Literal.pos 3592)] :=
  (lex_7_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3592) = lexBefore s permutation7 82 := by
  exact (positive_lex_of_descriptor s 3592 permutation7 83 (by rfl)).trans ((lex_skipped s permutation7 82 83 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation7 82) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation7 82 by rw [image7_eq]; rfl))

theorem lex_7_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3593) (Sat.Literal.pos 3592) (Sat.Literal.pos 82) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation7 82 (assignment s)
    (Sat.Literal.pos 3593) (Sat.Literal.pos 3592) (Sat.Literal.pos 82) (Sat.Literal.pos 164) (positive_of_descriptor s 3593 (.lex permutation7 82) (by rfl)) (lex_7_82_prefix s) (positive_select s 82) (lex_7_82_image s)

theorem lex_7_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.pos 82), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation7 82 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3592) (Sat.Literal.pos 82) (Sat.Literal.pos 164) (lex_7_82_prefix s) (positive_select s 82) (lex_7_82_image s)

theorem lex_7_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.pos 3592)] :=
  (lex_7_82_gate s).prop _ (List.Mem.head _)

theorem lex_7_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.neg 82), (Sat.Literal.pos 164)] :=
  (lex_7_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.pos 82), (Sat.Literal.neg 164)] :=
  (lex_7_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.neg 82), (Sat.Literal.neg 164), (Sat.Literal.pos 3593)] :=
  (lex_7_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3592), (Sat.Literal.pos 82), (Sat.Literal.pos 164), (Sat.Literal.pos 3593)] :=
  (lex_7_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3593) = lexBefore s permutation7 81 := by
  exact (positive_lex_of_descriptor s 3593 permutation7 82 (by rfl)).trans ((lex_skipped s permutation7 81 82 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation7 81) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation7 81 by rw [image7_eq]; rfl))

theorem lex_7_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3594) (Sat.Literal.pos 3593) (Sat.Literal.pos 81) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation7 81 (assignment s)
    (Sat.Literal.pos 3594) (Sat.Literal.pos 3593) (Sat.Literal.pos 81) (Sat.Literal.pos 162) (positive_of_descriptor s 3594 (.lex permutation7 81) (by rfl)) (lex_7_81_prefix s) (positive_select s 81) (lex_7_81_image s)

theorem lex_7_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.pos 81), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation7 81 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3593) (Sat.Literal.pos 81) (Sat.Literal.pos 162) (lex_7_81_prefix s) (positive_select s 81) (lex_7_81_image s)

theorem lex_7_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.pos 3593)] :=
  (lex_7_81_gate s).prop _ (List.Mem.head _)

theorem lex_7_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.neg 81), (Sat.Literal.pos 162)] :=
  (lex_7_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.pos 81), (Sat.Literal.neg 162)] :=
  (lex_7_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.neg 81), (Sat.Literal.neg 162), (Sat.Literal.pos 3594)] :=
  (lex_7_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3593), (Sat.Literal.pos 81), (Sat.Literal.pos 162), (Sat.Literal.pos 3594)] :=
  (lex_7_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3594) = lexBefore s permutation7 80 := by
  exact (positive_lex_of_descriptor s 3594 permutation7 81 (by rfl)).trans ((lex_skipped s permutation7 80 81 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation7 80) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation7 80 by rw [image7_eq]; rfl))

theorem lex_7_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3595) (Sat.Literal.pos 3594) (Sat.Literal.pos 80) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation7 80 (assignment s)
    (Sat.Literal.pos 3595) (Sat.Literal.pos 3594) (Sat.Literal.pos 80) (Sat.Literal.pos 160) (positive_of_descriptor s 3595 (.lex permutation7 80) (by rfl)) (lex_7_80_prefix s) (positive_select s 80) (lex_7_80_image s)

theorem lex_7_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.pos 80), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation7 80 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3594) (Sat.Literal.pos 80) (Sat.Literal.pos 160) (lex_7_80_prefix s) (positive_select s 80) (lex_7_80_image s)

theorem lex_7_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.pos 3594)] :=
  (lex_7_80_gate s).prop _ (List.Mem.head _)

theorem lex_7_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.neg 80), (Sat.Literal.pos 160)] :=
  (lex_7_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.pos 80), (Sat.Literal.neg 160)] :=
  (lex_7_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.neg 80), (Sat.Literal.neg 160), (Sat.Literal.pos 3595)] :=
  (lex_7_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3594), (Sat.Literal.pos 80), (Sat.Literal.pos 160), (Sat.Literal.pos 3595)] :=
  (lex_7_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3595) = lexBefore s permutation7 79 := by
  exact (positive_lex_of_descriptor s 3595 permutation7 80 (by rfl)).trans ((lex_skipped s permutation7 79 80 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation7 79) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation7 79 by rw [image7_eq]; rfl))

theorem lex_7_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3596) (Sat.Literal.pos 3595) (Sat.Literal.pos 79) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation7 79 (assignment s)
    (Sat.Literal.pos 3596) (Sat.Literal.pos 3595) (Sat.Literal.pos 79) (Sat.Literal.pos 158) (positive_of_descriptor s 3596 (.lex permutation7 79) (by rfl)) (lex_7_79_prefix s) (positive_select s 79) (lex_7_79_image s)

theorem lex_7_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.pos 79), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation7 79 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3595) (Sat.Literal.pos 79) (Sat.Literal.pos 158) (lex_7_79_prefix s) (positive_select s 79) (lex_7_79_image s)

theorem lex_7_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.pos 3595)] :=
  (lex_7_79_gate s).prop _ (List.Mem.head _)

theorem lex_7_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.neg 79), (Sat.Literal.pos 158)] :=
  (lex_7_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.pos 79), (Sat.Literal.neg 158)] :=
  (lex_7_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.neg 79), (Sat.Literal.neg 158), (Sat.Literal.pos 3596)] :=
  (lex_7_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3595), (Sat.Literal.pos 79), (Sat.Literal.pos 158), (Sat.Literal.pos 3596)] :=
  (lex_7_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3596) = lexBefore s permutation7 78 := by
  exact (positive_lex_of_descriptor s 3596 permutation7 79 (by rfl)).trans ((lex_skipped s permutation7 78 79 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation7 78) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation7 78 by rw [image7_eq]; rfl))

theorem lex_7_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3597) (Sat.Literal.pos 3596) (Sat.Literal.pos 78) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation7 78 (assignment s)
    (Sat.Literal.pos 3597) (Sat.Literal.pos 3596) (Sat.Literal.pos 78) (Sat.Literal.pos 156) (positive_of_descriptor s 3597 (.lex permutation7 78) (by rfl)) (lex_7_78_prefix s) (positive_select s 78) (lex_7_78_image s)

theorem lex_7_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.pos 78), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation7 78 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3596) (Sat.Literal.pos 78) (Sat.Literal.pos 156) (lex_7_78_prefix s) (positive_select s 78) (lex_7_78_image s)

theorem lex_7_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.pos 3596)] :=
  (lex_7_78_gate s).prop _ (List.Mem.head _)

theorem lex_7_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.neg 78), (Sat.Literal.pos 156)] :=
  (lex_7_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.pos 78), (Sat.Literal.neg 156)] :=
  (lex_7_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.neg 78), (Sat.Literal.neg 156), (Sat.Literal.pos 3597)] :=
  (lex_7_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3596), (Sat.Literal.pos 78), (Sat.Literal.pos 156), (Sat.Literal.pos 3597)] :=
  (lex_7_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3597) = lexBefore s permutation7 77 := by
  exact (positive_lex_of_descriptor s 3597 permutation7 78 (by rfl)).trans ((lex_skipped s permutation7 77 78 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation7 77) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation7 77 by rw [image7_eq]; rfl))

theorem lex_7_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3598) (Sat.Literal.pos 3597) (Sat.Literal.pos 77) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation7 77 (assignment s)
    (Sat.Literal.pos 3598) (Sat.Literal.pos 3597) (Sat.Literal.pos 77) (Sat.Literal.pos 154) (positive_of_descriptor s 3598 (.lex permutation7 77) (by rfl)) (lex_7_77_prefix s) (positive_select s 77) (lex_7_77_image s)

theorem lex_7_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.pos 77), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation7 77 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3597) (Sat.Literal.pos 77) (Sat.Literal.pos 154) (lex_7_77_prefix s) (positive_select s 77) (lex_7_77_image s)

theorem lex_7_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.pos 3597)] :=
  (lex_7_77_gate s).prop _ (List.Mem.head _)

theorem lex_7_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.neg 77), (Sat.Literal.pos 154)] :=
  (lex_7_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.pos 77), (Sat.Literal.neg 154)] :=
  (lex_7_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.neg 77), (Sat.Literal.neg 154), (Sat.Literal.pos 3598)] :=
  (lex_7_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3597), (Sat.Literal.pos 77), (Sat.Literal.pos 154), (Sat.Literal.pos 3598)] :=
  (lex_7_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3598) = lexBefore s permutation7 76 := by
  exact (positive_lex_of_descriptor s 3598 permutation7 77 (by rfl)).trans ((lex_skipped s permutation7 76 77 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation7 76) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation7 76 by rw [image7_eq]; rfl))

theorem lex_7_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3599) (Sat.Literal.pos 3598) (Sat.Literal.pos 76) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation7 76 (assignment s)
    (Sat.Literal.pos 3599) (Sat.Literal.pos 3598) (Sat.Literal.pos 76) (Sat.Literal.pos 152) (positive_of_descriptor s 3599 (.lex permutation7 76) (by rfl)) (lex_7_76_prefix s) (positive_select s 76) (lex_7_76_image s)

theorem lex_7_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.pos 76), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation7 76 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3598) (Sat.Literal.pos 76) (Sat.Literal.pos 152) (lex_7_76_prefix s) (positive_select s 76) (lex_7_76_image s)

theorem lex_7_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.pos 3598)] :=
  (lex_7_76_gate s).prop _ (List.Mem.head _)

theorem lex_7_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.neg 76), (Sat.Literal.pos 152)] :=
  (lex_7_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.pos 76), (Sat.Literal.neg 152)] :=
  (lex_7_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.neg 76), (Sat.Literal.neg 152), (Sat.Literal.pos 3599)] :=
  (lex_7_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3598), (Sat.Literal.pos 76), (Sat.Literal.pos 152), (Sat.Literal.pos 3599)] :=
  (lex_7_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3599) = lexBefore s permutation7 75 := by
  exact (positive_lex_of_descriptor s 3599 permutation7 76 (by rfl)).trans ((lex_skipped s permutation7 75 76 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation7 75) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation7 75 by rw [image7_eq]; rfl))

theorem lex_7_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3600) (Sat.Literal.pos 3599) (Sat.Literal.pos 75) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation7 75 (assignment s)
    (Sat.Literal.pos 3600) (Sat.Literal.pos 3599) (Sat.Literal.pos 75) (Sat.Literal.pos 150) (positive_of_descriptor s 3600 (.lex permutation7 75) (by rfl)) (lex_7_75_prefix s) (positive_select s 75) (lex_7_75_image s)

theorem lex_7_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.pos 75), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation7 75 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3599) (Sat.Literal.pos 75) (Sat.Literal.pos 150) (lex_7_75_prefix s) (positive_select s 75) (lex_7_75_image s)

theorem lex_7_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.pos 3599)] :=
  (lex_7_75_gate s).prop _ (List.Mem.head _)

theorem lex_7_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.neg 75), (Sat.Literal.pos 150)] :=
  (lex_7_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.pos 75), (Sat.Literal.neg 150)] :=
  (lex_7_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.neg 75), (Sat.Literal.neg 150), (Sat.Literal.pos 3600)] :=
  (lex_7_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3599), (Sat.Literal.pos 75), (Sat.Literal.pos 150), (Sat.Literal.pos 3600)] :=
  (lex_7_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3600) = lexBefore s permutation7 74 := by
  exact (positive_lex_of_descriptor s 3600 permutation7 75 (by rfl)).trans ((lex_skipped s permutation7 74 75 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation7 74) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation7 74 by rw [image7_eq]; rfl))

theorem lex_7_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3601) (Sat.Literal.pos 3600) (Sat.Literal.pos 74) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation7 74 (assignment s)
    (Sat.Literal.pos 3601) (Sat.Literal.pos 3600) (Sat.Literal.pos 74) (Sat.Literal.pos 148) (positive_of_descriptor s 3601 (.lex permutation7 74) (by rfl)) (lex_7_74_prefix s) (positive_select s 74) (lex_7_74_image s)

theorem lex_7_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.pos 74), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation7 74 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3600) (Sat.Literal.pos 74) (Sat.Literal.pos 148) (lex_7_74_prefix s) (positive_select s 74) (lex_7_74_image s)

theorem lex_7_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.pos 3600)] :=
  (lex_7_74_gate s).prop _ (List.Mem.head _)

theorem lex_7_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.neg 74), (Sat.Literal.pos 148)] :=
  (lex_7_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.pos 74), (Sat.Literal.neg 148)] :=
  (lex_7_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.neg 74), (Sat.Literal.neg 148), (Sat.Literal.pos 3601)] :=
  (lex_7_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3600), (Sat.Literal.pos 74), (Sat.Literal.pos 148), (Sat.Literal.pos 3601)] :=
  (lex_7_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3601) = lexBefore s permutation7 73 := by
  exact (positive_lex_of_descriptor s 3601 permutation7 74 (by rfl)).trans ((lex_skipped s permutation7 73 74 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation7 73) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation7 73 by rw [image7_eq]; rfl))

theorem lex_7_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3602) (Sat.Literal.pos 3601) (Sat.Literal.pos 73) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation7 73 (assignment s)
    (Sat.Literal.pos 3602) (Sat.Literal.pos 3601) (Sat.Literal.pos 73) (Sat.Literal.pos 146) (positive_of_descriptor s 3602 (.lex permutation7 73) (by rfl)) (lex_7_73_prefix s) (positive_select s 73) (lex_7_73_image s)

theorem lex_7_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.pos 73), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation7 73 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3601) (Sat.Literal.pos 73) (Sat.Literal.pos 146) (lex_7_73_prefix s) (positive_select s 73) (lex_7_73_image s)

theorem lex_7_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.pos 3601)] :=
  (lex_7_73_gate s).prop _ (List.Mem.head _)

theorem lex_7_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.neg 73), (Sat.Literal.pos 146)] :=
  (lex_7_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.pos 73), (Sat.Literal.neg 146)] :=
  (lex_7_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.neg 73), (Sat.Literal.neg 146), (Sat.Literal.pos 3602)] :=
  (lex_7_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3601), (Sat.Literal.pos 73), (Sat.Literal.pos 146), (Sat.Literal.pos 3602)] :=
  (lex_7_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3602) = lexBefore s permutation7 72 := by
  exact (positive_lex_of_descriptor s 3602 permutation7 73 (by rfl)).trans ((lex_skipped s permutation7 72 73 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation7 72) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation7 72 by rw [image7_eq]; rfl))

theorem lex_7_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3603) (Sat.Literal.pos 3602) (Sat.Literal.pos 72) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation7 72 (assignment s)
    (Sat.Literal.pos 3603) (Sat.Literal.pos 3602) (Sat.Literal.pos 72) (Sat.Literal.pos 144) (positive_of_descriptor s 3603 (.lex permutation7 72) (by rfl)) (lex_7_72_prefix s) (positive_select s 72) (lex_7_72_image s)

theorem lex_7_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.pos 72), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation7 72 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3602) (Sat.Literal.pos 72) (Sat.Literal.pos 144) (lex_7_72_prefix s) (positive_select s 72) (lex_7_72_image s)

theorem lex_7_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.pos 3602)] :=
  (lex_7_72_gate s).prop _ (List.Mem.head _)

theorem lex_7_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.neg 72), (Sat.Literal.pos 144)] :=
  (lex_7_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.pos 72), (Sat.Literal.neg 144)] :=
  (lex_7_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.neg 72), (Sat.Literal.neg 144), (Sat.Literal.pos 3603)] :=
  (lex_7_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3602), (Sat.Literal.pos 72), (Sat.Literal.pos 144), (Sat.Literal.pos 3603)] :=
  (lex_7_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3603) = lexBefore s permutation7 71 := by
  exact (positive_lex_of_descriptor s 3603 permutation7 72 (by rfl)).trans ((lex_skipped s permutation7 71 72 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation7 71) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation7 71 by rw [image7_eq]; rfl))

theorem lex_7_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3604) (Sat.Literal.pos 3603) (Sat.Literal.pos 71) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation7 71 (assignment s)
    (Sat.Literal.pos 3604) (Sat.Literal.pos 3603) (Sat.Literal.pos 71) (Sat.Literal.pos 142) (positive_of_descriptor s 3604 (.lex permutation7 71) (by rfl)) (lex_7_71_prefix s) (positive_select s 71) (lex_7_71_image s)

theorem lex_7_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.pos 71), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation7 71 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3603) (Sat.Literal.pos 71) (Sat.Literal.pos 142) (lex_7_71_prefix s) (positive_select s 71) (lex_7_71_image s)

theorem lex_7_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.pos 3603)] :=
  (lex_7_71_gate s).prop _ (List.Mem.head _)

theorem lex_7_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.neg 71), (Sat.Literal.pos 142)] :=
  (lex_7_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.pos 71), (Sat.Literal.neg 142)] :=
  (lex_7_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.neg 71), (Sat.Literal.neg 142), (Sat.Literal.pos 3604)] :=
  (lex_7_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3603), (Sat.Literal.pos 71), (Sat.Literal.pos 142), (Sat.Literal.pos 3604)] :=
  (lex_7_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3604) = lexBefore s permutation7 70 := by
  exact (positive_lex_of_descriptor s 3604 permutation7 71 (by rfl)).trans ((lex_skipped s permutation7 70 71 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation7 70) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation7 70 by rw [image7_eq]; rfl))

theorem lex_7_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3605) (Sat.Literal.pos 3604) (Sat.Literal.pos 70) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation7 70 (assignment s)
    (Sat.Literal.pos 3605) (Sat.Literal.pos 3604) (Sat.Literal.pos 70) (Sat.Literal.pos 140) (positive_of_descriptor s 3605 (.lex permutation7 70) (by rfl)) (lex_7_70_prefix s) (positive_select s 70) (lex_7_70_image s)

theorem lex_7_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.pos 70), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation7 70 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3604) (Sat.Literal.pos 70) (Sat.Literal.pos 140) (lex_7_70_prefix s) (positive_select s 70) (lex_7_70_image s)

theorem lex_7_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.pos 3604)] :=
  (lex_7_70_gate s).prop _ (List.Mem.head _)

theorem lex_7_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.neg 70), (Sat.Literal.pos 140)] :=
  (lex_7_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.pos 70), (Sat.Literal.neg 140)] :=
  (lex_7_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.neg 70), (Sat.Literal.neg 140), (Sat.Literal.pos 3605)] :=
  (lex_7_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3604), (Sat.Literal.pos 70), (Sat.Literal.pos 140), (Sat.Literal.pos 3605)] :=
  (lex_7_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3605) = lexBefore s permutation7 69 := by
  exact (positive_lex_of_descriptor s 3605 permutation7 70 (by rfl)).trans ((lex_skipped s permutation7 69 70 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation7 69) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation7 69 by rw [image7_eq]; rfl))

theorem lex_7_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3606) (Sat.Literal.pos 3605) (Sat.Literal.pos 69) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation7 69 (assignment s)
    (Sat.Literal.pos 3606) (Sat.Literal.pos 3605) (Sat.Literal.pos 69) (Sat.Literal.pos 138) (positive_of_descriptor s 3606 (.lex permutation7 69) (by rfl)) (lex_7_69_prefix s) (positive_select s 69) (lex_7_69_image s)

theorem lex_7_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.pos 69), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation7 69 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3605) (Sat.Literal.pos 69) (Sat.Literal.pos 138) (lex_7_69_prefix s) (positive_select s 69) (lex_7_69_image s)

theorem lex_7_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.pos 3605)] :=
  (lex_7_69_gate s).prop _ (List.Mem.head _)

theorem lex_7_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.neg 69), (Sat.Literal.pos 138)] :=
  (lex_7_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.pos 69), (Sat.Literal.neg 138)] :=
  (lex_7_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.neg 69), (Sat.Literal.neg 138), (Sat.Literal.pos 3606)] :=
  (lex_7_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3605), (Sat.Literal.pos 69), (Sat.Literal.pos 138), (Sat.Literal.pos 3606)] :=
  (lex_7_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3606) = lexBefore s permutation7 68 := by
  exact (positive_lex_of_descriptor s 3606 permutation7 69 (by rfl)).trans ((lex_skipped s permutation7 68 69 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation7 68) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation7 68 by rw [image7_eq]; rfl))

theorem lex_7_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3607) (Sat.Literal.pos 3606) (Sat.Literal.pos 68) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation7 68 (assignment s)
    (Sat.Literal.pos 3607) (Sat.Literal.pos 3606) (Sat.Literal.pos 68) (Sat.Literal.pos 136) (positive_of_descriptor s 3607 (.lex permutation7 68) (by rfl)) (lex_7_68_prefix s) (positive_select s 68) (lex_7_68_image s)

theorem lex_7_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.pos 68), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation7 68 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3606) (Sat.Literal.pos 68) (Sat.Literal.pos 136) (lex_7_68_prefix s) (positive_select s 68) (lex_7_68_image s)

theorem lex_7_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.pos 3606)] :=
  (lex_7_68_gate s).prop _ (List.Mem.head _)

theorem lex_7_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.neg 68), (Sat.Literal.pos 136)] :=
  (lex_7_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.pos 68), (Sat.Literal.neg 136)] :=
  (lex_7_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.neg 68), (Sat.Literal.neg 136), (Sat.Literal.pos 3607)] :=
  (lex_7_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3606), (Sat.Literal.pos 68), (Sat.Literal.pos 136), (Sat.Literal.pos 3607)] :=
  (lex_7_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3607) = lexBefore s permutation7 67 := by
  exact (positive_lex_of_descriptor s 3607 permutation7 68 (by rfl)).trans ((lex_skipped s permutation7 67 68 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation7 67) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation7 67 by rw [image7_eq]; rfl))

theorem lex_7_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3608) (Sat.Literal.pos 3607) (Sat.Literal.pos 67) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation7 67 (assignment s)
    (Sat.Literal.pos 3608) (Sat.Literal.pos 3607) (Sat.Literal.pos 67) (Sat.Literal.pos 134) (positive_of_descriptor s 3608 (.lex permutation7 67) (by rfl)) (lex_7_67_prefix s) (positive_select s 67) (lex_7_67_image s)

theorem lex_7_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.pos 67), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation7 67 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3607) (Sat.Literal.pos 67) (Sat.Literal.pos 134) (lex_7_67_prefix s) (positive_select s 67) (lex_7_67_image s)

theorem lex_7_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.pos 3607)] :=
  (lex_7_67_gate s).prop _ (List.Mem.head _)

theorem lex_7_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.neg 67), (Sat.Literal.pos 134)] :=
  (lex_7_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.pos 67), (Sat.Literal.neg 134)] :=
  (lex_7_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.neg 67), (Sat.Literal.neg 134), (Sat.Literal.pos 3608)] :=
  (lex_7_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3607), (Sat.Literal.pos 67), (Sat.Literal.pos 134), (Sat.Literal.pos 3608)] :=
  (lex_7_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3608) = lexBefore s permutation7 66 := by
  exact (positive_lex_of_descriptor s 3608 permutation7 67 (by rfl)).trans ((lex_skipped s permutation7 66 67 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation7 66) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation7 66 by rw [image7_eq]; rfl))

theorem lex_7_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3609) (Sat.Literal.pos 3608) (Sat.Literal.pos 66) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation7 66 (assignment s)
    (Sat.Literal.pos 3609) (Sat.Literal.pos 3608) (Sat.Literal.pos 66) (Sat.Literal.pos 132) (positive_of_descriptor s 3609 (.lex permutation7 66) (by rfl)) (lex_7_66_prefix s) (positive_select s 66) (lex_7_66_image s)

theorem lex_7_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.pos 66), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation7 66 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3608) (Sat.Literal.pos 66) (Sat.Literal.pos 132) (lex_7_66_prefix s) (positive_select s 66) (lex_7_66_image s)

theorem lex_7_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.pos 3608)] :=
  (lex_7_66_gate s).prop _ (List.Mem.head _)

theorem lex_7_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.neg 66), (Sat.Literal.pos 132)] :=
  (lex_7_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.pos 66), (Sat.Literal.neg 132)] :=
  (lex_7_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.neg 66), (Sat.Literal.neg 132), (Sat.Literal.pos 3609)] :=
  (lex_7_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3608), (Sat.Literal.pos 66), (Sat.Literal.pos 132), (Sat.Literal.pos 3609)] :=
  (lex_7_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3609) = lexBefore s permutation7 65 := by
  exact (positive_lex_of_descriptor s 3609 permutation7 66 (by rfl)).trans ((lex_skipped s permutation7 65 66 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation7 65) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation7 65 by rw [image7_eq]; rfl))

theorem lex_7_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3610) (Sat.Literal.pos 3609) (Sat.Literal.pos 65) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation7 65 (assignment s)
    (Sat.Literal.pos 3610) (Sat.Literal.pos 3609) (Sat.Literal.pos 65) (Sat.Literal.pos 130) (positive_of_descriptor s 3610 (.lex permutation7 65) (by rfl)) (lex_7_65_prefix s) (positive_select s 65) (lex_7_65_image s)

theorem lex_7_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.pos 65), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation7 65 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3609) (Sat.Literal.pos 65) (Sat.Literal.pos 130) (lex_7_65_prefix s) (positive_select s 65) (lex_7_65_image s)

theorem lex_7_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.pos 3609)] :=
  (lex_7_65_gate s).prop _ (List.Mem.head _)

theorem lex_7_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.neg 65), (Sat.Literal.pos 130)] :=
  (lex_7_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.pos 65), (Sat.Literal.neg 130)] :=
  (lex_7_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.neg 65), (Sat.Literal.neg 130), (Sat.Literal.pos 3610)] :=
  (lex_7_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3609), (Sat.Literal.pos 65), (Sat.Literal.pos 130), (Sat.Literal.pos 3610)] :=
  (lex_7_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3610) = lexBefore s permutation7 64 := by
  exact (positive_lex_of_descriptor s 3610 permutation7 65 (by rfl)).trans ((lex_skipped s permutation7 64 65 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation7 64) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation7 64 by rw [image7_eq]; rfl))

theorem lex_7_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3611) (Sat.Literal.pos 3610) (Sat.Literal.pos 64) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation7 64 (assignment s)
    (Sat.Literal.pos 3611) (Sat.Literal.pos 3610) (Sat.Literal.pos 64) (Sat.Literal.pos 128) (positive_of_descriptor s 3611 (.lex permutation7 64) (by rfl)) (lex_7_64_prefix s) (positive_select s 64) (lex_7_64_image s)

theorem lex_7_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.pos 64), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation7 64 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3610) (Sat.Literal.pos 64) (Sat.Literal.pos 128) (lex_7_64_prefix s) (positive_select s 64) (lex_7_64_image s)

theorem lex_7_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.pos 3610)] :=
  (lex_7_64_gate s).prop _ (List.Mem.head _)

theorem lex_7_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.neg 64), (Sat.Literal.pos 128)] :=
  (lex_7_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.pos 64), (Sat.Literal.neg 128)] :=
  (lex_7_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.neg 64), (Sat.Literal.neg 128), (Sat.Literal.pos 3611)] :=
  (lex_7_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3610), (Sat.Literal.pos 64), (Sat.Literal.pos 128), (Sat.Literal.pos 3611)] :=
  (lex_7_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3611) = lexBefore s permutation7 63 := by
  exact (positive_lex_of_descriptor s 3611 permutation7 64 (by rfl)).trans ((lex_skipped s permutation7 63 64 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation7 63) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation7 63 by rw [image7_eq]; rfl))

theorem lex_7_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3612) (Sat.Literal.pos 3611) (Sat.Literal.pos 63) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation7 63 (assignment s)
    (Sat.Literal.pos 3612) (Sat.Literal.pos 3611) (Sat.Literal.pos 63) (Sat.Literal.pos 126) (positive_of_descriptor s 3612 (.lex permutation7 63) (by rfl)) (lex_7_63_prefix s) (positive_select s 63) (lex_7_63_image s)

theorem lex_7_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.pos 63), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation7 63 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3611) (Sat.Literal.pos 63) (Sat.Literal.pos 126) (lex_7_63_prefix s) (positive_select s 63) (lex_7_63_image s)

theorem lex_7_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.pos 3611)] :=
  (lex_7_63_gate s).prop _ (List.Mem.head _)

theorem lex_7_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.neg 63), (Sat.Literal.pos 126)] :=
  (lex_7_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.pos 63), (Sat.Literal.neg 126)] :=
  (lex_7_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.neg 63), (Sat.Literal.neg 126), (Sat.Literal.pos 3612)] :=
  (lex_7_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3611), (Sat.Literal.pos 63), (Sat.Literal.pos 126), (Sat.Literal.pos 3612)] :=
  (lex_7_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3612) = lexBefore s permutation7 62 := by
  exact (positive_lex_of_descriptor s 3612 permutation7 63 (by rfl)).trans ((lex_skipped s permutation7 62 63 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation7 62) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation7 62 by rw [image7_eq]; rfl))

theorem lex_7_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3613) (Sat.Literal.pos 3612) (Sat.Literal.pos 62) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation7 62 (assignment s)
    (Sat.Literal.pos 3613) (Sat.Literal.pos 3612) (Sat.Literal.pos 62) (Sat.Literal.pos 124) (positive_of_descriptor s 3613 (.lex permutation7 62) (by rfl)) (lex_7_62_prefix s) (positive_select s 62) (lex_7_62_image s)

theorem lex_7_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.pos 62), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation7 62 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3612) (Sat.Literal.pos 62) (Sat.Literal.pos 124) (lex_7_62_prefix s) (positive_select s 62) (lex_7_62_image s)

theorem lex_7_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.pos 3612)] :=
  (lex_7_62_gate s).prop _ (List.Mem.head _)

theorem lex_7_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.neg 62), (Sat.Literal.pos 124)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.pos 62), (Sat.Literal.neg 124)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.neg 62), (Sat.Literal.neg 124), (Sat.Literal.pos 3613)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3612), (Sat.Literal.pos 62), (Sat.Literal.pos 124), (Sat.Literal.pos 3613)] :=
  (lex_7_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3613) = lexBefore s permutation7 61 := by
  exact (positive_lex_of_descriptor s 3613 permutation7 62 (by rfl)).trans ((lex_skipped s permutation7 61 62 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation7 61) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation7 61 by rw [image7_eq]; rfl))

theorem lex_7_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3614) (Sat.Literal.pos 3613) (Sat.Literal.pos 61) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation7 61 (assignment s)
    (Sat.Literal.pos 3614) (Sat.Literal.pos 3613) (Sat.Literal.pos 61) (Sat.Literal.pos 122) (positive_of_descriptor s 3614 (.lex permutation7 61) (by rfl)) (lex_7_61_prefix s) (positive_select s 61) (lex_7_61_image s)

theorem lex_7_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.pos 61), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation7 61 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3613) (Sat.Literal.pos 61) (Sat.Literal.pos 122) (lex_7_61_prefix s) (positive_select s 61) (lex_7_61_image s)

theorem lex_7_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.pos 3613)] :=
  (lex_7_61_gate s).prop _ (List.Mem.head _)

theorem lex_7_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.neg 61), (Sat.Literal.pos 122)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.pos 61), (Sat.Literal.neg 122)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.neg 61), (Sat.Literal.neg 122), (Sat.Literal.pos 3614)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3613), (Sat.Literal.pos 61), (Sat.Literal.pos 122), (Sat.Literal.pos 3614)] :=
  (lex_7_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3614) = lexBefore s permutation7 60 := by
  exact (positive_lex_of_descriptor s 3614 permutation7 61 (by rfl)).trans ((lex_skipped s permutation7 60 61 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation7 60) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation7 60 by rw [image7_eq]; rfl))

theorem lex_7_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3615) (Sat.Literal.pos 3614) (Sat.Literal.pos 60) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation7 60 (assignment s)
    (Sat.Literal.pos 3615) (Sat.Literal.pos 3614) (Sat.Literal.pos 60) (Sat.Literal.pos 120) (positive_of_descriptor s 3615 (.lex permutation7 60) (by rfl)) (lex_7_60_prefix s) (positive_select s 60) (lex_7_60_image s)

theorem lex_7_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.pos 60), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation7 60 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3614) (Sat.Literal.pos 60) (Sat.Literal.pos 120) (lex_7_60_prefix s) (positive_select s 60) (lex_7_60_image s)

theorem lex_7_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.pos 3614)] :=
  (lex_7_60_gate s).prop _ (List.Mem.head _)

theorem lex_7_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.neg 60), (Sat.Literal.pos 120)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.pos 60), (Sat.Literal.neg 120)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.neg 60), (Sat.Literal.neg 120), (Sat.Literal.pos 3615)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3614), (Sat.Literal.pos 60), (Sat.Literal.pos 120), (Sat.Literal.pos 3615)] :=
  (lex_7_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3615) = lexBefore s permutation7 59 := by
  exact (positive_lex_of_descriptor s 3615 permutation7 60 (by rfl)).trans ((lex_skipped s permutation7 59 60 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation7 59) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation7 59 by rw [image7_eq]; rfl))

theorem lex_7_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3616) (Sat.Literal.pos 3615) (Sat.Literal.pos 59) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation7 59 (assignment s)
    (Sat.Literal.pos 3616) (Sat.Literal.pos 3615) (Sat.Literal.pos 59) (Sat.Literal.pos 118) (positive_of_descriptor s 3616 (.lex permutation7 59) (by rfl)) (lex_7_59_prefix s) (positive_select s 59) (lex_7_59_image s)

theorem lex_7_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.pos 59), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation7 59 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3615) (Sat.Literal.pos 59) (Sat.Literal.pos 118) (lex_7_59_prefix s) (positive_select s 59) (lex_7_59_image s)

theorem lex_7_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.pos 3615)] :=
  (lex_7_59_gate s).prop _ (List.Mem.head _)

theorem lex_7_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.neg 59), (Sat.Literal.pos 118)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.pos 59), (Sat.Literal.neg 118)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.neg 59), (Sat.Literal.neg 118), (Sat.Literal.pos 3616)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3615), (Sat.Literal.pos 59), (Sat.Literal.pos 118), (Sat.Literal.pos 3616)] :=
  (lex_7_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3616) = lexBefore s permutation7 58 := by
  exact (positive_lex_of_descriptor s 3616 permutation7 59 (by rfl)).trans ((lex_skipped s permutation7 58 59 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation7 58) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation7 58 by rw [image7_eq]; rfl))

theorem lex_7_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3617) (Sat.Literal.pos 3616) (Sat.Literal.pos 58) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation7 58 (assignment s)
    (Sat.Literal.pos 3617) (Sat.Literal.pos 3616) (Sat.Literal.pos 58) (Sat.Literal.pos 116) (positive_of_descriptor s 3617 (.lex permutation7 58) (by rfl)) (lex_7_58_prefix s) (positive_select s 58) (lex_7_58_image s)

theorem lex_7_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.pos 58), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation7 58 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3616) (Sat.Literal.pos 58) (Sat.Literal.pos 116) (lex_7_58_prefix s) (positive_select s 58) (lex_7_58_image s)

theorem lex_7_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.pos 3616)] :=
  (lex_7_58_gate s).prop _ (List.Mem.head _)

theorem lex_7_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.neg 58), (Sat.Literal.pos 116)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.pos 58), (Sat.Literal.neg 116)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.neg 58), (Sat.Literal.neg 116), (Sat.Literal.pos 3617)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3616), (Sat.Literal.pos 58), (Sat.Literal.pos 116), (Sat.Literal.pos 3617)] :=
  (lex_7_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3617) = lexBefore s permutation7 57 := by
  exact (positive_lex_of_descriptor s 3617 permutation7 58 (by rfl)).trans ((lex_skipped s permutation7 57 58 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation7 57) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation7 57 by rw [image7_eq]; rfl))

theorem lex_7_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3618) (Sat.Literal.pos 3617) (Sat.Literal.pos 57) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation7 57 (assignment s)
    (Sat.Literal.pos 3618) (Sat.Literal.pos 3617) (Sat.Literal.pos 57) (Sat.Literal.pos 114) (positive_of_descriptor s 3618 (.lex permutation7 57) (by rfl)) (lex_7_57_prefix s) (positive_select s 57) (lex_7_57_image s)

theorem lex_7_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.pos 57), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation7 57 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3617) (Sat.Literal.pos 57) (Sat.Literal.pos 114) (lex_7_57_prefix s) (positive_select s 57) (lex_7_57_image s)

theorem lex_7_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.pos 3617)] :=
  (lex_7_57_gate s).prop _ (List.Mem.head _)

theorem lex_7_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.neg 57), (Sat.Literal.pos 114)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.pos 57), (Sat.Literal.neg 114)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.neg 57), (Sat.Literal.neg 114), (Sat.Literal.pos 3618)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3617), (Sat.Literal.pos 57), (Sat.Literal.pos 114), (Sat.Literal.pos 3618)] :=
  (lex_7_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3618) = lexBefore s permutation7 56 := by
  exact (positive_lex_of_descriptor s 3618 permutation7 57 (by rfl)).trans ((lex_skipped s permutation7 56 57 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation7 56) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation7 56 by rw [image7_eq]; rfl))

theorem lex_7_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3619) (Sat.Literal.pos 3618) (Sat.Literal.pos 56) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation7 56 (assignment s)
    (Sat.Literal.pos 3619) (Sat.Literal.pos 3618) (Sat.Literal.pos 56) (Sat.Literal.pos 112) (positive_of_descriptor s 3619 (.lex permutation7 56) (by rfl)) (lex_7_56_prefix s) (positive_select s 56) (lex_7_56_image s)

theorem lex_7_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.pos 56), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation7 56 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3618) (Sat.Literal.pos 56) (Sat.Literal.pos 112) (lex_7_56_prefix s) (positive_select s 56) (lex_7_56_image s)

theorem lex_7_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.pos 3618)] :=
  (lex_7_56_gate s).prop _ (List.Mem.head _)

theorem lex_7_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.neg 56), (Sat.Literal.pos 112)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.pos 56), (Sat.Literal.neg 112)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.neg 56), (Sat.Literal.neg 112), (Sat.Literal.pos 3619)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3618), (Sat.Literal.pos 56), (Sat.Literal.pos 112), (Sat.Literal.pos 3619)] :=
  (lex_7_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3619) = lexBefore s permutation7 55 := by
  exact (positive_lex_of_descriptor s 3619 permutation7 56 (by rfl)).trans ((lex_skipped s permutation7 55 56 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation7 55) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation7 55 by rw [image7_eq]; rfl))

theorem lex_7_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3620) (Sat.Literal.pos 3619) (Sat.Literal.pos 55) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation7 55 (assignment s)
    (Sat.Literal.pos 3620) (Sat.Literal.pos 3619) (Sat.Literal.pos 55) (Sat.Literal.pos 110) (positive_of_descriptor s 3620 (.lex permutation7 55) (by rfl)) (lex_7_55_prefix s) (positive_select s 55) (lex_7_55_image s)

theorem lex_7_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.pos 55), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation7 55 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3619) (Sat.Literal.pos 55) (Sat.Literal.pos 110) (lex_7_55_prefix s) (positive_select s 55) (lex_7_55_image s)

theorem lex_7_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.pos 3619)] :=
  (lex_7_55_gate s).prop _ (List.Mem.head _)

theorem lex_7_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.neg 55), (Sat.Literal.pos 110)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.pos 55), (Sat.Literal.neg 110)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.neg 55), (Sat.Literal.neg 110), (Sat.Literal.pos 3620)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3619), (Sat.Literal.pos 55), (Sat.Literal.pos 110), (Sat.Literal.pos 3620)] :=
  (lex_7_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3620) = lexBefore s permutation7 54 := by
  exact (positive_lex_of_descriptor s 3620 permutation7 55 (by rfl)).trans ((lex_skipped s permutation7 54 55 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation7 54) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation7 54 by rw [image7_eq]; rfl))

theorem lex_7_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3621) (Sat.Literal.pos 3620) (Sat.Literal.pos 54) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation7 54 (assignment s)
    (Sat.Literal.pos 3621) (Sat.Literal.pos 3620) (Sat.Literal.pos 54) (Sat.Literal.pos 108) (positive_of_descriptor s 3621 (.lex permutation7 54) (by rfl)) (lex_7_54_prefix s) (positive_select s 54) (lex_7_54_image s)

theorem lex_7_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.pos 54), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation7 54 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3620) (Sat.Literal.pos 54) (Sat.Literal.pos 108) (lex_7_54_prefix s) (positive_select s 54) (lex_7_54_image s)

theorem lex_7_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.pos 3620)] :=
  (lex_7_54_gate s).prop _ (List.Mem.head _)

theorem lex_7_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.neg 54), (Sat.Literal.pos 108)] :=
  (lex_7_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.pos 54), (Sat.Literal.neg 108)] :=
  (lex_7_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.neg 54), (Sat.Literal.neg 108), (Sat.Literal.pos 3621)] :=
  (lex_7_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3620), (Sat.Literal.pos 54), (Sat.Literal.pos 108), (Sat.Literal.pos 3621)] :=
  (lex_7_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3621) = lexBefore s permutation7 53 := by
  exact (positive_lex_of_descriptor s 3621 permutation7 54 (by rfl)).trans ((lex_skipped s permutation7 53 54 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation7 53) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation7 53 by rw [image7_eq]; rfl))

theorem lex_7_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3622) (Sat.Literal.pos 3621) (Sat.Literal.pos 53) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation7 53 (assignment s)
    (Sat.Literal.pos 3622) (Sat.Literal.pos 3621) (Sat.Literal.pos 53) (Sat.Literal.pos 106) (positive_of_descriptor s 3622 (.lex permutation7 53) (by rfl)) (lex_7_53_prefix s) (positive_select s 53) (lex_7_53_image s)

theorem lex_7_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.pos 53), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation7 53 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3621) (Sat.Literal.pos 53) (Sat.Literal.pos 106) (lex_7_53_prefix s) (positive_select s 53) (lex_7_53_image s)

theorem lex_7_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.pos 3621)] :=
  (lex_7_53_gate s).prop _ (List.Mem.head _)

theorem lex_7_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.neg 53), (Sat.Literal.pos 106)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.pos 53), (Sat.Literal.neg 106)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.neg 53), (Sat.Literal.neg 106), (Sat.Literal.pos 3622)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3621), (Sat.Literal.pos 53), (Sat.Literal.pos 106), (Sat.Literal.pos 3622)] :=
  (lex_7_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3622) = lexBefore s permutation7 52 := by
  exact (positive_lex_of_descriptor s 3622 permutation7 53 (by rfl)).trans ((lex_skipped s permutation7 52 53 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation7 52) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation7 52 by rw [image7_eq]; rfl))

theorem lex_7_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3623) (Sat.Literal.pos 3622) (Sat.Literal.pos 52) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation7 52 (assignment s)
    (Sat.Literal.pos 3623) (Sat.Literal.pos 3622) (Sat.Literal.pos 52) (Sat.Literal.pos 104) (positive_of_descriptor s 3623 (.lex permutation7 52) (by rfl)) (lex_7_52_prefix s) (positive_select s 52) (lex_7_52_image s)

theorem lex_7_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.pos 52), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation7 52 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3622) (Sat.Literal.pos 52) (Sat.Literal.pos 104) (lex_7_52_prefix s) (positive_select s 52) (lex_7_52_image s)

theorem lex_7_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.pos 3622)] :=
  (lex_7_52_gate s).prop _ (List.Mem.head _)

theorem lex_7_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.neg 52), (Sat.Literal.pos 104)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.pos 52), (Sat.Literal.neg 104)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.neg 52), (Sat.Literal.neg 104), (Sat.Literal.pos 3623)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3622), (Sat.Literal.pos 52), (Sat.Literal.pos 104), (Sat.Literal.pos 3623)] :=
  (lex_7_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3623) = lexBefore s permutation7 51 := by
  exact (positive_lex_of_descriptor s 3623 permutation7 52 (by rfl)).trans ((lex_skipped s permutation7 51 52 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation7 51) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation7 51 by rw [image7_eq]; rfl))

theorem lex_7_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3624) (Sat.Literal.pos 3623) (Sat.Literal.pos 51) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation7 51 (assignment s)
    (Sat.Literal.pos 3624) (Sat.Literal.pos 3623) (Sat.Literal.pos 51) (Sat.Literal.pos 102) (positive_of_descriptor s 3624 (.lex permutation7 51) (by rfl)) (lex_7_51_prefix s) (positive_select s 51) (lex_7_51_image s)

theorem lex_7_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.pos 51), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation7 51 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3623) (Sat.Literal.pos 51) (Sat.Literal.pos 102) (lex_7_51_prefix s) (positive_select s 51) (lex_7_51_image s)

theorem lex_7_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.pos 3623)] :=
  (lex_7_51_gate s).prop _ (List.Mem.head _)

theorem lex_7_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.neg 51), (Sat.Literal.pos 102)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.pos 51), (Sat.Literal.neg 102)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.neg 51), (Sat.Literal.neg 102), (Sat.Literal.pos 3624)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3623), (Sat.Literal.pos 51), (Sat.Literal.pos 102), (Sat.Literal.pos 3624)] :=
  (lex_7_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_7_150_gate

end Crown.CertificateData
