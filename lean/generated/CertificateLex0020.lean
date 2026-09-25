import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_11_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4524) = lexBefore s permutation11 150 := by
  exact (positive_lex_of_descriptor s 4524 permutation11 151 (by rfl)).trans ((lex_skipped s permutation11 150 151 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation11 150) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation11 150 by rw [image11_eq]; rfl))

theorem lex_11_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4525) (Sat.Literal.pos 4524) (Sat.Literal.pos 150) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation11 150 (assignment s)
    (Sat.Literal.pos 4525) (Sat.Literal.pos 4524) (Sat.Literal.pos 150) (Sat.Literal.pos 210) (positive_of_descriptor s 4525 (.lex permutation11 150) (by rfl)) (lex_11_150_prefix s) (positive_select s 150) (lex_11_150_image s)

theorem lex_11_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.pos 150), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation11 150 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4524) (Sat.Literal.pos 150) (Sat.Literal.pos 210) (lex_11_150_prefix s) (positive_select s 150) (lex_11_150_image s)

theorem lex_11_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.pos 4524)] :=
  (lex_11_150_gate s).prop _ (List.Mem.head _)

theorem lex_11_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.neg 150), (Sat.Literal.pos 210)] :=
  (lex_11_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.pos 150), (Sat.Literal.neg 210)] :=
  (lex_11_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.neg 150), (Sat.Literal.neg 210), (Sat.Literal.pos 4525)] :=
  (lex_11_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.pos 150), (Sat.Literal.pos 210), (Sat.Literal.pos 4525)] :=
  (lex_11_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4525) = lexBefore s permutation11 149 := by
  exact (positive_lex_of_descriptor s 4525 permutation11 150 (by rfl)).trans ((lex_skipped s permutation11 149 150 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation11 149) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation11 149 by rw [image11_eq]; rfl))

theorem lex_11_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4526) (Sat.Literal.pos 4525) (Sat.Literal.pos 149) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation11 149 (assignment s)
    (Sat.Literal.pos 4526) (Sat.Literal.pos 4525) (Sat.Literal.pos 149) (Sat.Literal.pos 178) (positive_of_descriptor s 4526 (.lex permutation11 149) (by rfl)) (lex_11_149_prefix s) (positive_select s 149) (lex_11_149_image s)

theorem lex_11_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.pos 149), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation11 149 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4525) (Sat.Literal.pos 149) (Sat.Literal.pos 178) (lex_11_149_prefix s) (positive_select s 149) (lex_11_149_image s)

theorem lex_11_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.pos 4525)] :=
  (lex_11_149_gate s).prop _ (List.Mem.head _)

theorem lex_11_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.neg 149), (Sat.Literal.pos 178)] :=
  (lex_11_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.pos 149), (Sat.Literal.neg 178)] :=
  (lex_11_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.neg 149), (Sat.Literal.neg 178), (Sat.Literal.pos 4526)] :=
  (lex_11_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4525), (Sat.Literal.pos 149), (Sat.Literal.pos 178), (Sat.Literal.pos 4526)] :=
  (lex_11_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4526) = lexBefore s permutation11 148 := by
  exact (positive_lex_of_descriptor s 4526 permutation11 149 (by rfl)).trans ((lex_skipped s permutation11 148 149 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation11 148) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation11 148 by rw [image11_eq]; rfl))

theorem lex_11_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4527) (Sat.Literal.pos 4526) (Sat.Literal.pos 148) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation11 148 (assignment s)
    (Sat.Literal.pos 4527) (Sat.Literal.pos 4526) (Sat.Literal.pos 148) (Sat.Literal.pos 146) (positive_of_descriptor s 4527 (.lex permutation11 148) (by rfl)) (lex_11_148_prefix s) (positive_select s 148) (lex_11_148_image s)

theorem lex_11_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.pos 148), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation11 148 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4526) (Sat.Literal.pos 148) (Sat.Literal.pos 146) (lex_11_148_prefix s) (positive_select s 148) (lex_11_148_image s)

theorem lex_11_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.pos 4526)] :=
  (lex_11_148_gate s).prop _ (List.Mem.head _)

theorem lex_11_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.neg 148), (Sat.Literal.pos 146)] :=
  (lex_11_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.pos 148), (Sat.Literal.neg 146)] :=
  (lex_11_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.neg 148), (Sat.Literal.neg 146), (Sat.Literal.pos 4527)] :=
  (lex_11_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4526), (Sat.Literal.pos 148), (Sat.Literal.pos 146), (Sat.Literal.pos 4527)] :=
  (lex_11_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4527) = lexBefore s permutation11 147 := by
  exact (positive_lex_of_descriptor s 4527 permutation11 148 (by rfl)).trans ((lex_skipped s permutation11 147 148 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation11 147) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation11 147 by rw [image11_eq]; rfl))

theorem lex_11_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4528) (Sat.Literal.pos 4527) (Sat.Literal.pos 147) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation11 147 (assignment s)
    (Sat.Literal.pos 4528) (Sat.Literal.pos 4527) (Sat.Literal.pos 147) (Sat.Literal.pos 114) (positive_of_descriptor s 4528 (.lex permutation11 147) (by rfl)) (lex_11_147_prefix s) (positive_select s 147) (lex_11_147_image s)

theorem lex_11_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.pos 147), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation11 147 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4527) (Sat.Literal.pos 147) (Sat.Literal.pos 114) (lex_11_147_prefix s) (positive_select s 147) (lex_11_147_image s)

theorem lex_11_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.pos 4527)] :=
  (lex_11_147_gate s).prop _ (List.Mem.head _)

theorem lex_11_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.neg 147), (Sat.Literal.pos 114)] :=
  (lex_11_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.pos 147), (Sat.Literal.neg 114)] :=
  (lex_11_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.neg 147), (Sat.Literal.neg 114), (Sat.Literal.pos 4528)] :=
  (lex_11_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4527), (Sat.Literal.pos 147), (Sat.Literal.pos 114), (Sat.Literal.pos 4528)] :=
  (lex_11_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4528) = lexBefore s permutation11 146 := by
  exact (positive_lex_of_descriptor s 4528 permutation11 147 (by rfl)).trans ((lex_skipped s permutation11 146 147 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation11 146) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation11 146 by rw [image11_eq]; rfl))

theorem lex_11_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4529) (Sat.Literal.pos 4528) (Sat.Literal.pos 146) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation11 146 (assignment s)
    (Sat.Literal.pos 4529) (Sat.Literal.pos 4528) (Sat.Literal.pos 146) (Sat.Literal.pos 82) (positive_of_descriptor s 4529 (.lex permutation11 146) (by rfl)) (lex_11_146_prefix s) (positive_select s 146) (lex_11_146_image s)

theorem lex_11_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.pos 146), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation11 146 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4528) (Sat.Literal.pos 146) (Sat.Literal.pos 82) (lex_11_146_prefix s) (positive_select s 146) (lex_11_146_image s)

theorem lex_11_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.pos 4528)] :=
  (lex_11_146_gate s).prop _ (List.Mem.head _)

theorem lex_11_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.neg 146), (Sat.Literal.pos 82)] :=
  (lex_11_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.pos 146), (Sat.Literal.neg 82)] :=
  (lex_11_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.neg 146), (Sat.Literal.neg 82), (Sat.Literal.pos 4529)] :=
  (lex_11_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4528), (Sat.Literal.pos 146), (Sat.Literal.pos 82), (Sat.Literal.pos 4529)] :=
  (lex_11_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4529) = lexBefore s permutation11 145 := by
  exact (positive_lex_of_descriptor s 4529 permutation11 146 (by rfl)).trans ((lex_skipped s permutation11 145 146 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation11 145) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation11 145 by rw [image11_eq]; rfl))

theorem lex_11_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4530) (Sat.Literal.pos 4529) (Sat.Literal.pos 145) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation11 145 (assignment s)
    (Sat.Literal.pos 4530) (Sat.Literal.pos 4529) (Sat.Literal.pos 145) (Sat.Literal.pos 50) (positive_of_descriptor s 4530 (.lex permutation11 145) (by rfl)) (lex_11_145_prefix s) (positive_select s 145) (lex_11_145_image s)

theorem lex_11_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.pos 145), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation11 145 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4529) (Sat.Literal.pos 145) (Sat.Literal.pos 50) (lex_11_145_prefix s) (positive_select s 145) (lex_11_145_image s)

theorem lex_11_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.pos 4529)] :=
  (lex_11_145_gate s).prop _ (List.Mem.head _)

theorem lex_11_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.neg 145), (Sat.Literal.pos 50)] :=
  (lex_11_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.pos 145), (Sat.Literal.neg 50)] :=
  (lex_11_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.neg 145), (Sat.Literal.neg 50), (Sat.Literal.pos 4530)] :=
  (lex_11_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4529), (Sat.Literal.pos 145), (Sat.Literal.pos 50), (Sat.Literal.pos 4530)] :=
  (lex_11_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4530) = lexBefore s permutation11 144 := by
  exact (positive_lex_of_descriptor s 4530 permutation11 145 (by rfl)).trans ((lex_skipped s permutation11 144 145 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation11 144) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation11 144 by rw [image11_eq]; rfl))

theorem lex_11_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4531) (Sat.Literal.pos 4530) (Sat.Literal.pos 144) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation11 144 (assignment s)
    (Sat.Literal.pos 4531) (Sat.Literal.pos 4530) (Sat.Literal.pos 144) (Sat.Literal.pos 18) (positive_of_descriptor s 4531 (.lex permutation11 144) (by rfl)) (lex_11_144_prefix s) (positive_select s 144) (lex_11_144_image s)

theorem lex_11_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.pos 144), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation11 144 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4530) (Sat.Literal.pos 144) (Sat.Literal.pos 18) (lex_11_144_prefix s) (positive_select s 144) (lex_11_144_image s)

theorem lex_11_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.pos 4530)] :=
  (lex_11_144_gate s).prop _ (List.Mem.head _)

theorem lex_11_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.neg 144), (Sat.Literal.pos 18)] :=
  (lex_11_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.pos 144), (Sat.Literal.neg 18)] :=
  (lex_11_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.neg 144), (Sat.Literal.neg 18), (Sat.Literal.pos 4531)] :=
  (lex_11_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4530), (Sat.Literal.pos 144), (Sat.Literal.pos 18), (Sat.Literal.pos 4531)] :=
  (lex_11_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4531) = lexBefore s permutation11 143 := by
  exact (positive_lex_of_descriptor s 4531 permutation11 144 (by rfl)).trans ((lex_skipped s permutation11 143 144 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation11 143) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation11 143 by rw [image11_eq]; rfl))

theorem lex_11_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4532) (Sat.Literal.pos 4531) (Sat.Literal.pos 143) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation11 143 (assignment s)
    (Sat.Literal.pos 4532) (Sat.Literal.pos 4531) (Sat.Literal.pos 143) (Sat.Literal.pos 241) (positive_of_descriptor s 4532 (.lex permutation11 143) (by rfl)) (lex_11_143_prefix s) (positive_select s 143) (lex_11_143_image s)

theorem lex_11_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.pos 143), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation11 143 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4531) (Sat.Literal.pos 143) (Sat.Literal.pos 241) (lex_11_143_prefix s) (positive_select s 143) (lex_11_143_image s)

theorem lex_11_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.pos 4531)] :=
  (lex_11_143_gate s).prop _ (List.Mem.head _)

theorem lex_11_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.neg 143), (Sat.Literal.pos 241)] :=
  (lex_11_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.pos 143), (Sat.Literal.neg 241)] :=
  (lex_11_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.neg 143), (Sat.Literal.neg 241), (Sat.Literal.pos 4532)] :=
  (lex_11_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4531), (Sat.Literal.pos 143), (Sat.Literal.pos 241), (Sat.Literal.pos 4532)] :=
  (lex_11_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4532) = lexBefore s permutation11 142 := by
  exact (positive_lex_of_descriptor s 4532 permutation11 143 (by rfl)).trans ((lex_skipped s permutation11 142 143 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation11 142) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation11 142 by rw [image11_eq]; rfl))

theorem lex_11_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4533) (Sat.Literal.pos 4532) (Sat.Literal.pos 142) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation11 142 (assignment s)
    (Sat.Literal.pos 4533) (Sat.Literal.pos 4532) (Sat.Literal.pos 142) (Sat.Literal.pos 209) (positive_of_descriptor s 4533 (.lex permutation11 142) (by rfl)) (lex_11_142_prefix s) (positive_select s 142) (lex_11_142_image s)

theorem lex_11_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.pos 142), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation11 142 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4532) (Sat.Literal.pos 142) (Sat.Literal.pos 209) (lex_11_142_prefix s) (positive_select s 142) (lex_11_142_image s)

theorem lex_11_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.pos 4532)] :=
  (lex_11_142_gate s).prop _ (List.Mem.head _)

theorem lex_11_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.neg 142), (Sat.Literal.pos 209)] :=
  (lex_11_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.pos 142), (Sat.Literal.neg 209)] :=
  (lex_11_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.neg 142), (Sat.Literal.neg 209), (Sat.Literal.pos 4533)] :=
  (lex_11_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4532), (Sat.Literal.pos 142), (Sat.Literal.pos 209), (Sat.Literal.pos 4533)] :=
  (lex_11_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4533) = lexBefore s permutation11 141 := by
  exact (positive_lex_of_descriptor s 4533 permutation11 142 (by rfl)).trans ((lex_skipped s permutation11 141 142 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation11 141) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation11 141 by rw [image11_eq]; rfl))

theorem lex_11_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4534) (Sat.Literal.pos 4533) (Sat.Literal.pos 141) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation11 141 (assignment s)
    (Sat.Literal.pos 4534) (Sat.Literal.pos 4533) (Sat.Literal.pos 141) (Sat.Literal.pos 177) (positive_of_descriptor s 4534 (.lex permutation11 141) (by rfl)) (lex_11_141_prefix s) (positive_select s 141) (lex_11_141_image s)

theorem lex_11_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.pos 141), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation11 141 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4533) (Sat.Literal.pos 141) (Sat.Literal.pos 177) (lex_11_141_prefix s) (positive_select s 141) (lex_11_141_image s)

theorem lex_11_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.pos 4533)] :=
  (lex_11_141_gate s).prop _ (List.Mem.head _)

theorem lex_11_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.neg 141), (Sat.Literal.pos 177)] :=
  (lex_11_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.pos 141), (Sat.Literal.neg 177)] :=
  (lex_11_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.neg 141), (Sat.Literal.neg 177), (Sat.Literal.pos 4534)] :=
  (lex_11_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4533), (Sat.Literal.pos 141), (Sat.Literal.pos 177), (Sat.Literal.pos 4534)] :=
  (lex_11_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4534) = lexBefore s permutation11 140 := by
  exact (positive_lex_of_descriptor s 4534 permutation11 141 (by rfl)).trans ((lex_skipped s permutation11 140 141 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation11 140) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation11 140 by rw [image11_eq]; rfl))

theorem lex_11_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4535) (Sat.Literal.pos 4534) (Sat.Literal.pos 140) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation11 140 (assignment s)
    (Sat.Literal.pos 4535) (Sat.Literal.pos 4534) (Sat.Literal.pos 140) (Sat.Literal.pos 145) (positive_of_descriptor s 4535 (.lex permutation11 140) (by rfl)) (lex_11_140_prefix s) (positive_select s 140) (lex_11_140_image s)

theorem lex_11_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.pos 140), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation11 140 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4534) (Sat.Literal.pos 140) (Sat.Literal.pos 145) (lex_11_140_prefix s) (positive_select s 140) (lex_11_140_image s)

theorem lex_11_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.pos 4534)] :=
  (lex_11_140_gate s).prop _ (List.Mem.head _)

theorem lex_11_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.neg 140), (Sat.Literal.pos 145)] :=
  (lex_11_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.pos 140), (Sat.Literal.neg 145)] :=
  (lex_11_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.neg 140), (Sat.Literal.neg 145), (Sat.Literal.pos 4535)] :=
  (lex_11_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4534), (Sat.Literal.pos 140), (Sat.Literal.pos 145), (Sat.Literal.pos 4535)] :=
  (lex_11_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4535) = lexBefore s permutation11 139 := by
  exact (positive_lex_of_descriptor s 4535 permutation11 140 (by rfl)).trans ((lex_skipped s permutation11 139 140 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation11 139) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation11 139 by rw [image11_eq]; rfl))

theorem lex_11_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4536) (Sat.Literal.pos 4535) (Sat.Literal.pos 139) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation11 139 (assignment s)
    (Sat.Literal.pos 4536) (Sat.Literal.pos 4535) (Sat.Literal.pos 139) (Sat.Literal.pos 113) (positive_of_descriptor s 4536 (.lex permutation11 139) (by rfl)) (lex_11_139_prefix s) (positive_select s 139) (lex_11_139_image s)

theorem lex_11_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.pos 139), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation11 139 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4535) (Sat.Literal.pos 139) (Sat.Literal.pos 113) (lex_11_139_prefix s) (positive_select s 139) (lex_11_139_image s)

theorem lex_11_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.pos 4535)] :=
  (lex_11_139_gate s).prop _ (List.Mem.head _)

theorem lex_11_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.neg 139), (Sat.Literal.pos 113)] :=
  (lex_11_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.pos 139), (Sat.Literal.neg 113)] :=
  (lex_11_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.neg 139), (Sat.Literal.neg 113), (Sat.Literal.pos 4536)] :=
  (lex_11_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4535), (Sat.Literal.pos 139), (Sat.Literal.pos 113), (Sat.Literal.pos 4536)] :=
  (lex_11_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4536) = lexBefore s permutation11 138 := by
  exact (positive_lex_of_descriptor s 4536 permutation11 139 (by rfl)).trans ((lex_skipped s permutation11 138 139 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation11 138) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation11 138 by rw [image11_eq]; rfl))

theorem lex_11_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4537) (Sat.Literal.pos 4536) (Sat.Literal.pos 138) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation11 138 (assignment s)
    (Sat.Literal.pos 4537) (Sat.Literal.pos 4536) (Sat.Literal.pos 138) (Sat.Literal.pos 81) (positive_of_descriptor s 4537 (.lex permutation11 138) (by rfl)) (lex_11_138_prefix s) (positive_select s 138) (lex_11_138_image s)

theorem lex_11_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.pos 138), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation11 138 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4536) (Sat.Literal.pos 138) (Sat.Literal.pos 81) (lex_11_138_prefix s) (positive_select s 138) (lex_11_138_image s)

theorem lex_11_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.pos 4536)] :=
  (lex_11_138_gate s).prop _ (List.Mem.head _)

theorem lex_11_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.neg 138), (Sat.Literal.pos 81)] :=
  (lex_11_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.pos 138), (Sat.Literal.neg 81)] :=
  (lex_11_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.neg 138), (Sat.Literal.neg 81), (Sat.Literal.pos 4537)] :=
  (lex_11_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4536), (Sat.Literal.pos 138), (Sat.Literal.pos 81), (Sat.Literal.pos 4537)] :=
  (lex_11_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4537) = lexBefore s permutation11 137 := by
  exact (positive_lex_of_descriptor s 4537 permutation11 138 (by rfl)).trans ((lex_skipped s permutation11 137 138 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation11 137) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation11 137 by rw [image11_eq]; rfl))

theorem lex_11_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4538) (Sat.Literal.pos 4537) (Sat.Literal.pos 137) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation11 137 (assignment s)
    (Sat.Literal.pos 4538) (Sat.Literal.pos 4537) (Sat.Literal.pos 137) (Sat.Literal.pos 49) (positive_of_descriptor s 4538 (.lex permutation11 137) (by rfl)) (lex_11_137_prefix s) (positive_select s 137) (lex_11_137_image s)

theorem lex_11_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.pos 137), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation11 137 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4537) (Sat.Literal.pos 137) (Sat.Literal.pos 49) (lex_11_137_prefix s) (positive_select s 137) (lex_11_137_image s)

theorem lex_11_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.pos 4537)] :=
  (lex_11_137_gate s).prop _ (List.Mem.head _)

theorem lex_11_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.neg 137), (Sat.Literal.pos 49)] :=
  (lex_11_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.pos 137), (Sat.Literal.neg 49)] :=
  (lex_11_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.neg 137), (Sat.Literal.neg 49), (Sat.Literal.pos 4538)] :=
  (lex_11_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4537), (Sat.Literal.pos 137), (Sat.Literal.pos 49), (Sat.Literal.pos 4538)] :=
  (lex_11_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4538) = lexBefore s permutation11 136 := by
  exact (positive_lex_of_descriptor s 4538 permutation11 137 (by rfl)).trans ((lex_skipped s permutation11 136 137 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation11 136) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation11 136 by rw [image11_eq]; rfl))

theorem lex_11_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4539) (Sat.Literal.pos 4538) (Sat.Literal.pos 136) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation11 136 (assignment s)
    (Sat.Literal.pos 4539) (Sat.Literal.pos 4538) (Sat.Literal.pos 136) (Sat.Literal.pos 17) (positive_of_descriptor s 4539 (.lex permutation11 136) (by rfl)) (lex_11_136_prefix s) (positive_select s 136) (lex_11_136_image s)

theorem lex_11_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.pos 136), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation11 136 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4538) (Sat.Literal.pos 136) (Sat.Literal.pos 17) (lex_11_136_prefix s) (positive_select s 136) (lex_11_136_image s)

theorem lex_11_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.pos 4538)] :=
  (lex_11_136_gate s).prop _ (List.Mem.head _)

theorem lex_11_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.neg 136), (Sat.Literal.pos 17)] :=
  (lex_11_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.pos 136), (Sat.Literal.neg 17)] :=
  (lex_11_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.neg 136), (Sat.Literal.neg 17), (Sat.Literal.pos 4539)] :=
  (lex_11_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4538), (Sat.Literal.pos 136), (Sat.Literal.pos 17), (Sat.Literal.pos 4539)] :=
  (lex_11_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4539) = lexBefore s permutation11 135 := by
  exact (positive_lex_of_descriptor s 4539 permutation11 136 (by rfl)).trans ((lex_skipped s permutation11 135 136 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation11 135) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation11 135 by rw [image11_eq]; rfl))

theorem lex_11_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4540) (Sat.Literal.pos 4539) (Sat.Literal.pos 135) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation11 135 (assignment s)
    (Sat.Literal.pos 4540) (Sat.Literal.pos 4539) (Sat.Literal.pos 135) (Sat.Literal.pos 240) (positive_of_descriptor s 4540 (.lex permutation11 135) (by rfl)) (lex_11_135_prefix s) (positive_select s 135) (lex_11_135_image s)

theorem lex_11_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.pos 135), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation11 135 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4539) (Sat.Literal.pos 135) (Sat.Literal.pos 240) (lex_11_135_prefix s) (positive_select s 135) (lex_11_135_image s)

theorem lex_11_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.pos 4539)] :=
  (lex_11_135_gate s).prop _ (List.Mem.head _)

theorem lex_11_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.neg 135), (Sat.Literal.pos 240)] :=
  (lex_11_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.pos 135), (Sat.Literal.neg 240)] :=
  (lex_11_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.neg 135), (Sat.Literal.neg 240), (Sat.Literal.pos 4540)] :=
  (lex_11_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4539), (Sat.Literal.pos 135), (Sat.Literal.pos 240), (Sat.Literal.pos 4540)] :=
  (lex_11_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4540) = lexBefore s permutation11 134 := by
  exact (positive_lex_of_descriptor s 4540 permutation11 135 (by rfl)).trans ((lex_skipped s permutation11 134 135 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation11 134) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation11 134 by rw [image11_eq]; rfl))

theorem lex_11_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4541) (Sat.Literal.pos 4540) (Sat.Literal.pos 134) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation11 134 (assignment s)
    (Sat.Literal.pos 4541) (Sat.Literal.pos 4540) (Sat.Literal.pos 134) (Sat.Literal.pos 208) (positive_of_descriptor s 4541 (.lex permutation11 134) (by rfl)) (lex_11_134_prefix s) (positive_select s 134) (lex_11_134_image s)

theorem lex_11_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.pos 134), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation11 134 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4540) (Sat.Literal.pos 134) (Sat.Literal.pos 208) (lex_11_134_prefix s) (positive_select s 134) (lex_11_134_image s)

theorem lex_11_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.pos 4540)] :=
  (lex_11_134_gate s).prop _ (List.Mem.head _)

theorem lex_11_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.neg 134), (Sat.Literal.pos 208)] :=
  (lex_11_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.pos 134), (Sat.Literal.neg 208)] :=
  (lex_11_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.neg 134), (Sat.Literal.neg 208), (Sat.Literal.pos 4541)] :=
  (lex_11_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4540), (Sat.Literal.pos 134), (Sat.Literal.pos 208), (Sat.Literal.pos 4541)] :=
  (lex_11_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4541) = lexBefore s permutation11 133 := by
  exact (positive_lex_of_descriptor s 4541 permutation11 134 (by rfl)).trans ((lex_skipped s permutation11 133 134 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation11 133) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation11 133 by rw [image11_eq]; rfl))

theorem lex_11_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4542) (Sat.Literal.pos 4541) (Sat.Literal.pos 133) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation11 133 (assignment s)
    (Sat.Literal.pos 4542) (Sat.Literal.pos 4541) (Sat.Literal.pos 133) (Sat.Literal.pos 176) (positive_of_descriptor s 4542 (.lex permutation11 133) (by rfl)) (lex_11_133_prefix s) (positive_select s 133) (lex_11_133_image s)

theorem lex_11_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.pos 133), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation11 133 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4541) (Sat.Literal.pos 133) (Sat.Literal.pos 176) (lex_11_133_prefix s) (positive_select s 133) (lex_11_133_image s)

theorem lex_11_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.pos 4541)] :=
  (lex_11_133_gate s).prop _ (List.Mem.head _)

theorem lex_11_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.neg 133), (Sat.Literal.pos 176)] :=
  (lex_11_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.pos 133), (Sat.Literal.neg 176)] :=
  (lex_11_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.neg 133), (Sat.Literal.neg 176), (Sat.Literal.pos 4542)] :=
  (lex_11_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4541), (Sat.Literal.pos 133), (Sat.Literal.pos 176), (Sat.Literal.pos 4542)] :=
  (lex_11_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4542) = lexBefore s permutation11 132 := by
  exact (positive_lex_of_descriptor s 4542 permutation11 133 (by rfl)).trans ((lex_skipped s permutation11 132 133 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation11 132) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation11 132 by rw [image11_eq]; rfl))

theorem lex_11_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4543) (Sat.Literal.pos 4542) (Sat.Literal.pos 132) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation11 132 (assignment s)
    (Sat.Literal.pos 4543) (Sat.Literal.pos 4542) (Sat.Literal.pos 132) (Sat.Literal.pos 144) (positive_of_descriptor s 4543 (.lex permutation11 132) (by rfl)) (lex_11_132_prefix s) (positive_select s 132) (lex_11_132_image s)

theorem lex_11_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.pos 132), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation11 132 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4542) (Sat.Literal.pos 132) (Sat.Literal.pos 144) (lex_11_132_prefix s) (positive_select s 132) (lex_11_132_image s)

theorem lex_11_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.pos 4542)] :=
  (lex_11_132_gate s).prop _ (List.Mem.head _)

theorem lex_11_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.neg 132), (Sat.Literal.pos 144)] :=
  (lex_11_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.pos 132), (Sat.Literal.neg 144)] :=
  (lex_11_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.neg 132), (Sat.Literal.neg 144), (Sat.Literal.pos 4543)] :=
  (lex_11_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4542), (Sat.Literal.pos 132), (Sat.Literal.pos 144), (Sat.Literal.pos 4543)] :=
  (lex_11_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4543) = lexBefore s permutation11 131 := by
  exact (positive_lex_of_descriptor s 4543 permutation11 132 (by rfl)).trans ((lex_skipped s permutation11 131 132 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation11 131) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation11 131 by rw [image11_eq]; rfl))

theorem lex_11_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4544) (Sat.Literal.pos 4543) (Sat.Literal.pos 131) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation11 131 (assignment s)
    (Sat.Literal.pos 4544) (Sat.Literal.pos 4543) (Sat.Literal.pos 131) (Sat.Literal.pos 112) (positive_of_descriptor s 4544 (.lex permutation11 131) (by rfl)) (lex_11_131_prefix s) (positive_select s 131) (lex_11_131_image s)

theorem lex_11_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.pos 131), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation11 131 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4543) (Sat.Literal.pos 131) (Sat.Literal.pos 112) (lex_11_131_prefix s) (positive_select s 131) (lex_11_131_image s)

theorem lex_11_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.pos 4543)] :=
  (lex_11_131_gate s).prop _ (List.Mem.head _)

theorem lex_11_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.neg 131), (Sat.Literal.pos 112)] :=
  (lex_11_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.pos 131), (Sat.Literal.neg 112)] :=
  (lex_11_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.neg 131), (Sat.Literal.neg 112), (Sat.Literal.pos 4544)] :=
  (lex_11_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4543), (Sat.Literal.pos 131), (Sat.Literal.pos 112), (Sat.Literal.pos 4544)] :=
  (lex_11_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4544) = lexBefore s permutation11 130 := by
  exact (positive_lex_of_descriptor s 4544 permutation11 131 (by rfl)).trans ((lex_skipped s permutation11 130 131 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation11 130) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation11 130 by rw [image11_eq]; rfl))

theorem lex_11_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4545) (Sat.Literal.pos 4544) (Sat.Literal.pos 130) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation11 130 (assignment s)
    (Sat.Literal.pos 4545) (Sat.Literal.pos 4544) (Sat.Literal.pos 130) (Sat.Literal.pos 80) (positive_of_descriptor s 4545 (.lex permutation11 130) (by rfl)) (lex_11_130_prefix s) (positive_select s 130) (lex_11_130_image s)

theorem lex_11_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.pos 130), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation11 130 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4544) (Sat.Literal.pos 130) (Sat.Literal.pos 80) (lex_11_130_prefix s) (positive_select s 130) (lex_11_130_image s)

theorem lex_11_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.pos 4544)] :=
  (lex_11_130_gate s).prop _ (List.Mem.head _)

theorem lex_11_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.neg 130), (Sat.Literal.pos 80)] :=
  (lex_11_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.pos 130), (Sat.Literal.neg 80)] :=
  (lex_11_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.neg 130), (Sat.Literal.neg 80), (Sat.Literal.pos 4545)] :=
  (lex_11_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4544), (Sat.Literal.pos 130), (Sat.Literal.pos 80), (Sat.Literal.pos 4545)] :=
  (lex_11_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4545) = lexBefore s permutation11 129 := by
  exact (positive_lex_of_descriptor s 4545 permutation11 130 (by rfl)).trans ((lex_skipped s permutation11 129 130 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation11 129) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation11 129 by rw [image11_eq]; rfl))

theorem lex_11_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4546) (Sat.Literal.pos 4545) (Sat.Literal.pos 129) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation11 129 (assignment s)
    (Sat.Literal.pos 4546) (Sat.Literal.pos 4545) (Sat.Literal.pos 129) (Sat.Literal.pos 48) (positive_of_descriptor s 4546 (.lex permutation11 129) (by rfl)) (lex_11_129_prefix s) (positive_select s 129) (lex_11_129_image s)

theorem lex_11_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.pos 129), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation11 129 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4545) (Sat.Literal.pos 129) (Sat.Literal.pos 48) (lex_11_129_prefix s) (positive_select s 129) (lex_11_129_image s)

theorem lex_11_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.pos 4545)] :=
  (lex_11_129_gate s).prop _ (List.Mem.head _)

theorem lex_11_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.neg 129), (Sat.Literal.pos 48)] :=
  (lex_11_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.pos 129), (Sat.Literal.neg 48)] :=
  (lex_11_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.neg 129), (Sat.Literal.neg 48), (Sat.Literal.pos 4546)] :=
  (lex_11_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4545), (Sat.Literal.pos 129), (Sat.Literal.pos 48), (Sat.Literal.pos 4546)] :=
  (lex_11_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4546) = lexBefore s permutation11 128 := by
  exact (positive_lex_of_descriptor s 4546 permutation11 129 (by rfl)).trans ((lex_skipped s permutation11 128 129 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation11 128) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation11 128 by rw [image11_eq]; rfl))

theorem lex_11_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4547) (Sat.Literal.pos 4546) (Sat.Literal.pos 128) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation11 128 (assignment s)
    (Sat.Literal.pos 4547) (Sat.Literal.pos 4546) (Sat.Literal.pos 128) (Sat.Literal.pos 16) (positive_of_descriptor s 4547 (.lex permutation11 128) (by rfl)) (lex_11_128_prefix s) (positive_select s 128) (lex_11_128_image s)

theorem lex_11_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.pos 128), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation11 128 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4546) (Sat.Literal.pos 128) (Sat.Literal.pos 16) (lex_11_128_prefix s) (positive_select s 128) (lex_11_128_image s)

theorem lex_11_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.pos 4546)] :=
  (lex_11_128_gate s).prop _ (List.Mem.head _)

theorem lex_11_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.neg 128), (Sat.Literal.pos 16)] :=
  (lex_11_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.pos 128), (Sat.Literal.neg 16)] :=
  (lex_11_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.neg 128), (Sat.Literal.neg 16), (Sat.Literal.pos 4547)] :=
  (lex_11_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4546), (Sat.Literal.pos 128), (Sat.Literal.pos 16), (Sat.Literal.pos 4547)] :=
  (lex_11_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4547) = lexBefore s permutation11 127 := by
  exact (positive_lex_of_descriptor s 4547 permutation11 128 (by rfl)).trans ((lex_skipped s permutation11 127 128 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation11 127) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation11 127 by rw [image11_eq]; rfl))

theorem lex_11_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4548) (Sat.Literal.pos 4547) (Sat.Literal.pos 127) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation11 127 (assignment s)
    (Sat.Literal.pos 4548) (Sat.Literal.pos 4547) (Sat.Literal.pos 127) (Sat.Literal.pos 239) (positive_of_descriptor s 4548 (.lex permutation11 127) (by rfl)) (lex_11_127_prefix s) (positive_select s 127) (lex_11_127_image s)

theorem lex_11_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.pos 127), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation11 127 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4547) (Sat.Literal.pos 127) (Sat.Literal.pos 239) (lex_11_127_prefix s) (positive_select s 127) (lex_11_127_image s)

theorem lex_11_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.pos 4547)] :=
  (lex_11_127_gate s).prop _ (List.Mem.head _)

theorem lex_11_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.neg 127), (Sat.Literal.pos 239)] :=
  (lex_11_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.pos 127), (Sat.Literal.neg 239)] :=
  (lex_11_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.neg 127), (Sat.Literal.neg 239), (Sat.Literal.pos 4548)] :=
  (lex_11_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4547), (Sat.Literal.pos 127), (Sat.Literal.pos 239), (Sat.Literal.pos 4548)] :=
  (lex_11_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4548) = lexBefore s permutation11 126 := by
  exact (positive_lex_of_descriptor s 4548 permutation11 127 (by rfl)).trans ((lex_skipped s permutation11 126 127 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation11 126) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation11 126 by rw [image11_eq]; rfl))

theorem lex_11_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4549) (Sat.Literal.pos 4548) (Sat.Literal.pos 126) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation11 126 (assignment s)
    (Sat.Literal.pos 4549) (Sat.Literal.pos 4548) (Sat.Literal.pos 126) (Sat.Literal.pos 207) (positive_of_descriptor s 4549 (.lex permutation11 126) (by rfl)) (lex_11_126_prefix s) (positive_select s 126) (lex_11_126_image s)

theorem lex_11_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.pos 126), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation11 126 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4548) (Sat.Literal.pos 126) (Sat.Literal.pos 207) (lex_11_126_prefix s) (positive_select s 126) (lex_11_126_image s)

theorem lex_11_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.pos 4548)] :=
  (lex_11_126_gate s).prop _ (List.Mem.head _)

theorem lex_11_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.neg 126), (Sat.Literal.pos 207)] :=
  (lex_11_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.pos 126), (Sat.Literal.neg 207)] :=
  (lex_11_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.neg 126), (Sat.Literal.neg 207), (Sat.Literal.pos 4549)] :=
  (lex_11_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4548), (Sat.Literal.pos 126), (Sat.Literal.pos 207), (Sat.Literal.pos 4549)] :=
  (lex_11_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4549) = lexBefore s permutation11 125 := by
  exact (positive_lex_of_descriptor s 4549 permutation11 126 (by rfl)).trans ((lex_skipped s permutation11 125 126 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation11 125) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation11 125 by rw [image11_eq]; rfl))

theorem lex_11_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4550) (Sat.Literal.pos 4549) (Sat.Literal.pos 125) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation11 125 (assignment s)
    (Sat.Literal.pos 4550) (Sat.Literal.pos 4549) (Sat.Literal.pos 125) (Sat.Literal.pos 175) (positive_of_descriptor s 4550 (.lex permutation11 125) (by rfl)) (lex_11_125_prefix s) (positive_select s 125) (lex_11_125_image s)

theorem lex_11_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.pos 125), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation11 125 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4549) (Sat.Literal.pos 125) (Sat.Literal.pos 175) (lex_11_125_prefix s) (positive_select s 125) (lex_11_125_image s)

theorem lex_11_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.pos 4549)] :=
  (lex_11_125_gate s).prop _ (List.Mem.head _)

theorem lex_11_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.neg 125), (Sat.Literal.pos 175)] :=
  (lex_11_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.pos 125), (Sat.Literal.neg 175)] :=
  (lex_11_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.neg 125), (Sat.Literal.neg 175), (Sat.Literal.pos 4550)] :=
  (lex_11_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4549), (Sat.Literal.pos 125), (Sat.Literal.pos 175), (Sat.Literal.pos 4550)] :=
  (lex_11_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4550) = lexBefore s permutation11 124 := by
  exact (positive_lex_of_descriptor s 4550 permutation11 125 (by rfl)).trans ((lex_skipped s permutation11 124 125 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation11 124) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation11 124 by rw [image11_eq]; rfl))

theorem lex_11_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4551) (Sat.Literal.pos 4550) (Sat.Literal.pos 124) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation11 124 (assignment s)
    (Sat.Literal.pos 4551) (Sat.Literal.pos 4550) (Sat.Literal.pos 124) (Sat.Literal.pos 143) (positive_of_descriptor s 4551 (.lex permutation11 124) (by rfl)) (lex_11_124_prefix s) (positive_select s 124) (lex_11_124_image s)

theorem lex_11_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.pos 124), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation11 124 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4550) (Sat.Literal.pos 124) (Sat.Literal.pos 143) (lex_11_124_prefix s) (positive_select s 124) (lex_11_124_image s)

theorem lex_11_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.pos 4550)] :=
  (lex_11_124_gate s).prop _ (List.Mem.head _)

theorem lex_11_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.neg 124), (Sat.Literal.pos 143)] :=
  (lex_11_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.pos 124), (Sat.Literal.neg 143)] :=
  (lex_11_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.neg 124), (Sat.Literal.neg 143), (Sat.Literal.pos 4551)] :=
  (lex_11_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4550), (Sat.Literal.pos 124), (Sat.Literal.pos 143), (Sat.Literal.pos 4551)] :=
  (lex_11_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4551) = lexBefore s permutation11 123 := by
  exact (positive_lex_of_descriptor s 4551 permutation11 124 (by rfl)).trans ((lex_skipped s permutation11 123 124 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation11 123) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation11 123 by rw [image11_eq]; rfl))

theorem lex_11_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4552) (Sat.Literal.pos 4551) (Sat.Literal.pos 123) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation11 123 (assignment s)
    (Sat.Literal.pos 4552) (Sat.Literal.pos 4551) (Sat.Literal.pos 123) (Sat.Literal.pos 111) (positive_of_descriptor s 4552 (.lex permutation11 123) (by rfl)) (lex_11_123_prefix s) (positive_select s 123) (lex_11_123_image s)

theorem lex_11_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.pos 123), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation11 123 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4551) (Sat.Literal.pos 123) (Sat.Literal.pos 111) (lex_11_123_prefix s) (positive_select s 123) (lex_11_123_image s)

theorem lex_11_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.pos 4551)] :=
  (lex_11_123_gate s).prop _ (List.Mem.head _)

theorem lex_11_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.neg 123), (Sat.Literal.pos 111)] :=
  (lex_11_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.pos 123), (Sat.Literal.neg 111)] :=
  (lex_11_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.neg 123), (Sat.Literal.neg 111), (Sat.Literal.pos 4552)] :=
  (lex_11_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4551), (Sat.Literal.pos 123), (Sat.Literal.pos 111), (Sat.Literal.pos 4552)] :=
  (lex_11_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4552) = lexBefore s permutation11 122 := by
  exact (positive_lex_of_descriptor s 4552 permutation11 123 (by rfl)).trans ((lex_skipped s permutation11 122 123 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation11 122) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation11 122 by rw [image11_eq]; rfl))

theorem lex_11_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4553) (Sat.Literal.pos 4552) (Sat.Literal.pos 122) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation11 122 (assignment s)
    (Sat.Literal.pos 4553) (Sat.Literal.pos 4552) (Sat.Literal.pos 122) (Sat.Literal.pos 79) (positive_of_descriptor s 4553 (.lex permutation11 122) (by rfl)) (lex_11_122_prefix s) (positive_select s 122) (lex_11_122_image s)

theorem lex_11_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.pos 122), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation11 122 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4552) (Sat.Literal.pos 122) (Sat.Literal.pos 79) (lex_11_122_prefix s) (positive_select s 122) (lex_11_122_image s)

theorem lex_11_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.pos 4552)] :=
  (lex_11_122_gate s).prop _ (List.Mem.head _)

theorem lex_11_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.neg 122), (Sat.Literal.pos 79)] :=
  (lex_11_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.pos 122), (Sat.Literal.neg 79)] :=
  (lex_11_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.neg 122), (Sat.Literal.neg 79), (Sat.Literal.pos 4553)] :=
  (lex_11_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4552), (Sat.Literal.pos 122), (Sat.Literal.pos 79), (Sat.Literal.pos 4553)] :=
  (lex_11_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4553) = lexBefore s permutation11 121 := by
  exact (positive_lex_of_descriptor s 4553 permutation11 122 (by rfl)).trans ((lex_skipped s permutation11 121 122 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation11 121) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation11 121 by rw [image11_eq]; rfl))

theorem lex_11_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4554) (Sat.Literal.pos 4553) (Sat.Literal.pos 121) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation11 121 (assignment s)
    (Sat.Literal.pos 4554) (Sat.Literal.pos 4553) (Sat.Literal.pos 121) (Sat.Literal.pos 47) (positive_of_descriptor s 4554 (.lex permutation11 121) (by rfl)) (lex_11_121_prefix s) (positive_select s 121) (lex_11_121_image s)

theorem lex_11_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.pos 121), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation11 121 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4553) (Sat.Literal.pos 121) (Sat.Literal.pos 47) (lex_11_121_prefix s) (positive_select s 121) (lex_11_121_image s)

theorem lex_11_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.pos 4553)] :=
  (lex_11_121_gate s).prop _ (List.Mem.head _)

theorem lex_11_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.neg 121), (Sat.Literal.pos 47)] :=
  (lex_11_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.pos 121), (Sat.Literal.neg 47)] :=
  (lex_11_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.neg 121), (Sat.Literal.neg 47), (Sat.Literal.pos 4554)] :=
  (lex_11_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4553), (Sat.Literal.pos 121), (Sat.Literal.pos 47), (Sat.Literal.pos 4554)] :=
  (lex_11_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4554) = lexBefore s permutation11 120 := by
  exact (positive_lex_of_descriptor s 4554 permutation11 121 (by rfl)).trans ((lex_skipped s permutation11 120 121 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation11 120) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation11 120 by rw [image11_eq]; rfl))

theorem lex_11_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4555) (Sat.Literal.pos 4554) (Sat.Literal.pos 120) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation11 120 (assignment s)
    (Sat.Literal.pos 4555) (Sat.Literal.pos 4554) (Sat.Literal.pos 120) (Sat.Literal.pos 15) (positive_of_descriptor s 4555 (.lex permutation11 120) (by rfl)) (lex_11_120_prefix s) (positive_select s 120) (lex_11_120_image s)

theorem lex_11_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.pos 120), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation11 120 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4554) (Sat.Literal.pos 120) (Sat.Literal.pos 15) (lex_11_120_prefix s) (positive_select s 120) (lex_11_120_image s)

theorem lex_11_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.pos 4554)] :=
  (lex_11_120_gate s).prop _ (List.Mem.head _)

theorem lex_11_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.neg 120), (Sat.Literal.pos 15)] :=
  (lex_11_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.pos 120), (Sat.Literal.neg 15)] :=
  (lex_11_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.neg 120), (Sat.Literal.neg 15), (Sat.Literal.pos 4555)] :=
  (lex_11_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4554), (Sat.Literal.pos 120), (Sat.Literal.pos 15), (Sat.Literal.pos 4555)] :=
  (lex_11_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4555) = lexBefore s permutation11 119 := by
  exact (positive_lex_of_descriptor s 4555 permutation11 120 (by rfl)).trans ((lex_skipped s permutation11 119 120 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation11 119) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation11 119 by rw [image11_eq]; rfl))

theorem lex_11_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4556) (Sat.Literal.pos 4555) (Sat.Literal.pos 119) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation11 119 (assignment s)
    (Sat.Literal.pos 4556) (Sat.Literal.pos 4555) (Sat.Literal.pos 119) (Sat.Literal.pos 238) (positive_of_descriptor s 4556 (.lex permutation11 119) (by rfl)) (lex_11_119_prefix s) (positive_select s 119) (lex_11_119_image s)

theorem lex_11_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.pos 119), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation11 119 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4555) (Sat.Literal.pos 119) (Sat.Literal.pos 238) (lex_11_119_prefix s) (positive_select s 119) (lex_11_119_image s)

theorem lex_11_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.pos 4555)] :=
  (lex_11_119_gate s).prop _ (List.Mem.head _)

theorem lex_11_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.neg 119), (Sat.Literal.pos 238)] :=
  (lex_11_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.pos 119), (Sat.Literal.neg 238)] :=
  (lex_11_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.neg 119), (Sat.Literal.neg 238), (Sat.Literal.pos 4556)] :=
  (lex_11_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4555), (Sat.Literal.pos 119), (Sat.Literal.pos 238), (Sat.Literal.pos 4556)] :=
  (lex_11_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4556) = lexBefore s permutation11 118 := by
  exact (positive_lex_of_descriptor s 4556 permutation11 119 (by rfl)).trans ((lex_skipped s permutation11 118 119 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation11 118) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation11 118 by rw [image11_eq]; rfl))

theorem lex_11_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4557) (Sat.Literal.pos 4556) (Sat.Literal.pos 118) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation11 118 (assignment s)
    (Sat.Literal.pos 4557) (Sat.Literal.pos 4556) (Sat.Literal.pos 118) (Sat.Literal.pos 206) (positive_of_descriptor s 4557 (.lex permutation11 118) (by rfl)) (lex_11_118_prefix s) (positive_select s 118) (lex_11_118_image s)

theorem lex_11_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.pos 118), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation11 118 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4556) (Sat.Literal.pos 118) (Sat.Literal.pos 206) (lex_11_118_prefix s) (positive_select s 118) (lex_11_118_image s)

theorem lex_11_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.pos 4556)] :=
  (lex_11_118_gate s).prop _ (List.Mem.head _)

theorem lex_11_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.neg 118), (Sat.Literal.pos 206)] :=
  (lex_11_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.pos 118), (Sat.Literal.neg 206)] :=
  (lex_11_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.neg 118), (Sat.Literal.neg 206), (Sat.Literal.pos 4557)] :=
  (lex_11_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4556), (Sat.Literal.pos 118), (Sat.Literal.pos 206), (Sat.Literal.pos 4557)] :=
  (lex_11_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4557) = lexBefore s permutation11 117 := by
  exact (positive_lex_of_descriptor s 4557 permutation11 118 (by rfl)).trans ((lex_skipped s permutation11 117 118 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation11 117) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation11 117 by rw [image11_eq]; rfl))

theorem lex_11_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4558) (Sat.Literal.pos 4557) (Sat.Literal.pos 117) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation11 117 (assignment s)
    (Sat.Literal.pos 4558) (Sat.Literal.pos 4557) (Sat.Literal.pos 117) (Sat.Literal.pos 174) (positive_of_descriptor s 4558 (.lex permutation11 117) (by rfl)) (lex_11_117_prefix s) (positive_select s 117) (lex_11_117_image s)

theorem lex_11_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.pos 117), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation11 117 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4557) (Sat.Literal.pos 117) (Sat.Literal.pos 174) (lex_11_117_prefix s) (positive_select s 117) (lex_11_117_image s)

theorem lex_11_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.pos 4557)] :=
  (lex_11_117_gate s).prop _ (List.Mem.head _)

theorem lex_11_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.neg 117), (Sat.Literal.pos 174)] :=
  (lex_11_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.pos 117), (Sat.Literal.neg 174)] :=
  (lex_11_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.neg 117), (Sat.Literal.neg 174), (Sat.Literal.pos 4558)] :=
  (lex_11_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4557), (Sat.Literal.pos 117), (Sat.Literal.pos 174), (Sat.Literal.pos 4558)] :=
  (lex_11_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4558) = lexBefore s permutation11 116 := by
  exact (positive_lex_of_descriptor s 4558 permutation11 117 (by rfl)).trans ((lex_skipped s permutation11 116 117 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation11 116) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation11 116 by rw [image11_eq]; rfl))

theorem lex_11_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4559) (Sat.Literal.pos 4558) (Sat.Literal.pos 116) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation11 116 (assignment s)
    (Sat.Literal.pos 4559) (Sat.Literal.pos 4558) (Sat.Literal.pos 116) (Sat.Literal.pos 142) (positive_of_descriptor s 4559 (.lex permutation11 116) (by rfl)) (lex_11_116_prefix s) (positive_select s 116) (lex_11_116_image s)

theorem lex_11_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.pos 116), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation11 116 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4558) (Sat.Literal.pos 116) (Sat.Literal.pos 142) (lex_11_116_prefix s) (positive_select s 116) (lex_11_116_image s)

theorem lex_11_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.pos 4558)] :=
  (lex_11_116_gate s).prop _ (List.Mem.head _)

theorem lex_11_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.neg 116), (Sat.Literal.pos 142)] :=
  (lex_11_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.pos 116), (Sat.Literal.neg 142)] :=
  (lex_11_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.neg 116), (Sat.Literal.neg 142), (Sat.Literal.pos 4559)] :=
  (lex_11_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4558), (Sat.Literal.pos 116), (Sat.Literal.pos 142), (Sat.Literal.pos 4559)] :=
  (lex_11_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4559) = lexBefore s permutation11 115 := by
  exact (positive_lex_of_descriptor s 4559 permutation11 116 (by rfl)).trans ((lex_skipped s permutation11 115 116 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation11 115) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation11 115 by rw [image11_eq]; rfl))

theorem lex_11_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4560) (Sat.Literal.pos 4559) (Sat.Literal.pos 115) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation11 115 (assignment s)
    (Sat.Literal.pos 4560) (Sat.Literal.pos 4559) (Sat.Literal.pos 115) (Sat.Literal.pos 110) (positive_of_descriptor s 4560 (.lex permutation11 115) (by rfl)) (lex_11_115_prefix s) (positive_select s 115) (lex_11_115_image s)

theorem lex_11_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.pos 115), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation11 115 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4559) (Sat.Literal.pos 115) (Sat.Literal.pos 110) (lex_11_115_prefix s) (positive_select s 115) (lex_11_115_image s)

theorem lex_11_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.pos 4559)] :=
  (lex_11_115_gate s).prop _ (List.Mem.head _)

theorem lex_11_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.neg 115), (Sat.Literal.pos 110)] :=
  (lex_11_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.pos 115), (Sat.Literal.neg 110)] :=
  (lex_11_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.neg 115), (Sat.Literal.neg 110), (Sat.Literal.pos 4560)] :=
  (lex_11_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4559), (Sat.Literal.pos 115), (Sat.Literal.pos 110), (Sat.Literal.pos 4560)] :=
  (lex_11_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4560) = lexBefore s permutation11 114 := by
  exact (positive_lex_of_descriptor s 4560 permutation11 115 (by rfl)).trans ((lex_skipped s permutation11 114 115 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation11 114) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation11 114 by rw [image11_eq]; rfl))

theorem lex_11_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4561) (Sat.Literal.pos 4560) (Sat.Literal.pos 114) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation11 114 (assignment s)
    (Sat.Literal.pos 4561) (Sat.Literal.pos 4560) (Sat.Literal.pos 114) (Sat.Literal.pos 78) (positive_of_descriptor s 4561 (.lex permutation11 114) (by rfl)) (lex_11_114_prefix s) (positive_select s 114) (lex_11_114_image s)

theorem lex_11_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.pos 114), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation11 114 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4560) (Sat.Literal.pos 114) (Sat.Literal.pos 78) (lex_11_114_prefix s) (positive_select s 114) (lex_11_114_image s)

theorem lex_11_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.pos 4560)] :=
  (lex_11_114_gate s).prop _ (List.Mem.head _)

theorem lex_11_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.neg 114), (Sat.Literal.pos 78)] :=
  (lex_11_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.pos 114), (Sat.Literal.neg 78)] :=
  (lex_11_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.neg 114), (Sat.Literal.neg 78), (Sat.Literal.pos 4561)] :=
  (lex_11_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4560), (Sat.Literal.pos 114), (Sat.Literal.pos 78), (Sat.Literal.pos 4561)] :=
  (lex_11_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4561) = lexBefore s permutation11 113 := by
  exact (positive_lex_of_descriptor s 4561 permutation11 114 (by rfl)).trans ((lex_skipped s permutation11 113 114 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation11 113) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation11 113 by rw [image11_eq]; rfl))

theorem lex_11_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4562) (Sat.Literal.pos 4561) (Sat.Literal.pos 113) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation11 113 (assignment s)
    (Sat.Literal.pos 4562) (Sat.Literal.pos 4561) (Sat.Literal.pos 113) (Sat.Literal.pos 46) (positive_of_descriptor s 4562 (.lex permutation11 113) (by rfl)) (lex_11_113_prefix s) (positive_select s 113) (lex_11_113_image s)

theorem lex_11_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.pos 113), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation11 113 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4561) (Sat.Literal.pos 113) (Sat.Literal.pos 46) (lex_11_113_prefix s) (positive_select s 113) (lex_11_113_image s)

theorem lex_11_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.pos 4561)] :=
  (lex_11_113_gate s).prop _ (List.Mem.head _)

theorem lex_11_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.neg 113), (Sat.Literal.pos 46)] :=
  (lex_11_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.pos 113), (Sat.Literal.neg 46)] :=
  (lex_11_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.neg 113), (Sat.Literal.neg 46), (Sat.Literal.pos 4562)] :=
  (lex_11_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4561), (Sat.Literal.pos 113), (Sat.Literal.pos 46), (Sat.Literal.pos 4562)] :=
  (lex_11_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4562) = lexBefore s permutation11 112 := by
  exact (positive_lex_of_descriptor s 4562 permutation11 113 (by rfl)).trans ((lex_skipped s permutation11 112 113 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation11 112) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation11 112 by rw [image11_eq]; rfl))

theorem lex_11_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4563) (Sat.Literal.pos 4562) (Sat.Literal.pos 112) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation11 112 (assignment s)
    (Sat.Literal.pos 4563) (Sat.Literal.pos 4562) (Sat.Literal.pos 112) (Sat.Literal.pos 14) (positive_of_descriptor s 4563 (.lex permutation11 112) (by rfl)) (lex_11_112_prefix s) (positive_select s 112) (lex_11_112_image s)

theorem lex_11_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.pos 112), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation11 112 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4562) (Sat.Literal.pos 112) (Sat.Literal.pos 14) (lex_11_112_prefix s) (positive_select s 112) (lex_11_112_image s)

theorem lex_11_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.pos 4562)] :=
  (lex_11_112_gate s).prop _ (List.Mem.head _)

theorem lex_11_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.neg 112), (Sat.Literal.pos 14)] :=
  (lex_11_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.pos 112), (Sat.Literal.neg 14)] :=
  (lex_11_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.neg 112), (Sat.Literal.neg 14), (Sat.Literal.pos 4563)] :=
  (lex_11_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4562), (Sat.Literal.pos 112), (Sat.Literal.pos 14), (Sat.Literal.pos 4563)] :=
  (lex_11_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4563) = lexBefore s permutation11 111 := by
  exact (positive_lex_of_descriptor s 4563 permutation11 112 (by rfl)).trans ((lex_skipped s permutation11 111 112 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation11 111) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation11 111 by rw [image11_eq]; rfl))

theorem lex_11_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4564) (Sat.Literal.pos 4563) (Sat.Literal.pos 111) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation11 111 (assignment s)
    (Sat.Literal.pos 4564) (Sat.Literal.pos 4563) (Sat.Literal.pos 111) (Sat.Literal.pos 237) (positive_of_descriptor s 4564 (.lex permutation11 111) (by rfl)) (lex_11_111_prefix s) (positive_select s 111) (lex_11_111_image s)

theorem lex_11_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.pos 111), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation11 111 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4563) (Sat.Literal.pos 111) (Sat.Literal.pos 237) (lex_11_111_prefix s) (positive_select s 111) (lex_11_111_image s)

theorem lex_11_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.pos 4563)] :=
  (lex_11_111_gate s).prop _ (List.Mem.head _)

theorem lex_11_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.neg 111), (Sat.Literal.pos 237)] :=
  (lex_11_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.pos 111), (Sat.Literal.neg 237)] :=
  (lex_11_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.neg 111), (Sat.Literal.neg 237), (Sat.Literal.pos 4564)] :=
  (lex_11_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4563), (Sat.Literal.pos 111), (Sat.Literal.pos 237), (Sat.Literal.pos 4564)] :=
  (lex_11_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4564) = lexBefore s permutation11 110 := by
  exact (positive_lex_of_descriptor s 4564 permutation11 111 (by rfl)).trans ((lex_skipped s permutation11 110 111 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation11 110) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation11 110 by rw [image11_eq]; rfl))

theorem lex_11_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4565) (Sat.Literal.pos 4564) (Sat.Literal.pos 110) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation11 110 (assignment s)
    (Sat.Literal.pos 4565) (Sat.Literal.pos 4564) (Sat.Literal.pos 110) (Sat.Literal.pos 205) (positive_of_descriptor s 4565 (.lex permutation11 110) (by rfl)) (lex_11_110_prefix s) (positive_select s 110) (lex_11_110_image s)

theorem lex_11_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.pos 110), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation11 110 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4564) (Sat.Literal.pos 110) (Sat.Literal.pos 205) (lex_11_110_prefix s) (positive_select s 110) (lex_11_110_image s)

theorem lex_11_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.pos 4564)] :=
  (lex_11_110_gate s).prop _ (List.Mem.head _)

theorem lex_11_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.neg 110), (Sat.Literal.pos 205)] :=
  (lex_11_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.pos 110), (Sat.Literal.neg 205)] :=
  (lex_11_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.neg 110), (Sat.Literal.neg 205), (Sat.Literal.pos 4565)] :=
  (lex_11_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4564), (Sat.Literal.pos 110), (Sat.Literal.pos 205), (Sat.Literal.pos 4565)] :=
  (lex_11_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4565) = lexBefore s permutation11 109 := by
  exact (positive_lex_of_descriptor s 4565 permutation11 110 (by rfl)).trans ((lex_skipped s permutation11 109 110 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation11 109) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation11 109 by rw [image11_eq]; rfl))

theorem lex_11_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4566) (Sat.Literal.pos 4565) (Sat.Literal.pos 109) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation11 109 (assignment s)
    (Sat.Literal.pos 4566) (Sat.Literal.pos 4565) (Sat.Literal.pos 109) (Sat.Literal.pos 173) (positive_of_descriptor s 4566 (.lex permutation11 109) (by rfl)) (lex_11_109_prefix s) (positive_select s 109) (lex_11_109_image s)

theorem lex_11_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.pos 109), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation11 109 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4565) (Sat.Literal.pos 109) (Sat.Literal.pos 173) (lex_11_109_prefix s) (positive_select s 109) (lex_11_109_image s)

theorem lex_11_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.pos 4565)] :=
  (lex_11_109_gate s).prop _ (List.Mem.head _)

theorem lex_11_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.neg 109), (Sat.Literal.pos 173)] :=
  (lex_11_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.pos 109), (Sat.Literal.neg 173)] :=
  (lex_11_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.neg 109), (Sat.Literal.neg 173), (Sat.Literal.pos 4566)] :=
  (lex_11_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4565), (Sat.Literal.pos 109), (Sat.Literal.pos 173), (Sat.Literal.pos 4566)] :=
  (lex_11_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4566) = lexBefore s permutation11 108 := by
  exact (positive_lex_of_descriptor s 4566 permutation11 109 (by rfl)).trans ((lex_skipped s permutation11 108 109 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation11 108) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation11 108 by rw [image11_eq]; rfl))

theorem lex_11_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4567) (Sat.Literal.pos 4566) (Sat.Literal.pos 108) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation11 108 (assignment s)
    (Sat.Literal.pos 4567) (Sat.Literal.pos 4566) (Sat.Literal.pos 108) (Sat.Literal.pos 141) (positive_of_descriptor s 4567 (.lex permutation11 108) (by rfl)) (lex_11_108_prefix s) (positive_select s 108) (lex_11_108_image s)

theorem lex_11_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.pos 108), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation11 108 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4566) (Sat.Literal.pos 108) (Sat.Literal.pos 141) (lex_11_108_prefix s) (positive_select s 108) (lex_11_108_image s)

theorem lex_11_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.pos 4566)] :=
  (lex_11_108_gate s).prop _ (List.Mem.head _)

theorem lex_11_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.neg 108), (Sat.Literal.pos 141)] :=
  (lex_11_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.pos 108), (Sat.Literal.neg 141)] :=
  (lex_11_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.neg 108), (Sat.Literal.neg 141), (Sat.Literal.pos 4567)] :=
  (lex_11_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4566), (Sat.Literal.pos 108), (Sat.Literal.pos 141), (Sat.Literal.pos 4567)] :=
  (lex_11_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4567) = lexBefore s permutation11 107 := by
  exact (positive_lex_of_descriptor s 4567 permutation11 108 (by rfl)).trans ((lex_skipped s permutation11 107 108 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation11 107) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation11 107 by rw [image11_eq]; rfl))

theorem lex_11_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4568) (Sat.Literal.pos 4567) (Sat.Literal.pos 107) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation11 107 (assignment s)
    (Sat.Literal.pos 4568) (Sat.Literal.pos 4567) (Sat.Literal.pos 107) (Sat.Literal.pos 109) (positive_of_descriptor s 4568 (.lex permutation11 107) (by rfl)) (lex_11_107_prefix s) (positive_select s 107) (lex_11_107_image s)

theorem lex_11_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.pos 107), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation11 107 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4567) (Sat.Literal.pos 107) (Sat.Literal.pos 109) (lex_11_107_prefix s) (positive_select s 107) (lex_11_107_image s)

theorem lex_11_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.pos 4567)] :=
  (lex_11_107_gate s).prop _ (List.Mem.head _)

theorem lex_11_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.neg 107), (Sat.Literal.pos 109)] :=
  (lex_11_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.pos 107), (Sat.Literal.neg 109)] :=
  (lex_11_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.neg 107), (Sat.Literal.neg 109), (Sat.Literal.pos 4568)] :=
  (lex_11_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4567), (Sat.Literal.pos 107), (Sat.Literal.pos 109), (Sat.Literal.pos 4568)] :=
  (lex_11_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4568) = lexBefore s permutation11 106 := by
  exact (positive_lex_of_descriptor s 4568 permutation11 107 (by rfl)).trans ((lex_skipped s permutation11 106 107 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation11 106) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation11 106 by rw [image11_eq]; rfl))

theorem lex_11_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4569) (Sat.Literal.pos 4568) (Sat.Literal.pos 106) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation11 106 (assignment s)
    (Sat.Literal.pos 4569) (Sat.Literal.pos 4568) (Sat.Literal.pos 106) (Sat.Literal.pos 77) (positive_of_descriptor s 4569 (.lex permutation11 106) (by rfl)) (lex_11_106_prefix s) (positive_select s 106) (lex_11_106_image s)

theorem lex_11_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.pos 106), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation11 106 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4568) (Sat.Literal.pos 106) (Sat.Literal.pos 77) (lex_11_106_prefix s) (positive_select s 106) (lex_11_106_image s)

theorem lex_11_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.pos 4568)] :=
  (lex_11_106_gate s).prop _ (List.Mem.head _)

theorem lex_11_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.neg 106), (Sat.Literal.pos 77)] :=
  (lex_11_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.pos 106), (Sat.Literal.neg 77)] :=
  (lex_11_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.neg 106), (Sat.Literal.neg 77), (Sat.Literal.pos 4569)] :=
  (lex_11_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4568), (Sat.Literal.pos 106), (Sat.Literal.pos 77), (Sat.Literal.pos 4569)] :=
  (lex_11_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4569) = lexBefore s permutation11 105 := by
  exact (positive_lex_of_descriptor s 4569 permutation11 106 (by rfl)).trans ((lex_skipped s permutation11 105 106 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation11 105) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation11 105 by rw [image11_eq]; rfl))

theorem lex_11_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4570) (Sat.Literal.pos 4569) (Sat.Literal.pos 105) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation11 105 (assignment s)
    (Sat.Literal.pos 4570) (Sat.Literal.pos 4569) (Sat.Literal.pos 105) (Sat.Literal.pos 45) (positive_of_descriptor s 4570 (.lex permutation11 105) (by rfl)) (lex_11_105_prefix s) (positive_select s 105) (lex_11_105_image s)

theorem lex_11_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.pos 105), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation11 105 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4569) (Sat.Literal.pos 105) (Sat.Literal.pos 45) (lex_11_105_prefix s) (positive_select s 105) (lex_11_105_image s)

theorem lex_11_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.pos 4569)] :=
  (lex_11_105_gate s).prop _ (List.Mem.head _)

theorem lex_11_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.neg 105), (Sat.Literal.pos 45)] :=
  (lex_11_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.pos 105), (Sat.Literal.neg 45)] :=
  (lex_11_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.neg 105), (Sat.Literal.neg 45), (Sat.Literal.pos 4570)] :=
  (lex_11_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4569), (Sat.Literal.pos 105), (Sat.Literal.pos 45), (Sat.Literal.pos 4570)] :=
  (lex_11_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4570) = lexBefore s permutation11 104 := by
  exact (positive_lex_of_descriptor s 4570 permutation11 105 (by rfl)).trans ((lex_skipped s permutation11 104 105 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation11 104) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation11 104 by rw [image11_eq]; rfl))

theorem lex_11_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4571) (Sat.Literal.pos 4570) (Sat.Literal.pos 104) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation11 104 (assignment s)
    (Sat.Literal.pos 4571) (Sat.Literal.pos 4570) (Sat.Literal.pos 104) (Sat.Literal.pos 13) (positive_of_descriptor s 4571 (.lex permutation11 104) (by rfl)) (lex_11_104_prefix s) (positive_select s 104) (lex_11_104_image s)

theorem lex_11_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.pos 104), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation11 104 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4570) (Sat.Literal.pos 104) (Sat.Literal.pos 13) (lex_11_104_prefix s) (positive_select s 104) (lex_11_104_image s)

theorem lex_11_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.pos 4570)] :=
  (lex_11_104_gate s).prop _ (List.Mem.head _)

theorem lex_11_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.neg 104), (Sat.Literal.pos 13)] :=
  (lex_11_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.pos 104), (Sat.Literal.neg 13)] :=
  (lex_11_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.neg 104), (Sat.Literal.neg 13), (Sat.Literal.pos 4571)] :=
  (lex_11_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4570), (Sat.Literal.pos 104), (Sat.Literal.pos 13), (Sat.Literal.pos 4571)] :=
  (lex_11_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4571) = lexBefore s permutation11 103 := by
  exact (positive_lex_of_descriptor s 4571 permutation11 104 (by rfl)).trans ((lex_skipped s permutation11 103 104 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation11 103) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation11 103 by rw [image11_eq]; rfl))

theorem lex_11_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4572) (Sat.Literal.pos 4571) (Sat.Literal.pos 103) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation11 103 (assignment s)
    (Sat.Literal.pos 4572) (Sat.Literal.pos 4571) (Sat.Literal.pos 103) (Sat.Literal.pos 236) (positive_of_descriptor s 4572 (.lex permutation11 103) (by rfl)) (lex_11_103_prefix s) (positive_select s 103) (lex_11_103_image s)

theorem lex_11_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.pos 103), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation11 103 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4571) (Sat.Literal.pos 103) (Sat.Literal.pos 236) (lex_11_103_prefix s) (positive_select s 103) (lex_11_103_image s)

theorem lex_11_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.pos 4571)] :=
  (lex_11_103_gate s).prop _ (List.Mem.head _)

theorem lex_11_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.neg 103), (Sat.Literal.pos 236)] :=
  (lex_11_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.pos 103), (Sat.Literal.neg 236)] :=
  (lex_11_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.neg 103), (Sat.Literal.neg 236), (Sat.Literal.pos 4572)] :=
  (lex_11_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4571), (Sat.Literal.pos 103), (Sat.Literal.pos 236), (Sat.Literal.pos 4572)] :=
  (lex_11_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4572) = lexBefore s permutation11 102 := by
  exact (positive_lex_of_descriptor s 4572 permutation11 103 (by rfl)).trans ((lex_skipped s permutation11 102 103 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation11 102) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation11 102 by rw [image11_eq]; rfl))

theorem lex_11_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4573) (Sat.Literal.pos 4572) (Sat.Literal.pos 102) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation11 102 (assignment s)
    (Sat.Literal.pos 4573) (Sat.Literal.pos 4572) (Sat.Literal.pos 102) (Sat.Literal.pos 204) (positive_of_descriptor s 4573 (.lex permutation11 102) (by rfl)) (lex_11_102_prefix s) (positive_select s 102) (lex_11_102_image s)

theorem lex_11_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.pos 102), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation11 102 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4572) (Sat.Literal.pos 102) (Sat.Literal.pos 204) (lex_11_102_prefix s) (positive_select s 102) (lex_11_102_image s)

theorem lex_11_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.pos 4572)] :=
  (lex_11_102_gate s).prop _ (List.Mem.head _)

theorem lex_11_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.neg 102), (Sat.Literal.pos 204)] :=
  (lex_11_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.pos 102), (Sat.Literal.neg 204)] :=
  (lex_11_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.neg 102), (Sat.Literal.neg 204), (Sat.Literal.pos 4573)] :=
  (lex_11_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4572), (Sat.Literal.pos 102), (Sat.Literal.pos 204), (Sat.Literal.pos 4573)] :=
  (lex_11_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4573) = lexBefore s permutation11 101 := by
  exact (positive_lex_of_descriptor s 4573 permutation11 102 (by rfl)).trans ((lex_skipped s permutation11 101 102 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation11 101) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation11 101 by rw [image11_eq]; rfl))

theorem lex_11_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4574) (Sat.Literal.pos 4573) (Sat.Literal.pos 101) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation11 101 (assignment s)
    (Sat.Literal.pos 4574) (Sat.Literal.pos 4573) (Sat.Literal.pos 101) (Sat.Literal.pos 172) (positive_of_descriptor s 4574 (.lex permutation11 101) (by rfl)) (lex_11_101_prefix s) (positive_select s 101) (lex_11_101_image s)

theorem lex_11_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.pos 101), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation11 101 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4573) (Sat.Literal.pos 101) (Sat.Literal.pos 172) (lex_11_101_prefix s) (positive_select s 101) (lex_11_101_image s)

theorem lex_11_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.pos 4573)] :=
  (lex_11_101_gate s).prop _ (List.Mem.head _)

theorem lex_11_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.neg 101), (Sat.Literal.pos 172)] :=
  (lex_11_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.pos 101), (Sat.Literal.neg 172)] :=
  (lex_11_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.neg 101), (Sat.Literal.neg 172), (Sat.Literal.pos 4574)] :=
  (lex_11_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4573), (Sat.Literal.pos 101), (Sat.Literal.pos 172), (Sat.Literal.pos 4574)] :=
  (lex_11_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4574) = lexBefore s permutation11 100 := by
  exact (positive_lex_of_descriptor s 4574 permutation11 101 (by rfl)).trans ((lex_skipped s permutation11 100 101 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation11 100) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation11 100 by rw [image11_eq]; rfl))

theorem lex_11_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4575) (Sat.Literal.pos 4574) (Sat.Literal.pos 100) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation11 100 (assignment s)
    (Sat.Literal.pos 4575) (Sat.Literal.pos 4574) (Sat.Literal.pos 100) (Sat.Literal.pos 140) (positive_of_descriptor s 4575 (.lex permutation11 100) (by rfl)) (lex_11_100_prefix s) (positive_select s 100) (lex_11_100_image s)

theorem lex_11_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.pos 100), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation11 100 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4574) (Sat.Literal.pos 100) (Sat.Literal.pos 140) (lex_11_100_prefix s) (positive_select s 100) (lex_11_100_image s)

theorem lex_11_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.pos 4574)] :=
  (lex_11_100_gate s).prop _ (List.Mem.head _)

theorem lex_11_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.neg 100), (Sat.Literal.pos 140)] :=
  (lex_11_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.pos 100), (Sat.Literal.neg 140)] :=
  (lex_11_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.neg 100), (Sat.Literal.neg 140), (Sat.Literal.pos 4575)] :=
  (lex_11_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4574), (Sat.Literal.pos 100), (Sat.Literal.pos 140), (Sat.Literal.pos 4575)] :=
  (lex_11_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4575) = lexBefore s permutation11 99 := by
  exact (positive_lex_of_descriptor s 4575 permutation11 100 (by rfl)).trans ((lex_skipped s permutation11 99 100 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation11 99) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation11 99 by rw [image11_eq]; rfl))

theorem lex_11_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4576) (Sat.Literal.pos 4575) (Sat.Literal.pos 99) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation11 99 (assignment s)
    (Sat.Literal.pos 4576) (Sat.Literal.pos 4575) (Sat.Literal.pos 99) (Sat.Literal.pos 108) (positive_of_descriptor s 4576 (.lex permutation11 99) (by rfl)) (lex_11_99_prefix s) (positive_select s 99) (lex_11_99_image s)

theorem lex_11_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.pos 99), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation11 99 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4575) (Sat.Literal.pos 99) (Sat.Literal.pos 108) (lex_11_99_prefix s) (positive_select s 99) (lex_11_99_image s)

theorem lex_11_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.pos 4575)] :=
  (lex_11_99_gate s).prop _ (List.Mem.head _)

theorem lex_11_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.neg 99), (Sat.Literal.pos 108)] :=
  (lex_11_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.pos 99), (Sat.Literal.neg 108)] :=
  (lex_11_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.neg 99), (Sat.Literal.neg 108), (Sat.Literal.pos 4576)] :=
  (lex_11_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4575), (Sat.Literal.pos 99), (Sat.Literal.pos 108), (Sat.Literal.pos 4576)] :=
  (lex_11_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4576) = lexBefore s permutation11 98 := by
  exact (positive_lex_of_descriptor s 4576 permutation11 99 (by rfl)).trans ((lex_skipped s permutation11 98 99 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation11 98) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation11 98 by rw [image11_eq]; rfl))

theorem lex_11_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4577) (Sat.Literal.pos 4576) (Sat.Literal.pos 98) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation11 98 (assignment s)
    (Sat.Literal.pos 4577) (Sat.Literal.pos 4576) (Sat.Literal.pos 98) (Sat.Literal.pos 76) (positive_of_descriptor s 4577 (.lex permutation11 98) (by rfl)) (lex_11_98_prefix s) (positive_select s 98) (lex_11_98_image s)

theorem lex_11_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.pos 98), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation11 98 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4576) (Sat.Literal.pos 98) (Sat.Literal.pos 76) (lex_11_98_prefix s) (positive_select s 98) (lex_11_98_image s)

theorem lex_11_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.pos 4576)] :=
  (lex_11_98_gate s).prop _ (List.Mem.head _)

theorem lex_11_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.neg 98), (Sat.Literal.pos 76)] :=
  (lex_11_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.pos 98), (Sat.Literal.neg 76)] :=
  (lex_11_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.neg 98), (Sat.Literal.neg 76), (Sat.Literal.pos 4577)] :=
  (lex_11_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4576), (Sat.Literal.pos 98), (Sat.Literal.pos 76), (Sat.Literal.pos 4577)] :=
  (lex_11_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4577) = lexBefore s permutation11 97 := by
  exact (positive_lex_of_descriptor s 4577 permutation11 98 (by rfl)).trans ((lex_skipped s permutation11 97 98 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation11 97) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation11 97 by rw [image11_eq]; rfl))

theorem lex_11_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4578) (Sat.Literal.pos 4577) (Sat.Literal.pos 97) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation11 97 (assignment s)
    (Sat.Literal.pos 4578) (Sat.Literal.pos 4577) (Sat.Literal.pos 97) (Sat.Literal.pos 44) (positive_of_descriptor s 4578 (.lex permutation11 97) (by rfl)) (lex_11_97_prefix s) (positive_select s 97) (lex_11_97_image s)

theorem lex_11_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.pos 97), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation11 97 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4577) (Sat.Literal.pos 97) (Sat.Literal.pos 44) (lex_11_97_prefix s) (positive_select s 97) (lex_11_97_image s)

theorem lex_11_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.pos 4577)] :=
  (lex_11_97_gate s).prop _ (List.Mem.head _)

theorem lex_11_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.neg 97), (Sat.Literal.pos 44)] :=
  (lex_11_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.pos 97), (Sat.Literal.neg 44)] :=
  (lex_11_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.neg 97), (Sat.Literal.neg 44), (Sat.Literal.pos 4578)] :=
  (lex_11_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4577), (Sat.Literal.pos 97), (Sat.Literal.pos 44), (Sat.Literal.pos 4578)] :=
  (lex_11_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4578) = lexBefore s permutation11 96 := by
  exact (positive_lex_of_descriptor s 4578 permutation11 97 (by rfl)).trans ((lex_skipped s permutation11 96 97 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation11 96) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation11 96 by rw [image11_eq]; rfl))

theorem lex_11_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4579) (Sat.Literal.pos 4578) (Sat.Literal.pos 96) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation11 96 (assignment s)
    (Sat.Literal.pos 4579) (Sat.Literal.pos 4578) (Sat.Literal.pos 96) (Sat.Literal.pos 12) (positive_of_descriptor s 4579 (.lex permutation11 96) (by rfl)) (lex_11_96_prefix s) (positive_select s 96) (lex_11_96_image s)

theorem lex_11_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.pos 96), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation11 96 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4578) (Sat.Literal.pos 96) (Sat.Literal.pos 12) (lex_11_96_prefix s) (positive_select s 96) (lex_11_96_image s)

theorem lex_11_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.pos 4578)] :=
  (lex_11_96_gate s).prop _ (List.Mem.head _)

theorem lex_11_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.neg 96), (Sat.Literal.pos 12)] :=
  (lex_11_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.pos 96), (Sat.Literal.neg 12)] :=
  (lex_11_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.neg 96), (Sat.Literal.neg 12), (Sat.Literal.pos 4579)] :=
  (lex_11_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4578), (Sat.Literal.pos 96), (Sat.Literal.pos 12), (Sat.Literal.pos 4579)] :=
  (lex_11_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4579) = lexBefore s permutation11 95 := by
  exact (positive_lex_of_descriptor s 4579 permutation11 96 (by rfl)).trans ((lex_skipped s permutation11 95 96 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation11 95) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation11 95 by rw [image11_eq]; rfl))

theorem lex_11_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4580) (Sat.Literal.pos 4579) (Sat.Literal.pos 95) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation11 95 (assignment s)
    (Sat.Literal.pos 4580) (Sat.Literal.pos 4579) (Sat.Literal.pos 95) (Sat.Literal.pos 235) (positive_of_descriptor s 4580 (.lex permutation11 95) (by rfl)) (lex_11_95_prefix s) (positive_select s 95) (lex_11_95_image s)

theorem lex_11_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.pos 95), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation11 95 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4579) (Sat.Literal.pos 95) (Sat.Literal.pos 235) (lex_11_95_prefix s) (positive_select s 95) (lex_11_95_image s)

theorem lex_11_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.pos 4579)] :=
  (lex_11_95_gate s).prop _ (List.Mem.head _)

theorem lex_11_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.neg 95), (Sat.Literal.pos 235)] :=
  (lex_11_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.pos 95), (Sat.Literal.neg 235)] :=
  (lex_11_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.neg 95), (Sat.Literal.neg 235), (Sat.Literal.pos 4580)] :=
  (lex_11_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4579), (Sat.Literal.pos 95), (Sat.Literal.pos 235), (Sat.Literal.pos 4580)] :=
  (lex_11_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4580) = lexBefore s permutation11 94 := by
  exact (positive_lex_of_descriptor s 4580 permutation11 95 (by rfl)).trans ((lex_skipped s permutation11 94 95 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation11 94) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation11 94 by rw [image11_eq]; rfl))

theorem lex_11_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4581) (Sat.Literal.pos 4580) (Sat.Literal.pos 94) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation11 94 (assignment s)
    (Sat.Literal.pos 4581) (Sat.Literal.pos 4580) (Sat.Literal.pos 94) (Sat.Literal.pos 203) (positive_of_descriptor s 4581 (.lex permutation11 94) (by rfl)) (lex_11_94_prefix s) (positive_select s 94) (lex_11_94_image s)

theorem lex_11_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.pos 94), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation11 94 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4580) (Sat.Literal.pos 94) (Sat.Literal.pos 203) (lex_11_94_prefix s) (positive_select s 94) (lex_11_94_image s)

theorem lex_11_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.pos 4580)] :=
  (lex_11_94_gate s).prop _ (List.Mem.head _)

theorem lex_11_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.neg 94), (Sat.Literal.pos 203)] :=
  (lex_11_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.pos 94), (Sat.Literal.neg 203)] :=
  (lex_11_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.neg 94), (Sat.Literal.neg 203), (Sat.Literal.pos 4581)] :=
  (lex_11_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4580), (Sat.Literal.pos 94), (Sat.Literal.pos 203), (Sat.Literal.pos 4581)] :=
  (lex_11_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4581) = lexBefore s permutation11 93 := by
  exact (positive_lex_of_descriptor s 4581 permutation11 94 (by rfl)).trans ((lex_skipped s permutation11 93 94 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation11 93) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation11 93 by rw [image11_eq]; rfl))

theorem lex_11_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4582) (Sat.Literal.pos 4581) (Sat.Literal.pos 93) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation11 93 (assignment s)
    (Sat.Literal.pos 4582) (Sat.Literal.pos 4581) (Sat.Literal.pos 93) (Sat.Literal.pos 171) (positive_of_descriptor s 4582 (.lex permutation11 93) (by rfl)) (lex_11_93_prefix s) (positive_select s 93) (lex_11_93_image s)

theorem lex_11_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.pos 93), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation11 93 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4581) (Sat.Literal.pos 93) (Sat.Literal.pos 171) (lex_11_93_prefix s) (positive_select s 93) (lex_11_93_image s)

theorem lex_11_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.pos 4581)] :=
  (lex_11_93_gate s).prop _ (List.Mem.head _)

theorem lex_11_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.neg 93), (Sat.Literal.pos 171)] :=
  (lex_11_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.pos 93), (Sat.Literal.neg 171)] :=
  (lex_11_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.neg 93), (Sat.Literal.neg 171), (Sat.Literal.pos 4582)] :=
  (lex_11_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4581), (Sat.Literal.pos 93), (Sat.Literal.pos 171), (Sat.Literal.pos 4582)] :=
  (lex_11_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4582) = lexBefore s permutation11 92 := by
  exact (positive_lex_of_descriptor s 4582 permutation11 93 (by rfl)).trans ((lex_skipped s permutation11 92 93 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation11 92) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation11 92 by rw [image11_eq]; rfl))

theorem lex_11_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4583) (Sat.Literal.pos 4582) (Sat.Literal.pos 92) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation11 92 (assignment s)
    (Sat.Literal.pos 4583) (Sat.Literal.pos 4582) (Sat.Literal.pos 92) (Sat.Literal.pos 139) (positive_of_descriptor s 4583 (.lex permutation11 92) (by rfl)) (lex_11_92_prefix s) (positive_select s 92) (lex_11_92_image s)

theorem lex_11_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.pos 92), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation11 92 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4582) (Sat.Literal.pos 92) (Sat.Literal.pos 139) (lex_11_92_prefix s) (positive_select s 92) (lex_11_92_image s)

theorem lex_11_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.pos 4582)] :=
  (lex_11_92_gate s).prop _ (List.Mem.head _)

theorem lex_11_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.neg 92), (Sat.Literal.pos 139)] :=
  (lex_11_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.pos 92), (Sat.Literal.neg 139)] :=
  (lex_11_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.neg 92), (Sat.Literal.neg 139), (Sat.Literal.pos 4583)] :=
  (lex_11_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4582), (Sat.Literal.pos 92), (Sat.Literal.pos 139), (Sat.Literal.pos 4583)] :=
  (lex_11_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4583) = lexBefore s permutation11 91 := by
  exact (positive_lex_of_descriptor s 4583 permutation11 92 (by rfl)).trans ((lex_skipped s permutation11 91 92 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation11 91) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation11 91 by rw [image11_eq]; rfl))

theorem lex_11_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4584) (Sat.Literal.pos 4583) (Sat.Literal.pos 91) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation11 91 (assignment s)
    (Sat.Literal.pos 4584) (Sat.Literal.pos 4583) (Sat.Literal.pos 91) (Sat.Literal.pos 107) (positive_of_descriptor s 4584 (.lex permutation11 91) (by rfl)) (lex_11_91_prefix s) (positive_select s 91) (lex_11_91_image s)

theorem lex_11_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.pos 91), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation11 91 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4583) (Sat.Literal.pos 91) (Sat.Literal.pos 107) (lex_11_91_prefix s) (positive_select s 91) (lex_11_91_image s)

theorem lex_11_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.pos 4583)] :=
  (lex_11_91_gate s).prop _ (List.Mem.head _)

theorem lex_11_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.neg 91), (Sat.Literal.pos 107)] :=
  (lex_11_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.pos 91), (Sat.Literal.neg 107)] :=
  (lex_11_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.neg 91), (Sat.Literal.neg 107), (Sat.Literal.pos 4584)] :=
  (lex_11_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4583), (Sat.Literal.pos 91), (Sat.Literal.pos 107), (Sat.Literal.pos 4584)] :=
  (lex_11_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4584) = lexBefore s permutation11 90 := by
  exact (positive_lex_of_descriptor s 4584 permutation11 91 (by rfl)).trans ((lex_skipped s permutation11 90 91 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation11 90) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation11 90 by rw [image11_eq]; rfl))

theorem lex_11_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4585) (Sat.Literal.pos 4584) (Sat.Literal.pos 90) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation11 90 (assignment s)
    (Sat.Literal.pos 4585) (Sat.Literal.pos 4584) (Sat.Literal.pos 90) (Sat.Literal.pos 75) (positive_of_descriptor s 4585 (.lex permutation11 90) (by rfl)) (lex_11_90_prefix s) (positive_select s 90) (lex_11_90_image s)

theorem lex_11_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.pos 90), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation11 90 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4584) (Sat.Literal.pos 90) (Sat.Literal.pos 75) (lex_11_90_prefix s) (positive_select s 90) (lex_11_90_image s)

theorem lex_11_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.pos 4584)] :=
  (lex_11_90_gate s).prop _ (List.Mem.head _)

theorem lex_11_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.neg 90), (Sat.Literal.pos 75)] :=
  (lex_11_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.pos 90), (Sat.Literal.neg 75)] :=
  (lex_11_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.neg 90), (Sat.Literal.neg 75), (Sat.Literal.pos 4585)] :=
  (lex_11_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4584), (Sat.Literal.pos 90), (Sat.Literal.pos 75), (Sat.Literal.pos 4585)] :=
  (lex_11_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4585) = lexBefore s permutation11 89 := by
  exact (positive_lex_of_descriptor s 4585 permutation11 90 (by rfl)).trans ((lex_skipped s permutation11 89 90 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation11 89) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation11 89 by rw [image11_eq]; rfl))

theorem lex_11_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4586) (Sat.Literal.pos 4585) (Sat.Literal.pos 89) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation11 89 (assignment s)
    (Sat.Literal.pos 4586) (Sat.Literal.pos 4585) (Sat.Literal.pos 89) (Sat.Literal.pos 43) (positive_of_descriptor s 4586 (.lex permutation11 89) (by rfl)) (lex_11_89_prefix s) (positive_select s 89) (lex_11_89_image s)

theorem lex_11_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.pos 89), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation11 89 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4585) (Sat.Literal.pos 89) (Sat.Literal.pos 43) (lex_11_89_prefix s) (positive_select s 89) (lex_11_89_image s)

theorem lex_11_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.pos 4585)] :=
  (lex_11_89_gate s).prop _ (List.Mem.head _)

theorem lex_11_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.neg 89), (Sat.Literal.pos 43)] :=
  (lex_11_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.pos 89), (Sat.Literal.neg 43)] :=
  (lex_11_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.neg 89), (Sat.Literal.neg 43), (Sat.Literal.pos 4586)] :=
  (lex_11_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4585), (Sat.Literal.pos 89), (Sat.Literal.pos 43), (Sat.Literal.pos 4586)] :=
  (lex_11_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4586) = lexBefore s permutation11 88 := by
  exact (positive_lex_of_descriptor s 4586 permutation11 89 (by rfl)).trans ((lex_skipped s permutation11 88 89 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation11 88) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation11 88 by rw [image11_eq]; rfl))

theorem lex_11_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4587) (Sat.Literal.pos 4586) (Sat.Literal.pos 88) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation11 88 (assignment s)
    (Sat.Literal.pos 4587) (Sat.Literal.pos 4586) (Sat.Literal.pos 88) (Sat.Literal.pos 11) (positive_of_descriptor s 4587 (.lex permutation11 88) (by rfl)) (lex_11_88_prefix s) (positive_select s 88) (lex_11_88_image s)

theorem lex_11_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.pos 88), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation11 88 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4586) (Sat.Literal.pos 88) (Sat.Literal.pos 11) (lex_11_88_prefix s) (positive_select s 88) (lex_11_88_image s)

theorem lex_11_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.pos 4586)] :=
  (lex_11_88_gate s).prop _ (List.Mem.head _)

theorem lex_11_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.neg 88), (Sat.Literal.pos 11)] :=
  (lex_11_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.pos 88), (Sat.Literal.neg 11)] :=
  (lex_11_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.neg 88), (Sat.Literal.neg 11), (Sat.Literal.pos 4587)] :=
  (lex_11_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4586), (Sat.Literal.pos 88), (Sat.Literal.pos 11), (Sat.Literal.pos 4587)] :=
  (lex_11_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4587) = lexBefore s permutation11 87 := by
  exact (positive_lex_of_descriptor s 4587 permutation11 88 (by rfl)).trans ((lex_skipped s permutation11 87 88 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation11 87) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation11 87 by rw [image11_eq]; rfl))

theorem lex_11_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4588) (Sat.Literal.pos 4587) (Sat.Literal.pos 87) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation11 87 (assignment s)
    (Sat.Literal.pos 4588) (Sat.Literal.pos 4587) (Sat.Literal.pos 87) (Sat.Literal.pos 234) (positive_of_descriptor s 4588 (.lex permutation11 87) (by rfl)) (lex_11_87_prefix s) (positive_select s 87) (lex_11_87_image s)

theorem lex_11_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.pos 87), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation11 87 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4587) (Sat.Literal.pos 87) (Sat.Literal.pos 234) (lex_11_87_prefix s) (positive_select s 87) (lex_11_87_image s)

theorem lex_11_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.pos 4587)] :=
  (lex_11_87_gate s).prop _ (List.Mem.head _)

theorem lex_11_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.neg 87), (Sat.Literal.pos 234)] :=
  (lex_11_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.pos 87), (Sat.Literal.neg 234)] :=
  (lex_11_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.neg 87), (Sat.Literal.neg 234), (Sat.Literal.pos 4588)] :=
  (lex_11_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4587), (Sat.Literal.pos 87), (Sat.Literal.pos 234), (Sat.Literal.pos 4588)] :=
  (lex_11_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4588) = lexBefore s permutation11 86 := by
  exact (positive_lex_of_descriptor s 4588 permutation11 87 (by rfl)).trans ((lex_skipped s permutation11 86 87 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation11 86) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation11 86 by rw [image11_eq]; rfl))

theorem lex_11_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4589) (Sat.Literal.pos 4588) (Sat.Literal.pos 86) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation11 86 (assignment s)
    (Sat.Literal.pos 4589) (Sat.Literal.pos 4588) (Sat.Literal.pos 86) (Sat.Literal.pos 202) (positive_of_descriptor s 4589 (.lex permutation11 86) (by rfl)) (lex_11_86_prefix s) (positive_select s 86) (lex_11_86_image s)

theorem lex_11_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.pos 86), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation11 86 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4588) (Sat.Literal.pos 86) (Sat.Literal.pos 202) (lex_11_86_prefix s) (positive_select s 86) (lex_11_86_image s)

theorem lex_11_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.pos 4588)] :=
  (lex_11_86_gate s).prop _ (List.Mem.head _)

theorem lex_11_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.neg 86), (Sat.Literal.pos 202)] :=
  (lex_11_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.pos 86), (Sat.Literal.neg 202)] :=
  (lex_11_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.neg 86), (Sat.Literal.neg 202), (Sat.Literal.pos 4589)] :=
  (lex_11_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4588), (Sat.Literal.pos 86), (Sat.Literal.pos 202), (Sat.Literal.pos 4589)] :=
  (lex_11_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4589) = lexBefore s permutation11 85 := by
  exact (positive_lex_of_descriptor s 4589 permutation11 86 (by rfl)).trans ((lex_skipped s permutation11 85 86 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation11 85) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation11 85 by rw [image11_eq]; rfl))

theorem lex_11_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4590) (Sat.Literal.pos 4589) (Sat.Literal.pos 85) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation11 85 (assignment s)
    (Sat.Literal.pos 4590) (Sat.Literal.pos 4589) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (positive_of_descriptor s 4590 (.lex permutation11 85) (by rfl)) (lex_11_85_prefix s) (positive_select s 85) (lex_11_85_image s)

theorem lex_11_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation11 85 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4589) (Sat.Literal.pos 85) (Sat.Literal.pos 170) (lex_11_85_prefix s) (positive_select s 85) (lex_11_85_image s)

theorem lex_11_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.pos 4589)] :=
  (lex_11_85_gate s).prop _ (List.Mem.head _)

theorem lex_11_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.neg 85), (Sat.Literal.pos 170)] :=
  (lex_11_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.pos 85), (Sat.Literal.neg 170)] :=
  (lex_11_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.neg 85), (Sat.Literal.neg 170), (Sat.Literal.pos 4590)] :=
  (lex_11_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4589), (Sat.Literal.pos 85), (Sat.Literal.pos 170), (Sat.Literal.pos 4590)] :=
  (lex_11_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4590) = lexBefore s permutation11 84 := by
  exact (positive_lex_of_descriptor s 4590 permutation11 85 (by rfl)).trans ((lex_skipped s permutation11 84 85 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation11 84) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation11 84 by rw [image11_eq]; rfl))

theorem lex_11_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4591) (Sat.Literal.pos 4590) (Sat.Literal.pos 84) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation11 84 (assignment s)
    (Sat.Literal.pos 4591) (Sat.Literal.pos 4590) (Sat.Literal.pos 84) (Sat.Literal.pos 138) (positive_of_descriptor s 4591 (.lex permutation11 84) (by rfl)) (lex_11_84_prefix s) (positive_select s 84) (lex_11_84_image s)

theorem lex_11_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.pos 84), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation11 84 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4590) (Sat.Literal.pos 84) (Sat.Literal.pos 138) (lex_11_84_prefix s) (positive_select s 84) (lex_11_84_image s)

theorem lex_11_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.pos 4590)] :=
  (lex_11_84_gate s).prop _ (List.Mem.head _)

theorem lex_11_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.neg 84), (Sat.Literal.pos 138)] :=
  (lex_11_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.pos 84), (Sat.Literal.neg 138)] :=
  (lex_11_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.neg 84), (Sat.Literal.neg 138), (Sat.Literal.pos 4591)] :=
  (lex_11_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4590), (Sat.Literal.pos 84), (Sat.Literal.pos 138), (Sat.Literal.pos 4591)] :=
  (lex_11_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4591) = lexBefore s permutation11 83 := by
  exact (positive_lex_of_descriptor s 4591 permutation11 84 (by rfl)).trans ((lex_skipped s permutation11 83 84 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation11 83) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation11 83 by rw [image11_eq]; rfl))

theorem lex_11_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4592) (Sat.Literal.pos 4591) (Sat.Literal.pos 83) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation11 83 (assignment s)
    (Sat.Literal.pos 4592) (Sat.Literal.pos 4591) (Sat.Literal.pos 83) (Sat.Literal.pos 106) (positive_of_descriptor s 4592 (.lex permutation11 83) (by rfl)) (lex_11_83_prefix s) (positive_select s 83) (lex_11_83_image s)

theorem lex_11_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.pos 83), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation11 83 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4591) (Sat.Literal.pos 83) (Sat.Literal.pos 106) (lex_11_83_prefix s) (positive_select s 83) (lex_11_83_image s)

theorem lex_11_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.pos 4591)] :=
  (lex_11_83_gate s).prop _ (List.Mem.head _)

theorem lex_11_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.neg 83), (Sat.Literal.pos 106)] :=
  (lex_11_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.pos 83), (Sat.Literal.neg 106)] :=
  (lex_11_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.neg 83), (Sat.Literal.neg 106), (Sat.Literal.pos 4592)] :=
  (lex_11_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4591), (Sat.Literal.pos 83), (Sat.Literal.pos 106), (Sat.Literal.pos 4592)] :=
  (lex_11_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4592) = lexBefore s permutation11 82 := by
  exact (positive_lex_of_descriptor s 4592 permutation11 83 (by rfl)).trans ((lex_skipped s permutation11 82 83 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation11 82) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation11 82 by rw [image11_eq]; rfl))

theorem lex_11_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4593) (Sat.Literal.pos 4592) (Sat.Literal.pos 82) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation11 82 (assignment s)
    (Sat.Literal.pos 4593) (Sat.Literal.pos 4592) (Sat.Literal.pos 82) (Sat.Literal.pos 74) (positive_of_descriptor s 4593 (.lex permutation11 82) (by rfl)) (lex_11_82_prefix s) (positive_select s 82) (lex_11_82_image s)

theorem lex_11_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.pos 82), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation11 82 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4592) (Sat.Literal.pos 82) (Sat.Literal.pos 74) (lex_11_82_prefix s) (positive_select s 82) (lex_11_82_image s)

theorem lex_11_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.pos 4592)] :=
  (lex_11_82_gate s).prop _ (List.Mem.head _)

theorem lex_11_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.neg 82), (Sat.Literal.pos 74)] :=
  (lex_11_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.pos 82), (Sat.Literal.neg 74)] :=
  (lex_11_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.neg 82), (Sat.Literal.neg 74), (Sat.Literal.pos 4593)] :=
  (lex_11_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4592), (Sat.Literal.pos 82), (Sat.Literal.pos 74), (Sat.Literal.pos 4593)] :=
  (lex_11_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4593) = lexBefore s permutation11 81 := by
  exact (positive_lex_of_descriptor s 4593 permutation11 82 (by rfl)).trans ((lex_skipped s permutation11 81 82 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation11 81) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation11 81 by rw [image11_eq]; rfl))

theorem lex_11_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4594) (Sat.Literal.pos 4593) (Sat.Literal.pos 81) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation11 81 (assignment s)
    (Sat.Literal.pos 4594) (Sat.Literal.pos 4593) (Sat.Literal.pos 81) (Sat.Literal.pos 42) (positive_of_descriptor s 4594 (.lex permutation11 81) (by rfl)) (lex_11_81_prefix s) (positive_select s 81) (lex_11_81_image s)

theorem lex_11_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.pos 81), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation11 81 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4593) (Sat.Literal.pos 81) (Sat.Literal.pos 42) (lex_11_81_prefix s) (positive_select s 81) (lex_11_81_image s)

theorem lex_11_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.pos 4593)] :=
  (lex_11_81_gate s).prop _ (List.Mem.head _)

theorem lex_11_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.neg 81), (Sat.Literal.pos 42)] :=
  (lex_11_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.pos 81), (Sat.Literal.neg 42)] :=
  (lex_11_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.neg 81), (Sat.Literal.neg 42), (Sat.Literal.pos 4594)] :=
  (lex_11_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4593), (Sat.Literal.pos 81), (Sat.Literal.pos 42), (Sat.Literal.pos 4594)] :=
  (lex_11_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4594) = lexBefore s permutation11 80 := by
  exact (positive_lex_of_descriptor s 4594 permutation11 81 (by rfl)).trans ((lex_skipped s permutation11 80 81 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation11 80) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation11 80 by rw [image11_eq]; rfl))

theorem lex_11_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4595) (Sat.Literal.pos 4594) (Sat.Literal.pos 80) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation11 80 (assignment s)
    (Sat.Literal.pos 4595) (Sat.Literal.pos 4594) (Sat.Literal.pos 80) (Sat.Literal.pos 10) (positive_of_descriptor s 4595 (.lex permutation11 80) (by rfl)) (lex_11_80_prefix s) (positive_select s 80) (lex_11_80_image s)

theorem lex_11_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.pos 80), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation11 80 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4594) (Sat.Literal.pos 80) (Sat.Literal.pos 10) (lex_11_80_prefix s) (positive_select s 80) (lex_11_80_image s)

theorem lex_11_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.pos 4594)] :=
  (lex_11_80_gate s).prop _ (List.Mem.head _)

theorem lex_11_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.neg 80), (Sat.Literal.pos 10)] :=
  (lex_11_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.pos 80), (Sat.Literal.neg 10)] :=
  (lex_11_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.neg 80), (Sat.Literal.neg 10), (Sat.Literal.pos 4595)] :=
  (lex_11_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4594), (Sat.Literal.pos 80), (Sat.Literal.pos 10), (Sat.Literal.pos 4595)] :=
  (lex_11_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4595) = lexBefore s permutation11 79 := by
  exact (positive_lex_of_descriptor s 4595 permutation11 80 (by rfl)).trans ((lex_skipped s permutation11 79 80 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation11 79) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation11 79 by rw [image11_eq]; rfl))

theorem lex_11_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4596) (Sat.Literal.pos 4595) (Sat.Literal.pos 79) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation11 79 (assignment s)
    (Sat.Literal.pos 4596) (Sat.Literal.pos 4595) (Sat.Literal.pos 79) (Sat.Literal.pos 233) (positive_of_descriptor s 4596 (.lex permutation11 79) (by rfl)) (lex_11_79_prefix s) (positive_select s 79) (lex_11_79_image s)

theorem lex_11_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.pos 79), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation11 79 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4595) (Sat.Literal.pos 79) (Sat.Literal.pos 233) (lex_11_79_prefix s) (positive_select s 79) (lex_11_79_image s)

theorem lex_11_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.pos 4595)] :=
  (lex_11_79_gate s).prop _ (List.Mem.head _)

theorem lex_11_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.neg 79), (Sat.Literal.pos 233)] :=
  (lex_11_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.pos 79), (Sat.Literal.neg 233)] :=
  (lex_11_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.neg 79), (Sat.Literal.neg 233), (Sat.Literal.pos 4596)] :=
  (lex_11_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4595), (Sat.Literal.pos 79), (Sat.Literal.pos 233), (Sat.Literal.pos 4596)] :=
  (lex_11_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4596) = lexBefore s permutation11 78 := by
  exact (positive_lex_of_descriptor s 4596 permutation11 79 (by rfl)).trans ((lex_skipped s permutation11 78 79 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation11 78) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation11 78 by rw [image11_eq]; rfl))

theorem lex_11_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4597) (Sat.Literal.pos 4596) (Sat.Literal.pos 78) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation11 78 (assignment s)
    (Sat.Literal.pos 4597) (Sat.Literal.pos 4596) (Sat.Literal.pos 78) (Sat.Literal.pos 201) (positive_of_descriptor s 4597 (.lex permutation11 78) (by rfl)) (lex_11_78_prefix s) (positive_select s 78) (lex_11_78_image s)

theorem lex_11_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.pos 78), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation11 78 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4596) (Sat.Literal.pos 78) (Sat.Literal.pos 201) (lex_11_78_prefix s) (positive_select s 78) (lex_11_78_image s)

theorem lex_11_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.pos 4596)] :=
  (lex_11_78_gate s).prop _ (List.Mem.head _)

theorem lex_11_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.neg 78), (Sat.Literal.pos 201)] :=
  (lex_11_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.pos 78), (Sat.Literal.neg 201)] :=
  (lex_11_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.neg 78), (Sat.Literal.neg 201), (Sat.Literal.pos 4597)] :=
  (lex_11_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4596), (Sat.Literal.pos 78), (Sat.Literal.pos 201), (Sat.Literal.pos 4597)] :=
  (lex_11_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4597) = lexBefore s permutation11 77 := by
  exact (positive_lex_of_descriptor s 4597 permutation11 78 (by rfl)).trans ((lex_skipped s permutation11 77 78 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation11 77) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation11 77 by rw [image11_eq]; rfl))

theorem lex_11_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4598) (Sat.Literal.pos 4597) (Sat.Literal.pos 77) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation11 77 (assignment s)
    (Sat.Literal.pos 4598) (Sat.Literal.pos 4597) (Sat.Literal.pos 77) (Sat.Literal.pos 169) (positive_of_descriptor s 4598 (.lex permutation11 77) (by rfl)) (lex_11_77_prefix s) (positive_select s 77) (lex_11_77_image s)

theorem lex_11_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.pos 77), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation11 77 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4597) (Sat.Literal.pos 77) (Sat.Literal.pos 169) (lex_11_77_prefix s) (positive_select s 77) (lex_11_77_image s)

theorem lex_11_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.pos 4597)] :=
  (lex_11_77_gate s).prop _ (List.Mem.head _)

theorem lex_11_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.neg 77), (Sat.Literal.pos 169)] :=
  (lex_11_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.pos 77), (Sat.Literal.neg 169)] :=
  (lex_11_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.neg 77), (Sat.Literal.neg 169), (Sat.Literal.pos 4598)] :=
  (lex_11_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4597), (Sat.Literal.pos 77), (Sat.Literal.pos 169), (Sat.Literal.pos 4598)] :=
  (lex_11_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4598) = lexBefore s permutation11 76 := by
  exact (positive_lex_of_descriptor s 4598 permutation11 77 (by rfl)).trans ((lex_skipped s permutation11 76 77 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation11 76) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation11 76 by rw [image11_eq]; rfl))

theorem lex_11_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4599) (Sat.Literal.pos 4598) (Sat.Literal.pos 76) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation11 76 (assignment s)
    (Sat.Literal.pos 4599) (Sat.Literal.pos 4598) (Sat.Literal.pos 76) (Sat.Literal.pos 137) (positive_of_descriptor s 4599 (.lex permutation11 76) (by rfl)) (lex_11_76_prefix s) (positive_select s 76) (lex_11_76_image s)

theorem lex_11_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.pos 76), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation11 76 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4598) (Sat.Literal.pos 76) (Sat.Literal.pos 137) (lex_11_76_prefix s) (positive_select s 76) (lex_11_76_image s)

theorem lex_11_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.pos 4598)] :=
  (lex_11_76_gate s).prop _ (List.Mem.head _)

theorem lex_11_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.neg 76), (Sat.Literal.pos 137)] :=
  (lex_11_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.pos 76), (Sat.Literal.neg 137)] :=
  (lex_11_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.neg 76), (Sat.Literal.neg 137), (Sat.Literal.pos 4599)] :=
  (lex_11_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4598), (Sat.Literal.pos 76), (Sat.Literal.pos 137), (Sat.Literal.pos 4599)] :=
  (lex_11_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4599) = lexBefore s permutation11 75 := by
  exact (positive_lex_of_descriptor s 4599 permutation11 76 (by rfl)).trans ((lex_skipped s permutation11 75 76 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation11 75) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation11 75 by rw [image11_eq]; rfl))

theorem lex_11_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4600) (Sat.Literal.pos 4599) (Sat.Literal.pos 75) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation11 75 (assignment s)
    (Sat.Literal.pos 4600) (Sat.Literal.pos 4599) (Sat.Literal.pos 75) (Sat.Literal.pos 105) (positive_of_descriptor s 4600 (.lex permutation11 75) (by rfl)) (lex_11_75_prefix s) (positive_select s 75) (lex_11_75_image s)

theorem lex_11_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.pos 75), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation11 75 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4599) (Sat.Literal.pos 75) (Sat.Literal.pos 105) (lex_11_75_prefix s) (positive_select s 75) (lex_11_75_image s)

theorem lex_11_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.pos 4599)] :=
  (lex_11_75_gate s).prop _ (List.Mem.head _)

theorem lex_11_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.neg 75), (Sat.Literal.pos 105)] :=
  (lex_11_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.pos 75), (Sat.Literal.neg 105)] :=
  (lex_11_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.neg 75), (Sat.Literal.neg 105), (Sat.Literal.pos 4600)] :=
  (lex_11_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4599), (Sat.Literal.pos 75), (Sat.Literal.pos 105), (Sat.Literal.pos 4600)] :=
  (lex_11_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4600) = lexBefore s permutation11 74 := by
  exact (positive_lex_of_descriptor s 4600 permutation11 75 (by rfl)).trans ((lex_skipped s permutation11 74 75 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation11 74) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation11 74 by rw [image11_eq]; rfl))

theorem lex_11_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4601) (Sat.Literal.pos 4600) (Sat.Literal.pos 74) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation11 74 (assignment s)
    (Sat.Literal.pos 4601) (Sat.Literal.pos 4600) (Sat.Literal.pos 74) (Sat.Literal.pos 73) (positive_of_descriptor s 4601 (.lex permutation11 74) (by rfl)) (lex_11_74_prefix s) (positive_select s 74) (lex_11_74_image s)

theorem lex_11_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.pos 74), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation11 74 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4600) (Sat.Literal.pos 74) (Sat.Literal.pos 73) (lex_11_74_prefix s) (positive_select s 74) (lex_11_74_image s)

theorem lex_11_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.pos 4600)] :=
  (lex_11_74_gate s).prop _ (List.Mem.head _)

theorem lex_11_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.neg 74), (Sat.Literal.pos 73)] :=
  (lex_11_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.pos 74), (Sat.Literal.neg 73)] :=
  (lex_11_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.neg 74), (Sat.Literal.neg 73), (Sat.Literal.pos 4601)] :=
  (lex_11_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4600), (Sat.Literal.pos 74), (Sat.Literal.pos 73), (Sat.Literal.pos 4601)] :=
  (lex_11_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4601) = lexBefore s permutation11 73 := by
  exact (positive_lex_of_descriptor s 4601 permutation11 74 (by rfl)).trans ((lex_skipped s permutation11 73 74 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation11 73) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation11 73 by rw [image11_eq]; rfl))

theorem lex_11_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4602) (Sat.Literal.pos 4601) (Sat.Literal.pos 73) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation11 73 (assignment s)
    (Sat.Literal.pos 4602) (Sat.Literal.pos 4601) (Sat.Literal.pos 73) (Sat.Literal.pos 41) (positive_of_descriptor s 4602 (.lex permutation11 73) (by rfl)) (lex_11_73_prefix s) (positive_select s 73) (lex_11_73_image s)

theorem lex_11_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.pos 73), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation11 73 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4601) (Sat.Literal.pos 73) (Sat.Literal.pos 41) (lex_11_73_prefix s) (positive_select s 73) (lex_11_73_image s)

theorem lex_11_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.pos 4601)] :=
  (lex_11_73_gate s).prop _ (List.Mem.head _)

theorem lex_11_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.neg 73), (Sat.Literal.pos 41)] :=
  (lex_11_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.pos 73), (Sat.Literal.neg 41)] :=
  (lex_11_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.neg 73), (Sat.Literal.neg 41), (Sat.Literal.pos 4602)] :=
  (lex_11_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4601), (Sat.Literal.pos 73), (Sat.Literal.pos 41), (Sat.Literal.pos 4602)] :=
  (lex_11_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4602) = lexBefore s permutation11 72 := by
  exact (positive_lex_of_descriptor s 4602 permutation11 73 (by rfl)).trans ((lex_skipped s permutation11 72 73 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation11 72) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation11 72 by rw [image11_eq]; rfl))

theorem lex_11_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4603) (Sat.Literal.pos 4602) (Sat.Literal.pos 72) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation11 72 (assignment s)
    (Sat.Literal.pos 4603) (Sat.Literal.pos 4602) (Sat.Literal.pos 72) (Sat.Literal.pos 9) (positive_of_descriptor s 4603 (.lex permutation11 72) (by rfl)) (lex_11_72_prefix s) (positive_select s 72) (lex_11_72_image s)

theorem lex_11_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.pos 72), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation11 72 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4602) (Sat.Literal.pos 72) (Sat.Literal.pos 9) (lex_11_72_prefix s) (positive_select s 72) (lex_11_72_image s)

theorem lex_11_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.pos 4602)] :=
  (lex_11_72_gate s).prop _ (List.Mem.head _)

theorem lex_11_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.neg 72), (Sat.Literal.pos 9)] :=
  (lex_11_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.pos 72), (Sat.Literal.neg 9)] :=
  (lex_11_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.neg 72), (Sat.Literal.neg 9), (Sat.Literal.pos 4603)] :=
  (lex_11_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4602), (Sat.Literal.pos 72), (Sat.Literal.pos 9), (Sat.Literal.pos 4603)] :=
  (lex_11_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4603) = lexBefore s permutation11 71 := by
  exact (positive_lex_of_descriptor s 4603 permutation11 72 (by rfl)).trans ((lex_skipped s permutation11 71 72 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation11 71) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation11 71 by rw [image11_eq]; rfl))

theorem lex_11_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4604) (Sat.Literal.pos 4603) (Sat.Literal.pos 71) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation11 71 (assignment s)
    (Sat.Literal.pos 4604) (Sat.Literal.pos 4603) (Sat.Literal.pos 71) (Sat.Literal.pos 232) (positive_of_descriptor s 4604 (.lex permutation11 71) (by rfl)) (lex_11_71_prefix s) (positive_select s 71) (lex_11_71_image s)

theorem lex_11_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.pos 71), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation11 71 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4603) (Sat.Literal.pos 71) (Sat.Literal.pos 232) (lex_11_71_prefix s) (positive_select s 71) (lex_11_71_image s)

theorem lex_11_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.pos 4603)] :=
  (lex_11_71_gate s).prop _ (List.Mem.head _)

theorem lex_11_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.neg 71), (Sat.Literal.pos 232)] :=
  (lex_11_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.pos 71), (Sat.Literal.neg 232)] :=
  (lex_11_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.neg 71), (Sat.Literal.neg 232), (Sat.Literal.pos 4604)] :=
  (lex_11_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4603), (Sat.Literal.pos 71), (Sat.Literal.pos 232), (Sat.Literal.pos 4604)] :=
  (lex_11_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4604) = lexBefore s permutation11 70 := by
  exact (positive_lex_of_descriptor s 4604 permutation11 71 (by rfl)).trans ((lex_skipped s permutation11 70 71 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation11 70) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation11 70 by rw [image11_eq]; rfl))

theorem lex_11_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4605) (Sat.Literal.pos 4604) (Sat.Literal.pos 70) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation11 70 (assignment s)
    (Sat.Literal.pos 4605) (Sat.Literal.pos 4604) (Sat.Literal.pos 70) (Sat.Literal.pos 200) (positive_of_descriptor s 4605 (.lex permutation11 70) (by rfl)) (lex_11_70_prefix s) (positive_select s 70) (lex_11_70_image s)

theorem lex_11_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.pos 70), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation11 70 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4604) (Sat.Literal.pos 70) (Sat.Literal.pos 200) (lex_11_70_prefix s) (positive_select s 70) (lex_11_70_image s)

theorem lex_11_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.pos 4604)] :=
  (lex_11_70_gate s).prop _ (List.Mem.head _)

theorem lex_11_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.neg 70), (Sat.Literal.pos 200)] :=
  (lex_11_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.pos 70), (Sat.Literal.neg 200)] :=
  (lex_11_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.neg 70), (Sat.Literal.neg 200), (Sat.Literal.pos 4605)] :=
  (lex_11_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4604), (Sat.Literal.pos 70), (Sat.Literal.pos 200), (Sat.Literal.pos 4605)] :=
  (lex_11_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4605) = lexBefore s permutation11 69 := by
  exact (positive_lex_of_descriptor s 4605 permutation11 70 (by rfl)).trans ((lex_skipped s permutation11 69 70 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation11 69) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation11 69 by rw [image11_eq]; rfl))

theorem lex_11_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4606) (Sat.Literal.pos 4605) (Sat.Literal.pos 69) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation11 69 (assignment s)
    (Sat.Literal.pos 4606) (Sat.Literal.pos 4605) (Sat.Literal.pos 69) (Sat.Literal.pos 168) (positive_of_descriptor s 4606 (.lex permutation11 69) (by rfl)) (lex_11_69_prefix s) (positive_select s 69) (lex_11_69_image s)

theorem lex_11_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.pos 69), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation11 69 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4605) (Sat.Literal.pos 69) (Sat.Literal.pos 168) (lex_11_69_prefix s) (positive_select s 69) (lex_11_69_image s)

theorem lex_11_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.pos 4605)] :=
  (lex_11_69_gate s).prop _ (List.Mem.head _)

theorem lex_11_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.neg 69), (Sat.Literal.pos 168)] :=
  (lex_11_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.pos 69), (Sat.Literal.neg 168)] :=
  (lex_11_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.neg 69), (Sat.Literal.neg 168), (Sat.Literal.pos 4606)] :=
  (lex_11_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4605), (Sat.Literal.pos 69), (Sat.Literal.pos 168), (Sat.Literal.pos 4606)] :=
  (lex_11_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4606) = lexBefore s permutation11 68 := by
  exact (positive_lex_of_descriptor s 4606 permutation11 69 (by rfl)).trans ((lex_skipped s permutation11 68 69 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation11 68) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation11 68 by rw [image11_eq]; rfl))

theorem lex_11_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4607) (Sat.Literal.pos 4606) (Sat.Literal.pos 68) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation11 68 (assignment s)
    (Sat.Literal.pos 4607) (Sat.Literal.pos 4606) (Sat.Literal.pos 68) (Sat.Literal.pos 136) (positive_of_descriptor s 4607 (.lex permutation11 68) (by rfl)) (lex_11_68_prefix s) (positive_select s 68) (lex_11_68_image s)

theorem lex_11_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.pos 68), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation11 68 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4606) (Sat.Literal.pos 68) (Sat.Literal.pos 136) (lex_11_68_prefix s) (positive_select s 68) (lex_11_68_image s)

theorem lex_11_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.pos 4606)] :=
  (lex_11_68_gate s).prop _ (List.Mem.head _)

theorem lex_11_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.neg 68), (Sat.Literal.pos 136)] :=
  (lex_11_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.pos 68), (Sat.Literal.neg 136)] :=
  (lex_11_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.neg 68), (Sat.Literal.neg 136), (Sat.Literal.pos 4607)] :=
  (lex_11_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4606), (Sat.Literal.pos 68), (Sat.Literal.pos 136), (Sat.Literal.pos 4607)] :=
  (lex_11_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4607) = lexBefore s permutation11 67 := by
  exact (positive_lex_of_descriptor s 4607 permutation11 68 (by rfl)).trans ((lex_skipped s permutation11 67 68 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation11 67) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation11 67 by rw [image11_eq]; rfl))

theorem lex_11_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4608) (Sat.Literal.pos 4607) (Sat.Literal.pos 67) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation11 67 (assignment s)
    (Sat.Literal.pos 4608) (Sat.Literal.pos 4607) (Sat.Literal.pos 67) (Sat.Literal.pos 104) (positive_of_descriptor s 4608 (.lex permutation11 67) (by rfl)) (lex_11_67_prefix s) (positive_select s 67) (lex_11_67_image s)

theorem lex_11_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.pos 67), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation11 67 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4607) (Sat.Literal.pos 67) (Sat.Literal.pos 104) (lex_11_67_prefix s) (positive_select s 67) (lex_11_67_image s)

theorem lex_11_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.pos 4607)] :=
  (lex_11_67_gate s).prop _ (List.Mem.head _)

theorem lex_11_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.neg 67), (Sat.Literal.pos 104)] :=
  (lex_11_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.pos 67), (Sat.Literal.neg 104)] :=
  (lex_11_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.neg 67), (Sat.Literal.neg 104), (Sat.Literal.pos 4608)] :=
  (lex_11_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4607), (Sat.Literal.pos 67), (Sat.Literal.pos 104), (Sat.Literal.pos 4608)] :=
  (lex_11_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4608) = lexBefore s permutation11 66 := by
  exact (positive_lex_of_descriptor s 4608 permutation11 67 (by rfl)).trans ((lex_skipped s permutation11 66 67 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation11 66) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation11 66 by rw [image11_eq]; rfl))

theorem lex_11_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4609) (Sat.Literal.pos 4608) (Sat.Literal.pos 66) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation11 66 (assignment s)
    (Sat.Literal.pos 4609) (Sat.Literal.pos 4608) (Sat.Literal.pos 66) (Sat.Literal.pos 72) (positive_of_descriptor s 4609 (.lex permutation11 66) (by rfl)) (lex_11_66_prefix s) (positive_select s 66) (lex_11_66_image s)

theorem lex_11_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.pos 66), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation11 66 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4608) (Sat.Literal.pos 66) (Sat.Literal.pos 72) (lex_11_66_prefix s) (positive_select s 66) (lex_11_66_image s)

theorem lex_11_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.pos 4608)] :=
  (lex_11_66_gate s).prop _ (List.Mem.head _)

theorem lex_11_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.neg 66), (Sat.Literal.pos 72)] :=
  (lex_11_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.pos 66), (Sat.Literal.neg 72)] :=
  (lex_11_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.neg 66), (Sat.Literal.neg 72), (Sat.Literal.pos 4609)] :=
  (lex_11_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4608), (Sat.Literal.pos 66), (Sat.Literal.pos 72), (Sat.Literal.pos 4609)] :=
  (lex_11_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4609) = lexBefore s permutation11 65 := by
  exact (positive_lex_of_descriptor s 4609 permutation11 66 (by rfl)).trans ((lex_skipped s permutation11 65 66 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation11 65) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation11 65 by rw [image11_eq]; rfl))

theorem lex_11_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4610) (Sat.Literal.pos 4609) (Sat.Literal.pos 65) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation11 65 (assignment s)
    (Sat.Literal.pos 4610) (Sat.Literal.pos 4609) (Sat.Literal.pos 65) (Sat.Literal.pos 40) (positive_of_descriptor s 4610 (.lex permutation11 65) (by rfl)) (lex_11_65_prefix s) (positive_select s 65) (lex_11_65_image s)

theorem lex_11_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.pos 65), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation11 65 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4609) (Sat.Literal.pos 65) (Sat.Literal.pos 40) (lex_11_65_prefix s) (positive_select s 65) (lex_11_65_image s)

theorem lex_11_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.pos 4609)] :=
  (lex_11_65_gate s).prop _ (List.Mem.head _)

theorem lex_11_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.neg 65), (Sat.Literal.pos 40)] :=
  (lex_11_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.pos 65), (Sat.Literal.neg 40)] :=
  (lex_11_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.neg 65), (Sat.Literal.neg 40), (Sat.Literal.pos 4610)] :=
  (lex_11_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4609), (Sat.Literal.pos 65), (Sat.Literal.pos 40), (Sat.Literal.pos 4610)] :=
  (lex_11_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4610) = lexBefore s permutation11 64 := by
  exact (positive_lex_of_descriptor s 4610 permutation11 65 (by rfl)).trans ((lex_skipped s permutation11 64 65 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation11 64) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation11 64 by rw [image11_eq]; rfl))

theorem lex_11_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4611) (Sat.Literal.pos 4610) (Sat.Literal.pos 64) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation11 64 (assignment s)
    (Sat.Literal.pos 4611) (Sat.Literal.pos 4610) (Sat.Literal.pos 64) (Sat.Literal.pos 8) (positive_of_descriptor s 4611 (.lex permutation11 64) (by rfl)) (lex_11_64_prefix s) (positive_select s 64) (lex_11_64_image s)

theorem lex_11_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.pos 64), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation11 64 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4610) (Sat.Literal.pos 64) (Sat.Literal.pos 8) (lex_11_64_prefix s) (positive_select s 64) (lex_11_64_image s)

theorem lex_11_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.pos 4610)] :=
  (lex_11_64_gate s).prop _ (List.Mem.head _)

theorem lex_11_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.neg 64), (Sat.Literal.pos 8)] :=
  (lex_11_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.pos 64), (Sat.Literal.neg 8)] :=
  (lex_11_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.neg 64), (Sat.Literal.neg 8), (Sat.Literal.pos 4611)] :=
  (lex_11_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4610), (Sat.Literal.pos 64), (Sat.Literal.pos 8), (Sat.Literal.pos 4611)] :=
  (lex_11_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_63_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4611) = lexBefore s permutation11 63 := by
  exact (positive_lex_of_descriptor s 4611 permutation11 64 (by rfl)).trans ((lex_skipped s permutation11 63 64 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 64 64 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_63_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation11 63) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation11 63 by rw [image11_eq]; rfl))

theorem lex_11_63_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4612) (Sat.Literal.pos 4611) (Sat.Literal.pos 63) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation11 63 (assignment s)
    (Sat.Literal.pos 4612) (Sat.Literal.pos 4611) (Sat.Literal.pos 63) (Sat.Literal.pos 231) (positive_of_descriptor s 4612 (.lex permutation11 63) (by rfl)) (lex_11_63_prefix s) (positive_select s 63) (lex_11_63_image s)

theorem lex_11_63_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.pos 63), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation11 63 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4611) (Sat.Literal.pos 63) (Sat.Literal.pos 231) (lex_11_63_prefix s) (positive_select s 63) (lex_11_63_image s)

theorem lex_11_63_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.pos 4611)] :=
  (lex_11_63_gate s).prop _ (List.Mem.head _)

theorem lex_11_63_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.neg 63), (Sat.Literal.pos 231)] :=
  (lex_11_63_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_63_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.pos 63), (Sat.Literal.neg 231)] :=
  (lex_11_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_63_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.neg 63), (Sat.Literal.neg 231), (Sat.Literal.pos 4612)] :=
  (lex_11_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_63_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4611), (Sat.Literal.pos 63), (Sat.Literal.pos 231), (Sat.Literal.pos 4612)] :=
  (lex_11_63_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4612) = lexBefore s permutation11 62 := by
  exact (positive_lex_of_descriptor s 4612 permutation11 63 (by rfl)).trans ((lex_skipped s permutation11 62 63 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 63 63 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation11 62) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation11 62 by rw [image11_eq]; rfl))

theorem lex_11_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4613) (Sat.Literal.pos 4612) (Sat.Literal.pos 62) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation11 62 (assignment s)
    (Sat.Literal.pos 4613) (Sat.Literal.pos 4612) (Sat.Literal.pos 62) (Sat.Literal.pos 199) (positive_of_descriptor s 4613 (.lex permutation11 62) (by rfl)) (lex_11_62_prefix s) (positive_select s 62) (lex_11_62_image s)

theorem lex_11_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.pos 62), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation11 62 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4612) (Sat.Literal.pos 62) (Sat.Literal.pos 199) (lex_11_62_prefix s) (positive_select s 62) (lex_11_62_image s)

theorem lex_11_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.pos 4612)] :=
  (lex_11_62_gate s).prop _ (List.Mem.head _)

theorem lex_11_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.neg 62), (Sat.Literal.pos 199)] :=
  (lex_11_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.pos 62), (Sat.Literal.neg 199)] :=
  (lex_11_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.neg 62), (Sat.Literal.neg 199), (Sat.Literal.pos 4613)] :=
  (lex_11_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4612), (Sat.Literal.pos 62), (Sat.Literal.pos 199), (Sat.Literal.pos 4613)] :=
  (lex_11_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4613) = lexBefore s permutation11 61 := by
  exact (positive_lex_of_descriptor s 4613 permutation11 62 (by rfl)).trans ((lex_skipped s permutation11 61 62 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation11 61) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation11 61 by rw [image11_eq]; rfl))

theorem lex_11_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4614) (Sat.Literal.pos 4613) (Sat.Literal.pos 61) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation11 61 (assignment s)
    (Sat.Literal.pos 4614) (Sat.Literal.pos 4613) (Sat.Literal.pos 61) (Sat.Literal.pos 167) (positive_of_descriptor s 4614 (.lex permutation11 61) (by rfl)) (lex_11_61_prefix s) (positive_select s 61) (lex_11_61_image s)

theorem lex_11_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.pos 61), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation11 61 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4613) (Sat.Literal.pos 61) (Sat.Literal.pos 167) (lex_11_61_prefix s) (positive_select s 61) (lex_11_61_image s)

theorem lex_11_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.pos 4613)] :=
  (lex_11_61_gate s).prop _ (List.Mem.head _)

theorem lex_11_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.neg 61), (Sat.Literal.pos 167)] :=
  (lex_11_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.pos 61), (Sat.Literal.neg 167)] :=
  (lex_11_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.neg 61), (Sat.Literal.neg 167), (Sat.Literal.pos 4614)] :=
  (lex_11_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4613), (Sat.Literal.pos 61), (Sat.Literal.pos 167), (Sat.Literal.pos 4614)] :=
  (lex_11_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_60_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4614) = lexBefore s permutation11 60 := by
  exact (positive_lex_of_descriptor s 4614 permutation11 61 (by rfl)).trans ((lex_skipped s permutation11 60 61 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_60_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation11 60) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation11 60 by rw [image11_eq]; rfl))

theorem lex_11_60_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4615) (Sat.Literal.pos 4614) (Sat.Literal.pos 60) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation11 60 (assignment s)
    (Sat.Literal.pos 4615) (Sat.Literal.pos 4614) (Sat.Literal.pos 60) (Sat.Literal.pos 135) (positive_of_descriptor s 4615 (.lex permutation11 60) (by rfl)) (lex_11_60_prefix s) (positive_select s 60) (lex_11_60_image s)

theorem lex_11_60_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.pos 60), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation11 60 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4614) (Sat.Literal.pos 60) (Sat.Literal.pos 135) (lex_11_60_prefix s) (positive_select s 60) (lex_11_60_image s)

theorem lex_11_60_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.pos 4614)] :=
  (lex_11_60_gate s).prop _ (List.Mem.head _)

theorem lex_11_60_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.neg 60), (Sat.Literal.pos 135)] :=
  (lex_11_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_60_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.pos 60), (Sat.Literal.neg 135)] :=
  (lex_11_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_60_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.neg 60), (Sat.Literal.neg 135), (Sat.Literal.pos 4615)] :=
  (lex_11_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_60_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4614), (Sat.Literal.pos 60), (Sat.Literal.pos 135), (Sat.Literal.pos 4615)] :=
  (lex_11_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4615) = lexBefore s permutation11 59 := by
  exact (positive_lex_of_descriptor s 4615 permutation11 60 (by rfl)).trans ((lex_skipped s permutation11 59 60 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation11 59) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation11 59 by rw [image11_eq]; rfl))

theorem lex_11_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4616) (Sat.Literal.pos 4615) (Sat.Literal.pos 59) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation11 59 (assignment s)
    (Sat.Literal.pos 4616) (Sat.Literal.pos 4615) (Sat.Literal.pos 59) (Sat.Literal.pos 103) (positive_of_descriptor s 4616 (.lex permutation11 59) (by rfl)) (lex_11_59_prefix s) (positive_select s 59) (lex_11_59_image s)

theorem lex_11_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.pos 59), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation11 59 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4615) (Sat.Literal.pos 59) (Sat.Literal.pos 103) (lex_11_59_prefix s) (positive_select s 59) (lex_11_59_image s)

theorem lex_11_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.pos 4615)] :=
  (lex_11_59_gate s).prop _ (List.Mem.head _)

theorem lex_11_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.neg 59), (Sat.Literal.pos 103)] :=
  (lex_11_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.pos 59), (Sat.Literal.neg 103)] :=
  (lex_11_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.neg 59), (Sat.Literal.neg 103), (Sat.Literal.pos 4616)] :=
  (lex_11_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4615), (Sat.Literal.pos 59), (Sat.Literal.pos 103), (Sat.Literal.pos 4616)] :=
  (lex_11_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4616) = lexBefore s permutation11 58 := by
  exact (positive_lex_of_descriptor s 4616 permutation11 59 (by rfl)).trans ((lex_skipped s permutation11 58 59 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation11 58) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation11 58 by rw [image11_eq]; rfl))

theorem lex_11_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4617) (Sat.Literal.pos 4616) (Sat.Literal.pos 58) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation11 58 (assignment s)
    (Sat.Literal.pos 4617) (Sat.Literal.pos 4616) (Sat.Literal.pos 58) (Sat.Literal.pos 71) (positive_of_descriptor s 4617 (.lex permutation11 58) (by rfl)) (lex_11_58_prefix s) (positive_select s 58) (lex_11_58_image s)

theorem lex_11_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.pos 58), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation11 58 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4616) (Sat.Literal.pos 58) (Sat.Literal.pos 71) (lex_11_58_prefix s) (positive_select s 58) (lex_11_58_image s)

theorem lex_11_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.pos 4616)] :=
  (lex_11_58_gate s).prop _ (List.Mem.head _)

theorem lex_11_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.neg 58), (Sat.Literal.pos 71)] :=
  (lex_11_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.pos 58), (Sat.Literal.neg 71)] :=
  (lex_11_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.neg 58), (Sat.Literal.neg 71), (Sat.Literal.pos 4617)] :=
  (lex_11_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4616), (Sat.Literal.pos 58), (Sat.Literal.pos 71), (Sat.Literal.pos 4617)] :=
  (lex_11_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4617) = lexBefore s permutation11 57 := by
  exact (positive_lex_of_descriptor s 4617 permutation11 58 (by rfl)).trans ((lex_skipped s permutation11 57 58 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation11 57) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation11 57 by rw [image11_eq]; rfl))

theorem lex_11_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4618) (Sat.Literal.pos 4617) (Sat.Literal.pos 57) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation11 57 (assignment s)
    (Sat.Literal.pos 4618) (Sat.Literal.pos 4617) (Sat.Literal.pos 57) (Sat.Literal.pos 39) (positive_of_descriptor s 4618 (.lex permutation11 57) (by rfl)) (lex_11_57_prefix s) (positive_select s 57) (lex_11_57_image s)

theorem lex_11_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.pos 57), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation11 57 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4617) (Sat.Literal.pos 57) (Sat.Literal.pos 39) (lex_11_57_prefix s) (positive_select s 57) (lex_11_57_image s)

theorem lex_11_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.pos 4617)] :=
  (lex_11_57_gate s).prop _ (List.Mem.head _)

theorem lex_11_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.neg 57), (Sat.Literal.pos 39)] :=
  (lex_11_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.pos 57), (Sat.Literal.neg 39)] :=
  (lex_11_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.neg 57), (Sat.Literal.neg 39), (Sat.Literal.pos 4618)] :=
  (lex_11_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4617), (Sat.Literal.pos 57), (Sat.Literal.pos 39), (Sat.Literal.pos 4618)] :=
  (lex_11_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4618) = lexBefore s permutation11 56 := by
  exact (positive_lex_of_descriptor s 4618 permutation11 57 (by rfl)).trans ((lex_skipped s permutation11 56 57 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation11 56) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation11 56 by rw [image11_eq]; rfl))

theorem lex_11_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4619) (Sat.Literal.pos 4618) (Sat.Literal.pos 56) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation11 56 (assignment s)
    (Sat.Literal.pos 4619) (Sat.Literal.pos 4618) (Sat.Literal.pos 56) (Sat.Literal.pos 7) (positive_of_descriptor s 4619 (.lex permutation11 56) (by rfl)) (lex_11_56_prefix s) (positive_select s 56) (lex_11_56_image s)

theorem lex_11_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.pos 56), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation11 56 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4618) (Sat.Literal.pos 56) (Sat.Literal.pos 7) (lex_11_56_prefix s) (positive_select s 56) (lex_11_56_image s)

theorem lex_11_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.pos 4618)] :=
  (lex_11_56_gate s).prop _ (List.Mem.head _)

theorem lex_11_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.neg 56), (Sat.Literal.pos 7)] :=
  (lex_11_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.pos 56), (Sat.Literal.neg 7)] :=
  (lex_11_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.neg 56), (Sat.Literal.neg 7), (Sat.Literal.pos 4619)] :=
  (lex_11_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4618), (Sat.Literal.pos 56), (Sat.Literal.pos 7), (Sat.Literal.pos 4619)] :=
  (lex_11_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4619) = lexBefore s permutation11 55 := by
  exact (positive_lex_of_descriptor s 4619 permutation11 56 (by rfl)).trans ((lex_skipped s permutation11 55 56 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation11 55) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation11 55 by rw [image11_eq]; rfl))

theorem lex_11_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4620) (Sat.Literal.pos 4619) (Sat.Literal.pos 55) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation11 55 (assignment s)
    (Sat.Literal.pos 4620) (Sat.Literal.pos 4619) (Sat.Literal.pos 55) (Sat.Literal.pos 230) (positive_of_descriptor s 4620 (.lex permutation11 55) (by rfl)) (lex_11_55_prefix s) (positive_select s 55) (lex_11_55_image s)

theorem lex_11_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.pos 55), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation11 55 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4619) (Sat.Literal.pos 55) (Sat.Literal.pos 230) (lex_11_55_prefix s) (positive_select s 55) (lex_11_55_image s)

theorem lex_11_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.pos 4619)] :=
  (lex_11_55_gate s).prop _ (List.Mem.head _)

theorem lex_11_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.neg 55), (Sat.Literal.pos 230)] :=
  (lex_11_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.pos 55), (Sat.Literal.neg 230)] :=
  (lex_11_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.neg 55), (Sat.Literal.neg 230), (Sat.Literal.pos 4620)] :=
  (lex_11_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4619), (Sat.Literal.pos 55), (Sat.Literal.pos 230), (Sat.Literal.pos 4620)] :=
  (lex_11_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4620) = lexBefore s permutation11 54 := by
  exact (positive_lex_of_descriptor s 4620 permutation11 55 (by rfl)).trans ((lex_skipped s permutation11 54 55 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation11 54) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation11 54 by rw [image11_eq]; rfl))

theorem lex_11_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4621) (Sat.Literal.pos 4620) (Sat.Literal.pos 54) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation11 54 (assignment s)
    (Sat.Literal.pos 4621) (Sat.Literal.pos 4620) (Sat.Literal.pos 54) (Sat.Literal.pos 198) (positive_of_descriptor s 4621 (.lex permutation11 54) (by rfl)) (lex_11_54_prefix s) (positive_select s 54) (lex_11_54_image s)

theorem lex_11_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.pos 54), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation11 54 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4620) (Sat.Literal.pos 54) (Sat.Literal.pos 198) (lex_11_54_prefix s) (positive_select s 54) (lex_11_54_image s)

theorem lex_11_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.pos 4620)] :=
  (lex_11_54_gate s).prop _ (List.Mem.head _)

theorem lex_11_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.neg 54), (Sat.Literal.pos 198)] :=
  (lex_11_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.pos 54), (Sat.Literal.neg 198)] :=
  (lex_11_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.neg 54), (Sat.Literal.neg 198), (Sat.Literal.pos 4621)] :=
  (lex_11_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4620), (Sat.Literal.pos 54), (Sat.Literal.pos 198), (Sat.Literal.pos 4621)] :=
  (lex_11_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4621) = lexBefore s permutation11 53 := by
  exact (positive_lex_of_descriptor s 4621 permutation11 54 (by rfl)).trans ((lex_skipped s permutation11 53 54 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation11 53) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation11 53 by rw [image11_eq]; rfl))

theorem lex_11_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4622) (Sat.Literal.pos 4621) (Sat.Literal.pos 53) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation11 53 (assignment s)
    (Sat.Literal.pos 4622) (Sat.Literal.pos 4621) (Sat.Literal.pos 53) (Sat.Literal.pos 166) (positive_of_descriptor s 4622 (.lex permutation11 53) (by rfl)) (lex_11_53_prefix s) (positive_select s 53) (lex_11_53_image s)

theorem lex_11_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.pos 53), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation11 53 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4621) (Sat.Literal.pos 53) (Sat.Literal.pos 166) (lex_11_53_prefix s) (positive_select s 53) (lex_11_53_image s)

theorem lex_11_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.pos 4621)] :=
  (lex_11_53_gate s).prop _ (List.Mem.head _)

theorem lex_11_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.neg 53), (Sat.Literal.pos 166)] :=
  (lex_11_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.pos 53), (Sat.Literal.neg 166)] :=
  (lex_11_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.neg 53), (Sat.Literal.neg 166), (Sat.Literal.pos 4622)] :=
  (lex_11_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4621), (Sat.Literal.pos 53), (Sat.Literal.pos 166), (Sat.Literal.pos 4622)] :=
  (lex_11_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4622) = lexBefore s permutation11 52 := by
  exact (positive_lex_of_descriptor s 4622 permutation11 53 (by rfl)).trans ((lex_skipped s permutation11 52 53 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation11 52) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation11 52 by rw [image11_eq]; rfl))

theorem lex_11_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4623) (Sat.Literal.pos 4622) (Sat.Literal.pos 52) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation11 52 (assignment s)
    (Sat.Literal.pos 4623) (Sat.Literal.pos 4622) (Sat.Literal.pos 52) (Sat.Literal.pos 134) (positive_of_descriptor s 4623 (.lex permutation11 52) (by rfl)) (lex_11_52_prefix s) (positive_select s 52) (lex_11_52_image s)

theorem lex_11_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.pos 52), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation11 52 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4622) (Sat.Literal.pos 52) (Sat.Literal.pos 134) (lex_11_52_prefix s) (positive_select s 52) (lex_11_52_image s)

theorem lex_11_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.pos 4622)] :=
  (lex_11_52_gate s).prop _ (List.Mem.head _)

theorem lex_11_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.neg 52), (Sat.Literal.pos 134)] :=
  (lex_11_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.pos 52), (Sat.Literal.neg 134)] :=
  (lex_11_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.neg 52), (Sat.Literal.neg 134), (Sat.Literal.pos 4623)] :=
  (lex_11_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4622), (Sat.Literal.pos 52), (Sat.Literal.pos 134), (Sat.Literal.pos 4623)] :=
  (lex_11_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4623) = lexBefore s permutation11 51 := by
  exact (positive_lex_of_descriptor s 4623 permutation11 52 (by rfl)).trans ((lex_skipped s permutation11 51 52 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation11 51) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation11 51 by rw [image11_eq]; rfl))

theorem lex_11_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4624) (Sat.Literal.pos 4623) (Sat.Literal.pos 51) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation11 51 (assignment s)
    (Sat.Literal.pos 4624) (Sat.Literal.pos 4623) (Sat.Literal.pos 51) (Sat.Literal.pos 102) (positive_of_descriptor s 4624 (.lex permutation11 51) (by rfl)) (lex_11_51_prefix s) (positive_select s 51) (lex_11_51_image s)

theorem lex_11_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.pos 51), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation11 51 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4623) (Sat.Literal.pos 51) (Sat.Literal.pos 102) (lex_11_51_prefix s) (positive_select s 51) (lex_11_51_image s)

theorem lex_11_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.pos 4623)] :=
  (lex_11_51_gate s).prop _ (List.Mem.head _)

theorem lex_11_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.neg 51), (Sat.Literal.pos 102)] :=
  (lex_11_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.pos 51), (Sat.Literal.neg 102)] :=
  (lex_11_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.neg 51), (Sat.Literal.neg 102), (Sat.Literal.pos 4624)] :=
  (lex_11_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4623), (Sat.Literal.pos 51), (Sat.Literal.pos 102), (Sat.Literal.pos 4624)] :=
  (lex_11_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_11_150_gate

end Crown.CertificateData
