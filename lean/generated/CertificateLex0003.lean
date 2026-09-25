import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_2_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2824) = lexBefore s permutation2 167 := by
  exact (positive_lex_of_descriptor s 2824 permutation2 168 (by rfl)).trans ((lex_skipped s permutation2 167 168 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation2 167) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation2 167 by rw [image2_eq]; rfl))

theorem lex_2_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2825) (Sat.Literal.pos 2824) (Sat.Literal.pos 167) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation2 167 (assignment s)
    (Sat.Literal.pos 2825) (Sat.Literal.pos 2824) (Sat.Literal.pos 167) (Sat.Literal.pos 171) (positive_of_descriptor s 2825 (.lex permutation2 167) (by rfl)) (lex_2_167_prefix s) (positive_select s 167) (lex_2_167_image s)

theorem lex_2_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.pos 167), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation2 167 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2824) (Sat.Literal.pos 167) (Sat.Literal.pos 171) (lex_2_167_prefix s) (positive_select s 167) (lex_2_167_image s)

theorem lex_2_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.pos 2824)] :=
  (lex_2_167_gate s).prop _ (List.Mem.head _)

theorem lex_2_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.neg 167), (Sat.Literal.pos 171)] :=
  (lex_2_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.pos 167), (Sat.Literal.neg 171)] :=
  (lex_2_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.neg 167), (Sat.Literal.neg 171), (Sat.Literal.pos 2825)] :=
  (lex_2_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2824), (Sat.Literal.pos 167), (Sat.Literal.pos 171), (Sat.Literal.pos 2825)] :=
  (lex_2_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2825) = lexBefore s permutation2 166 := by
  exact (positive_lex_of_descriptor s 2825 permutation2 167 (by rfl)).trans ((lex_skipped s permutation2 166 167 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation2 166) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation2 166 by rw [image2_eq]; rfl))

theorem lex_2_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2826) (Sat.Literal.pos 2825) (Sat.Literal.pos 166) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation2 166 (assignment s)
    (Sat.Literal.pos 2826) (Sat.Literal.pos 2825) (Sat.Literal.pos 166) (Sat.Literal.pos 170) (positive_of_descriptor s 2826 (.lex permutation2 166) (by rfl)) (lex_2_166_prefix s) (positive_select s 166) (lex_2_166_image s)

theorem lex_2_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.pos 166), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation2 166 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2825) (Sat.Literal.pos 166) (Sat.Literal.pos 170) (lex_2_166_prefix s) (positive_select s 166) (lex_2_166_image s)

theorem lex_2_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.pos 2825)] :=
  (lex_2_166_gate s).prop _ (List.Mem.head _)

theorem lex_2_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.neg 166), (Sat.Literal.pos 170)] :=
  (lex_2_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.pos 166), (Sat.Literal.neg 170)] :=
  (lex_2_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.neg 166), (Sat.Literal.neg 170), (Sat.Literal.pos 2826)] :=
  (lex_2_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2825), (Sat.Literal.pos 166), (Sat.Literal.pos 170), (Sat.Literal.pos 2826)] :=
  (lex_2_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2826) = lexBefore s permutation2 165 := by
  exact (positive_lex_of_descriptor s 2826 permutation2 166 (by rfl)).trans ((lex_skipped s permutation2 165 166 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation2 165) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation2 165 by rw [image2_eq]; rfl))

theorem lex_2_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2827) (Sat.Literal.pos 2826) (Sat.Literal.pos 165) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation2 165 (assignment s)
    (Sat.Literal.pos 2827) (Sat.Literal.pos 2826) (Sat.Literal.pos 165) (Sat.Literal.pos 169) (positive_of_descriptor s 2827 (.lex permutation2 165) (by rfl)) (lex_2_165_prefix s) (positive_select s 165) (lex_2_165_image s)

theorem lex_2_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.pos 165), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation2 165 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2826) (Sat.Literal.pos 165) (Sat.Literal.pos 169) (lex_2_165_prefix s) (positive_select s 165) (lex_2_165_image s)

theorem lex_2_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.pos 2826)] :=
  (lex_2_165_gate s).prop _ (List.Mem.head _)

theorem lex_2_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.neg 165), (Sat.Literal.pos 169)] :=
  (lex_2_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.pos 165), (Sat.Literal.neg 169)] :=
  (lex_2_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.neg 165), (Sat.Literal.neg 169), (Sat.Literal.pos 2827)] :=
  (lex_2_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2826), (Sat.Literal.pos 165), (Sat.Literal.pos 169), (Sat.Literal.pos 2827)] :=
  (lex_2_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2827) = lexBefore s permutation2 164 := by
  exact (positive_lex_of_descriptor s 2827 permutation2 165 (by rfl)).trans ((lex_skipped s permutation2 164 165 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation2 164) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation2 164 by rw [image2_eq]; rfl))

theorem lex_2_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2828) (Sat.Literal.pos 2827) (Sat.Literal.pos 164) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation2 164 (assignment s)
    (Sat.Literal.pos 2828) (Sat.Literal.pos 2827) (Sat.Literal.pos 164) (Sat.Literal.pos 168) (positive_of_descriptor s 2828 (.lex permutation2 164) (by rfl)) (lex_2_164_prefix s) (positive_select s 164) (lex_2_164_image s)

theorem lex_2_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.pos 164), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation2 164 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2827) (Sat.Literal.pos 164) (Sat.Literal.pos 168) (lex_2_164_prefix s) (positive_select s 164) (lex_2_164_image s)

theorem lex_2_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.pos 2827)] :=
  (lex_2_164_gate s).prop _ (List.Mem.head _)

theorem lex_2_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.neg 164), (Sat.Literal.pos 168)] :=
  (lex_2_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.pos 164), (Sat.Literal.neg 168)] :=
  (lex_2_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.neg 164), (Sat.Literal.neg 168), (Sat.Literal.pos 2828)] :=
  (lex_2_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2827), (Sat.Literal.pos 164), (Sat.Literal.pos 168), (Sat.Literal.pos 2828)] :=
  (lex_2_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2828) = lexBefore s permutation2 155 := by
  exact (positive_lex_of_descriptor s 2828 permutation2 164 (by rfl)).trans ((lex_skipped s permutation2 155 164 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 156 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation2 155) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation2 155 by rw [image2_eq]; rfl))

theorem lex_2_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2829) (Sat.Literal.pos 2828) (Sat.Literal.pos 155) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation2 155 (assignment s)
    (Sat.Literal.pos 2829) (Sat.Literal.pos 2828) (Sat.Literal.pos 155) (Sat.Literal.pos 151) (positive_of_descriptor s 2829 (.lex permutation2 155) (by rfl)) (lex_2_155_prefix s) (positive_select s 155) (lex_2_155_image s)

theorem lex_2_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.pos 155), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation2 155 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2828) (Sat.Literal.pos 155) (Sat.Literal.pos 151) (lex_2_155_prefix s) (positive_select s 155) (lex_2_155_image s)

theorem lex_2_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.pos 2828)] :=
  (lex_2_155_gate s).prop _ (List.Mem.head _)

theorem lex_2_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.neg 155), (Sat.Literal.pos 151)] :=
  (lex_2_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.pos 155), (Sat.Literal.neg 151)] :=
  (lex_2_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.neg 155), (Sat.Literal.neg 151), (Sat.Literal.pos 2829)] :=
  (lex_2_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2828), (Sat.Literal.pos 155), (Sat.Literal.pos 151), (Sat.Literal.pos 2829)] :=
  (lex_2_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2829) = lexBefore s permutation2 154 := by
  exact (positive_lex_of_descriptor s 2829 permutation2 155 (by rfl)).trans ((lex_skipped s permutation2 154 155 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation2 154) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation2 154 by rw [image2_eq]; rfl))

theorem lex_2_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2830) (Sat.Literal.pos 2829) (Sat.Literal.pos 154) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation2 154 (assignment s)
    (Sat.Literal.pos 2830) (Sat.Literal.pos 2829) (Sat.Literal.pos 154) (Sat.Literal.pos 150) (positive_of_descriptor s 2830 (.lex permutation2 154) (by rfl)) (lex_2_154_prefix s) (positive_select s 154) (lex_2_154_image s)

theorem lex_2_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.pos 154), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation2 154 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2829) (Sat.Literal.pos 154) (Sat.Literal.pos 150) (lex_2_154_prefix s) (positive_select s 154) (lex_2_154_image s)

theorem lex_2_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.pos 2829)] :=
  (lex_2_154_gate s).prop _ (List.Mem.head _)

theorem lex_2_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.neg 154), (Sat.Literal.pos 150)] :=
  (lex_2_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.pos 154), (Sat.Literal.neg 150)] :=
  (lex_2_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.neg 154), (Sat.Literal.neg 150), (Sat.Literal.pos 2830)] :=
  (lex_2_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2829), (Sat.Literal.pos 154), (Sat.Literal.pos 150), (Sat.Literal.pos 2830)] :=
  (lex_2_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2830) = lexBefore s permutation2 153 := by
  exact (positive_lex_of_descriptor s 2830 permutation2 154 (by rfl)).trans ((lex_skipped s permutation2 153 154 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation2 153) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation2 153 by rw [image2_eq]; rfl))

theorem lex_2_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2831) (Sat.Literal.pos 2830) (Sat.Literal.pos 153) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation2 153 (assignment s)
    (Sat.Literal.pos 2831) (Sat.Literal.pos 2830) (Sat.Literal.pos 153) (Sat.Literal.pos 149) (positive_of_descriptor s 2831 (.lex permutation2 153) (by rfl)) (lex_2_153_prefix s) (positive_select s 153) (lex_2_153_image s)

theorem lex_2_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.pos 153), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation2 153 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2830) (Sat.Literal.pos 153) (Sat.Literal.pos 149) (lex_2_153_prefix s) (positive_select s 153) (lex_2_153_image s)

theorem lex_2_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.pos 2830)] :=
  (lex_2_153_gate s).prop _ (List.Mem.head _)

theorem lex_2_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.neg 153), (Sat.Literal.pos 149)] :=
  (lex_2_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.pos 153), (Sat.Literal.neg 149)] :=
  (lex_2_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.neg 153), (Sat.Literal.neg 149), (Sat.Literal.pos 2831)] :=
  (lex_2_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2830), (Sat.Literal.pos 153), (Sat.Literal.pos 149), (Sat.Literal.pos 2831)] :=
  (lex_2_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2831) = lexBefore s permutation2 152 := by
  exact (positive_lex_of_descriptor s 2831 permutation2 153 (by rfl)).trans ((lex_skipped s permutation2 152 153 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation2 152) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation2 152 by rw [image2_eq]; rfl))

theorem lex_2_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2832) (Sat.Literal.pos 2831) (Sat.Literal.pos 152) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation2 152 (assignment s)
    (Sat.Literal.pos 2832) (Sat.Literal.pos 2831) (Sat.Literal.pos 152) (Sat.Literal.pos 148) (positive_of_descriptor s 2832 (.lex permutation2 152) (by rfl)) (lex_2_152_prefix s) (positive_select s 152) (lex_2_152_image s)

theorem lex_2_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.pos 152), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation2 152 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2831) (Sat.Literal.pos 152) (Sat.Literal.pos 148) (lex_2_152_prefix s) (positive_select s 152) (lex_2_152_image s)

theorem lex_2_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.pos 2831)] :=
  (lex_2_152_gate s).prop _ (List.Mem.head _)

theorem lex_2_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.neg 152), (Sat.Literal.pos 148)] :=
  (lex_2_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.pos 152), (Sat.Literal.neg 148)] :=
  (lex_2_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.neg 152), (Sat.Literal.neg 148), (Sat.Literal.pos 2832)] :=
  (lex_2_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2831), (Sat.Literal.pos 152), (Sat.Literal.pos 148), (Sat.Literal.pos 2832)] :=
  (lex_2_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2832) = lexBefore s permutation2 151 := by
  exact (positive_lex_of_descriptor s 2832 permutation2 152 (by rfl)).trans ((lex_skipped s permutation2 151 152 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation2 151) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation2 151 by rw [image2_eq]; rfl))

theorem lex_2_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2833) (Sat.Literal.pos 2832) (Sat.Literal.pos 151) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation2 151 (assignment s)
    (Sat.Literal.pos 2833) (Sat.Literal.pos 2832) (Sat.Literal.pos 151) (Sat.Literal.pos 155) (positive_of_descriptor s 2833 (.lex permutation2 151) (by rfl)) (lex_2_151_prefix s) (positive_select s 151) (lex_2_151_image s)

theorem lex_2_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.pos 151), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation2 151 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2832) (Sat.Literal.pos 151) (Sat.Literal.pos 155) (lex_2_151_prefix s) (positive_select s 151) (lex_2_151_image s)

theorem lex_2_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.pos 2832)] :=
  (lex_2_151_gate s).prop _ (List.Mem.head _)

theorem lex_2_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.neg 151), (Sat.Literal.pos 155)] :=
  (lex_2_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.pos 151), (Sat.Literal.neg 155)] :=
  (lex_2_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.neg 151), (Sat.Literal.neg 155), (Sat.Literal.pos 2833)] :=
  (lex_2_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2832), (Sat.Literal.pos 151), (Sat.Literal.pos 155), (Sat.Literal.pos 2833)] :=
  (lex_2_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2833) = lexBefore s permutation2 150 := by
  exact (positive_lex_of_descriptor s 2833 permutation2 151 (by rfl)).trans ((lex_skipped s permutation2 150 151 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation2 150) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation2 150 by rw [image2_eq]; rfl))

theorem lex_2_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2834) (Sat.Literal.pos 2833) (Sat.Literal.pos 150) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation2 150 (assignment s)
    (Sat.Literal.pos 2834) (Sat.Literal.pos 2833) (Sat.Literal.pos 150) (Sat.Literal.pos 154) (positive_of_descriptor s 2834 (.lex permutation2 150) (by rfl)) (lex_2_150_prefix s) (positive_select s 150) (lex_2_150_image s)

theorem lex_2_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.pos 150), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation2 150 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2833) (Sat.Literal.pos 150) (Sat.Literal.pos 154) (lex_2_150_prefix s) (positive_select s 150) (lex_2_150_image s)

theorem lex_2_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.pos 2833)] :=
  (lex_2_150_gate s).prop _ (List.Mem.head _)

theorem lex_2_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.neg 150), (Sat.Literal.pos 154)] :=
  (lex_2_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.pos 150), (Sat.Literal.neg 154)] :=
  (lex_2_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.neg 150), (Sat.Literal.neg 154), (Sat.Literal.pos 2834)] :=
  (lex_2_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2833), (Sat.Literal.pos 150), (Sat.Literal.pos 154), (Sat.Literal.pos 2834)] :=
  (lex_2_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2834) = lexBefore s permutation2 149 := by
  exact (positive_lex_of_descriptor s 2834 permutation2 150 (by rfl)).trans ((lex_skipped s permutation2 149 150 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation2 149) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation2 149 by rw [image2_eq]; rfl))

theorem lex_2_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2835) (Sat.Literal.pos 2834) (Sat.Literal.pos 149) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation2 149 (assignment s)
    (Sat.Literal.pos 2835) (Sat.Literal.pos 2834) (Sat.Literal.pos 149) (Sat.Literal.pos 153) (positive_of_descriptor s 2835 (.lex permutation2 149) (by rfl)) (lex_2_149_prefix s) (positive_select s 149) (lex_2_149_image s)

theorem lex_2_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.pos 149), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation2 149 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2834) (Sat.Literal.pos 149) (Sat.Literal.pos 153) (lex_2_149_prefix s) (positive_select s 149) (lex_2_149_image s)

theorem lex_2_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.pos 2834)] :=
  (lex_2_149_gate s).prop _ (List.Mem.head _)

theorem lex_2_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.neg 149), (Sat.Literal.pos 153)] :=
  (lex_2_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.pos 149), (Sat.Literal.neg 153)] :=
  (lex_2_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.neg 149), (Sat.Literal.neg 153), (Sat.Literal.pos 2835)] :=
  (lex_2_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2834), (Sat.Literal.pos 149), (Sat.Literal.pos 153), (Sat.Literal.pos 2835)] :=
  (lex_2_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2835) = lexBefore s permutation2 148 := by
  exact (positive_lex_of_descriptor s 2835 permutation2 149 (by rfl)).trans ((lex_skipped s permutation2 148 149 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation2 148) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation2 148 by rw [image2_eq]; rfl))

theorem lex_2_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2836) (Sat.Literal.pos 2835) (Sat.Literal.pos 148) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation2 148 (assignment s)
    (Sat.Literal.pos 2836) (Sat.Literal.pos 2835) (Sat.Literal.pos 148) (Sat.Literal.pos 152) (positive_of_descriptor s 2836 (.lex permutation2 148) (by rfl)) (lex_2_148_prefix s) (positive_select s 148) (lex_2_148_image s)

theorem lex_2_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.pos 148), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation2 148 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2835) (Sat.Literal.pos 148) (Sat.Literal.pos 152) (lex_2_148_prefix s) (positive_select s 148) (lex_2_148_image s)

theorem lex_2_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.pos 2835)] :=
  (lex_2_148_gate s).prop _ (List.Mem.head _)

theorem lex_2_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.neg 148), (Sat.Literal.pos 152)] :=
  (lex_2_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.pos 148), (Sat.Literal.neg 152)] :=
  (lex_2_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.neg 148), (Sat.Literal.neg 152), (Sat.Literal.pos 2836)] :=
  (lex_2_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2835), (Sat.Literal.pos 148), (Sat.Literal.pos 152), (Sat.Literal.pos 2836)] :=
  (lex_2_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2836) = lexBefore s permutation2 139 := by
  exact (positive_lex_of_descriptor s 2836 permutation2 148 (by rfl)).trans ((lex_skipped s permutation2 139 148 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 140 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation2 139) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation2 139 by rw [image2_eq]; rfl))

theorem lex_2_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2837) (Sat.Literal.pos 2836) (Sat.Literal.pos 139) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation2 139 (assignment s)
    (Sat.Literal.pos 2837) (Sat.Literal.pos 2836) (Sat.Literal.pos 139) (Sat.Literal.pos 135) (positive_of_descriptor s 2837 (.lex permutation2 139) (by rfl)) (lex_2_139_prefix s) (positive_select s 139) (lex_2_139_image s)

theorem lex_2_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.pos 139), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation2 139 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2836) (Sat.Literal.pos 139) (Sat.Literal.pos 135) (lex_2_139_prefix s) (positive_select s 139) (lex_2_139_image s)

theorem lex_2_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.pos 2836)] :=
  (lex_2_139_gate s).prop _ (List.Mem.head _)

theorem lex_2_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.neg 139), (Sat.Literal.pos 135)] :=
  (lex_2_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.pos 139), (Sat.Literal.neg 135)] :=
  (lex_2_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.neg 139), (Sat.Literal.neg 135), (Sat.Literal.pos 2837)] :=
  (lex_2_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2836), (Sat.Literal.pos 139), (Sat.Literal.pos 135), (Sat.Literal.pos 2837)] :=
  (lex_2_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2837) = lexBefore s permutation2 138 := by
  exact (positive_lex_of_descriptor s 2837 permutation2 139 (by rfl)).trans ((lex_skipped s permutation2 138 139 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation2 138) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation2 138 by rw [image2_eq]; rfl))

theorem lex_2_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2838) (Sat.Literal.pos 2837) (Sat.Literal.pos 138) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation2 138 (assignment s)
    (Sat.Literal.pos 2838) (Sat.Literal.pos 2837) (Sat.Literal.pos 138) (Sat.Literal.pos 134) (positive_of_descriptor s 2838 (.lex permutation2 138) (by rfl)) (lex_2_138_prefix s) (positive_select s 138) (lex_2_138_image s)

theorem lex_2_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.pos 138), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation2 138 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2837) (Sat.Literal.pos 138) (Sat.Literal.pos 134) (lex_2_138_prefix s) (positive_select s 138) (lex_2_138_image s)

theorem lex_2_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.pos 2837)] :=
  (lex_2_138_gate s).prop _ (List.Mem.head _)

theorem lex_2_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.neg 138), (Sat.Literal.pos 134)] :=
  (lex_2_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.pos 138), (Sat.Literal.neg 134)] :=
  (lex_2_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.neg 138), (Sat.Literal.neg 134), (Sat.Literal.pos 2838)] :=
  (lex_2_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2837), (Sat.Literal.pos 138), (Sat.Literal.pos 134), (Sat.Literal.pos 2838)] :=
  (lex_2_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2838) = lexBefore s permutation2 137 := by
  exact (positive_lex_of_descriptor s 2838 permutation2 138 (by rfl)).trans ((lex_skipped s permutation2 137 138 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation2 137) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation2 137 by rw [image2_eq]; rfl))

theorem lex_2_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2839) (Sat.Literal.pos 2838) (Sat.Literal.pos 137) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation2 137 (assignment s)
    (Sat.Literal.pos 2839) (Sat.Literal.pos 2838) (Sat.Literal.pos 137) (Sat.Literal.pos 133) (positive_of_descriptor s 2839 (.lex permutation2 137) (by rfl)) (lex_2_137_prefix s) (positive_select s 137) (lex_2_137_image s)

theorem lex_2_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.pos 137), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation2 137 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2838) (Sat.Literal.pos 137) (Sat.Literal.pos 133) (lex_2_137_prefix s) (positive_select s 137) (lex_2_137_image s)

theorem lex_2_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.pos 2838)] :=
  (lex_2_137_gate s).prop _ (List.Mem.head _)

theorem lex_2_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.neg 137), (Sat.Literal.pos 133)] :=
  (lex_2_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.pos 137), (Sat.Literal.neg 133)] :=
  (lex_2_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.neg 137), (Sat.Literal.neg 133), (Sat.Literal.pos 2839)] :=
  (lex_2_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2838), (Sat.Literal.pos 137), (Sat.Literal.pos 133), (Sat.Literal.pos 2839)] :=
  (lex_2_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2839) = lexBefore s permutation2 136 := by
  exact (positive_lex_of_descriptor s 2839 permutation2 137 (by rfl)).trans ((lex_skipped s permutation2 136 137 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation2 136) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation2 136 by rw [image2_eq]; rfl))

theorem lex_2_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2840) (Sat.Literal.pos 2839) (Sat.Literal.pos 136) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation2 136 (assignment s)
    (Sat.Literal.pos 2840) (Sat.Literal.pos 2839) (Sat.Literal.pos 136) (Sat.Literal.pos 132) (positive_of_descriptor s 2840 (.lex permutation2 136) (by rfl)) (lex_2_136_prefix s) (positive_select s 136) (lex_2_136_image s)

theorem lex_2_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.pos 136), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation2 136 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2839) (Sat.Literal.pos 136) (Sat.Literal.pos 132) (lex_2_136_prefix s) (positive_select s 136) (lex_2_136_image s)

theorem lex_2_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.pos 2839)] :=
  (lex_2_136_gate s).prop _ (List.Mem.head _)

theorem lex_2_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.neg 136), (Sat.Literal.pos 132)] :=
  (lex_2_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.pos 136), (Sat.Literal.neg 132)] :=
  (lex_2_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.neg 136), (Sat.Literal.neg 132), (Sat.Literal.pos 2840)] :=
  (lex_2_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2839), (Sat.Literal.pos 136), (Sat.Literal.pos 132), (Sat.Literal.pos 2840)] :=
  (lex_2_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2840) = lexBefore s permutation2 135 := by
  exact (positive_lex_of_descriptor s 2840 permutation2 136 (by rfl)).trans ((lex_skipped s permutation2 135 136 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation2 135) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation2 135 by rw [image2_eq]; rfl))

theorem lex_2_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2841) (Sat.Literal.pos 2840) (Sat.Literal.pos 135) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation2 135 (assignment s)
    (Sat.Literal.pos 2841) (Sat.Literal.pos 2840) (Sat.Literal.pos 135) (Sat.Literal.pos 139) (positive_of_descriptor s 2841 (.lex permutation2 135) (by rfl)) (lex_2_135_prefix s) (positive_select s 135) (lex_2_135_image s)

theorem lex_2_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.pos 135), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation2 135 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2840) (Sat.Literal.pos 135) (Sat.Literal.pos 139) (lex_2_135_prefix s) (positive_select s 135) (lex_2_135_image s)

theorem lex_2_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.pos 2840)] :=
  (lex_2_135_gate s).prop _ (List.Mem.head _)

theorem lex_2_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.neg 135), (Sat.Literal.pos 139)] :=
  (lex_2_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.pos 135), (Sat.Literal.neg 139)] :=
  (lex_2_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.neg 135), (Sat.Literal.neg 139), (Sat.Literal.pos 2841)] :=
  (lex_2_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2840), (Sat.Literal.pos 135), (Sat.Literal.pos 139), (Sat.Literal.pos 2841)] :=
  (lex_2_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2841) = lexBefore s permutation2 134 := by
  exact (positive_lex_of_descriptor s 2841 permutation2 135 (by rfl)).trans ((lex_skipped s permutation2 134 135 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation2 134) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation2 134 by rw [image2_eq]; rfl))

theorem lex_2_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2842) (Sat.Literal.pos 2841) (Sat.Literal.pos 134) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation2 134 (assignment s)
    (Sat.Literal.pos 2842) (Sat.Literal.pos 2841) (Sat.Literal.pos 134) (Sat.Literal.pos 138) (positive_of_descriptor s 2842 (.lex permutation2 134) (by rfl)) (lex_2_134_prefix s) (positive_select s 134) (lex_2_134_image s)

theorem lex_2_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.pos 134), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation2 134 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2841) (Sat.Literal.pos 134) (Sat.Literal.pos 138) (lex_2_134_prefix s) (positive_select s 134) (lex_2_134_image s)

theorem lex_2_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.pos 2841)] :=
  (lex_2_134_gate s).prop _ (List.Mem.head _)

theorem lex_2_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.neg 134), (Sat.Literal.pos 138)] :=
  (lex_2_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.pos 134), (Sat.Literal.neg 138)] :=
  (lex_2_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.neg 134), (Sat.Literal.neg 138), (Sat.Literal.pos 2842)] :=
  (lex_2_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2841), (Sat.Literal.pos 134), (Sat.Literal.pos 138), (Sat.Literal.pos 2842)] :=
  (lex_2_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2842) = lexBefore s permutation2 133 := by
  exact (positive_lex_of_descriptor s 2842 permutation2 134 (by rfl)).trans ((lex_skipped s permutation2 133 134 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation2 133) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation2 133 by rw [image2_eq]; rfl))

theorem lex_2_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2843) (Sat.Literal.pos 2842) (Sat.Literal.pos 133) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation2 133 (assignment s)
    (Sat.Literal.pos 2843) (Sat.Literal.pos 2842) (Sat.Literal.pos 133) (Sat.Literal.pos 137) (positive_of_descriptor s 2843 (.lex permutation2 133) (by rfl)) (lex_2_133_prefix s) (positive_select s 133) (lex_2_133_image s)

theorem lex_2_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.pos 133), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation2 133 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2842) (Sat.Literal.pos 133) (Sat.Literal.pos 137) (lex_2_133_prefix s) (positive_select s 133) (lex_2_133_image s)

theorem lex_2_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.pos 2842)] :=
  (lex_2_133_gate s).prop _ (List.Mem.head _)

theorem lex_2_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.neg 133), (Sat.Literal.pos 137)] :=
  (lex_2_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.pos 133), (Sat.Literal.neg 137)] :=
  (lex_2_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.neg 133), (Sat.Literal.neg 137), (Sat.Literal.pos 2843)] :=
  (lex_2_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2842), (Sat.Literal.pos 133), (Sat.Literal.pos 137), (Sat.Literal.pos 2843)] :=
  (lex_2_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2843) = lexBefore s permutation2 132 := by
  exact (positive_lex_of_descriptor s 2843 permutation2 133 (by rfl)).trans ((lex_skipped s permutation2 132 133 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation2 132) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation2 132 by rw [image2_eq]; rfl))

theorem lex_2_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2844) (Sat.Literal.pos 2843) (Sat.Literal.pos 132) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation2 132 (assignment s)
    (Sat.Literal.pos 2844) (Sat.Literal.pos 2843) (Sat.Literal.pos 132) (Sat.Literal.pos 136) (positive_of_descriptor s 2844 (.lex permutation2 132) (by rfl)) (lex_2_132_prefix s) (positive_select s 132) (lex_2_132_image s)

theorem lex_2_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.pos 132), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation2 132 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2843) (Sat.Literal.pos 132) (Sat.Literal.pos 136) (lex_2_132_prefix s) (positive_select s 132) (lex_2_132_image s)

theorem lex_2_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.pos 2843)] :=
  (lex_2_132_gate s).prop _ (List.Mem.head _)

theorem lex_2_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.neg 132), (Sat.Literal.pos 136)] :=
  (lex_2_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.pos 132), (Sat.Literal.neg 136)] :=
  (lex_2_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.neg 132), (Sat.Literal.neg 136), (Sat.Literal.pos 2844)] :=
  (lex_2_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2843), (Sat.Literal.pos 132), (Sat.Literal.pos 136), (Sat.Literal.pos 2844)] :=
  (lex_2_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2844) = lexBefore s permutation2 123 := by
  exact (positive_lex_of_descriptor s 2844 permutation2 132 (by rfl)).trans ((lex_skipped s permutation2 123 132 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 124 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation2 123) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation2 123 by rw [image2_eq]; rfl))

theorem lex_2_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2845) (Sat.Literal.pos 2844) (Sat.Literal.pos 123) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation2 123 (assignment s)
    (Sat.Literal.pos 2845) (Sat.Literal.pos 2844) (Sat.Literal.pos 123) (Sat.Literal.pos 119) (positive_of_descriptor s 2845 (.lex permutation2 123) (by rfl)) (lex_2_123_prefix s) (positive_select s 123) (lex_2_123_image s)

theorem lex_2_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.pos 123), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation2 123 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2844) (Sat.Literal.pos 123) (Sat.Literal.pos 119) (lex_2_123_prefix s) (positive_select s 123) (lex_2_123_image s)

theorem lex_2_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.pos 2844)] :=
  (lex_2_123_gate s).prop _ (List.Mem.head _)

theorem lex_2_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.neg 123), (Sat.Literal.pos 119)] :=
  (lex_2_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.pos 123), (Sat.Literal.neg 119)] :=
  (lex_2_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.neg 123), (Sat.Literal.neg 119), (Sat.Literal.pos 2845)] :=
  (lex_2_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2844), (Sat.Literal.pos 123), (Sat.Literal.pos 119), (Sat.Literal.pos 2845)] :=
  (lex_2_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2845) = lexBefore s permutation2 122 := by
  exact (positive_lex_of_descriptor s 2845 permutation2 123 (by rfl)).trans ((lex_skipped s permutation2 122 123 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation2 122) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation2 122 by rw [image2_eq]; rfl))

theorem lex_2_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2846) (Sat.Literal.pos 2845) (Sat.Literal.pos 122) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation2 122 (assignment s)
    (Sat.Literal.pos 2846) (Sat.Literal.pos 2845) (Sat.Literal.pos 122) (Sat.Literal.pos 118) (positive_of_descriptor s 2846 (.lex permutation2 122) (by rfl)) (lex_2_122_prefix s) (positive_select s 122) (lex_2_122_image s)

theorem lex_2_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.pos 122), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation2 122 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2845) (Sat.Literal.pos 122) (Sat.Literal.pos 118) (lex_2_122_prefix s) (positive_select s 122) (lex_2_122_image s)

theorem lex_2_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.pos 2845)] :=
  (lex_2_122_gate s).prop _ (List.Mem.head _)

theorem lex_2_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.neg 122), (Sat.Literal.pos 118)] :=
  (lex_2_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.pos 122), (Sat.Literal.neg 118)] :=
  (lex_2_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.neg 122), (Sat.Literal.neg 118), (Sat.Literal.pos 2846)] :=
  (lex_2_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2845), (Sat.Literal.pos 122), (Sat.Literal.pos 118), (Sat.Literal.pos 2846)] :=
  (lex_2_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2846) = lexBefore s permutation2 121 := by
  exact (positive_lex_of_descriptor s 2846 permutation2 122 (by rfl)).trans ((lex_skipped s permutation2 121 122 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation2 121) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation2 121 by rw [image2_eq]; rfl))

theorem lex_2_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2847) (Sat.Literal.pos 2846) (Sat.Literal.pos 121) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation2 121 (assignment s)
    (Sat.Literal.pos 2847) (Sat.Literal.pos 2846) (Sat.Literal.pos 121) (Sat.Literal.pos 117) (positive_of_descriptor s 2847 (.lex permutation2 121) (by rfl)) (lex_2_121_prefix s) (positive_select s 121) (lex_2_121_image s)

theorem lex_2_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.pos 121), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation2 121 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2846) (Sat.Literal.pos 121) (Sat.Literal.pos 117) (lex_2_121_prefix s) (positive_select s 121) (lex_2_121_image s)

theorem lex_2_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.pos 2846)] :=
  (lex_2_121_gate s).prop _ (List.Mem.head _)

theorem lex_2_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.neg 121), (Sat.Literal.pos 117)] :=
  (lex_2_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.pos 121), (Sat.Literal.neg 117)] :=
  (lex_2_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.neg 121), (Sat.Literal.neg 117), (Sat.Literal.pos 2847)] :=
  (lex_2_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2846), (Sat.Literal.pos 121), (Sat.Literal.pos 117), (Sat.Literal.pos 2847)] :=
  (lex_2_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2847) = lexBefore s permutation2 120 := by
  exact (positive_lex_of_descriptor s 2847 permutation2 121 (by rfl)).trans ((lex_skipped s permutation2 120 121 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation2 120) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation2 120 by rw [image2_eq]; rfl))

theorem lex_2_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2848) (Sat.Literal.pos 2847) (Sat.Literal.pos 120) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation2 120 (assignment s)
    (Sat.Literal.pos 2848) (Sat.Literal.pos 2847) (Sat.Literal.pos 120) (Sat.Literal.pos 116) (positive_of_descriptor s 2848 (.lex permutation2 120) (by rfl)) (lex_2_120_prefix s) (positive_select s 120) (lex_2_120_image s)

theorem lex_2_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.pos 120), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation2 120 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2847) (Sat.Literal.pos 120) (Sat.Literal.pos 116) (lex_2_120_prefix s) (positive_select s 120) (lex_2_120_image s)

theorem lex_2_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.pos 2847)] :=
  (lex_2_120_gate s).prop _ (List.Mem.head _)

theorem lex_2_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.neg 120), (Sat.Literal.pos 116)] :=
  (lex_2_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.pos 120), (Sat.Literal.neg 116)] :=
  (lex_2_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.neg 120), (Sat.Literal.neg 116), (Sat.Literal.pos 2848)] :=
  (lex_2_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2847), (Sat.Literal.pos 120), (Sat.Literal.pos 116), (Sat.Literal.pos 2848)] :=
  (lex_2_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2848) = lexBefore s permutation2 119 := by
  exact (positive_lex_of_descriptor s 2848 permutation2 120 (by rfl)).trans ((lex_skipped s permutation2 119 120 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation2 119) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation2 119 by rw [image2_eq]; rfl))

theorem lex_2_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2849) (Sat.Literal.pos 2848) (Sat.Literal.pos 119) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation2 119 (assignment s)
    (Sat.Literal.pos 2849) (Sat.Literal.pos 2848) (Sat.Literal.pos 119) (Sat.Literal.pos 123) (positive_of_descriptor s 2849 (.lex permutation2 119) (by rfl)) (lex_2_119_prefix s) (positive_select s 119) (lex_2_119_image s)

theorem lex_2_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.pos 119), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation2 119 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2848) (Sat.Literal.pos 119) (Sat.Literal.pos 123) (lex_2_119_prefix s) (positive_select s 119) (lex_2_119_image s)

theorem lex_2_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.pos 2848)] :=
  (lex_2_119_gate s).prop _ (List.Mem.head _)

theorem lex_2_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.neg 119), (Sat.Literal.pos 123)] :=
  (lex_2_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.pos 119), (Sat.Literal.neg 123)] :=
  (lex_2_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.neg 119), (Sat.Literal.neg 123), (Sat.Literal.pos 2849)] :=
  (lex_2_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2848), (Sat.Literal.pos 119), (Sat.Literal.pos 123), (Sat.Literal.pos 2849)] :=
  (lex_2_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2849) = lexBefore s permutation2 118 := by
  exact (positive_lex_of_descriptor s 2849 permutation2 119 (by rfl)).trans ((lex_skipped s permutation2 118 119 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation2 118) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation2 118 by rw [image2_eq]; rfl))

theorem lex_2_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2850) (Sat.Literal.pos 2849) (Sat.Literal.pos 118) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation2 118 (assignment s)
    (Sat.Literal.pos 2850) (Sat.Literal.pos 2849) (Sat.Literal.pos 118) (Sat.Literal.pos 122) (positive_of_descriptor s 2850 (.lex permutation2 118) (by rfl)) (lex_2_118_prefix s) (positive_select s 118) (lex_2_118_image s)

theorem lex_2_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.pos 118), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation2 118 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2849) (Sat.Literal.pos 118) (Sat.Literal.pos 122) (lex_2_118_prefix s) (positive_select s 118) (lex_2_118_image s)

theorem lex_2_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.pos 2849)] :=
  (lex_2_118_gate s).prop _ (List.Mem.head _)

theorem lex_2_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.neg 118), (Sat.Literal.pos 122)] :=
  (lex_2_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.pos 118), (Sat.Literal.neg 122)] :=
  (lex_2_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.neg 118), (Sat.Literal.neg 122), (Sat.Literal.pos 2850)] :=
  (lex_2_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2849), (Sat.Literal.pos 118), (Sat.Literal.pos 122), (Sat.Literal.pos 2850)] :=
  (lex_2_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2850) = lexBefore s permutation2 117 := by
  exact (positive_lex_of_descriptor s 2850 permutation2 118 (by rfl)).trans ((lex_skipped s permutation2 117 118 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation2 117) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation2 117 by rw [image2_eq]; rfl))

theorem lex_2_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2851) (Sat.Literal.pos 2850) (Sat.Literal.pos 117) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation2 117 (assignment s)
    (Sat.Literal.pos 2851) (Sat.Literal.pos 2850) (Sat.Literal.pos 117) (Sat.Literal.pos 121) (positive_of_descriptor s 2851 (.lex permutation2 117) (by rfl)) (lex_2_117_prefix s) (positive_select s 117) (lex_2_117_image s)

theorem lex_2_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.pos 117), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation2 117 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2850) (Sat.Literal.pos 117) (Sat.Literal.pos 121) (lex_2_117_prefix s) (positive_select s 117) (lex_2_117_image s)

theorem lex_2_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.pos 2850)] :=
  (lex_2_117_gate s).prop _ (List.Mem.head _)

theorem lex_2_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.neg 117), (Sat.Literal.pos 121)] :=
  (lex_2_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.pos 117), (Sat.Literal.neg 121)] :=
  (lex_2_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.neg 117), (Sat.Literal.neg 121), (Sat.Literal.pos 2851)] :=
  (lex_2_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2850), (Sat.Literal.pos 117), (Sat.Literal.pos 121), (Sat.Literal.pos 2851)] :=
  (lex_2_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2851) = lexBefore s permutation2 116 := by
  exact (positive_lex_of_descriptor s 2851 permutation2 117 (by rfl)).trans ((lex_skipped s permutation2 116 117 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation2 116) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation2 116 by rw [image2_eq]; rfl))

theorem lex_2_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2852) (Sat.Literal.pos 2851) (Sat.Literal.pos 116) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation2 116 (assignment s)
    (Sat.Literal.pos 2852) (Sat.Literal.pos 2851) (Sat.Literal.pos 116) (Sat.Literal.pos 120) (positive_of_descriptor s 2852 (.lex permutation2 116) (by rfl)) (lex_2_116_prefix s) (positive_select s 116) (lex_2_116_image s)

theorem lex_2_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.pos 116), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation2 116 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2851) (Sat.Literal.pos 116) (Sat.Literal.pos 120) (lex_2_116_prefix s) (positive_select s 116) (lex_2_116_image s)

theorem lex_2_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.pos 2851)] :=
  (lex_2_116_gate s).prop _ (List.Mem.head _)

theorem lex_2_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.neg 116), (Sat.Literal.pos 120)] :=
  (lex_2_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.pos 116), (Sat.Literal.neg 120)] :=
  (lex_2_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.neg 116), (Sat.Literal.neg 120), (Sat.Literal.pos 2852)] :=
  (lex_2_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2851), (Sat.Literal.pos 116), (Sat.Literal.pos 120), (Sat.Literal.pos 2852)] :=
  (lex_2_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2852) = lexBefore s permutation2 107 := by
  exact (positive_lex_of_descriptor s 2852 permutation2 116 (by rfl)).trans ((lex_skipped s permutation2 107 116 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 108 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation2 107) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation2 107 by rw [image2_eq]; rfl))

theorem lex_2_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2853) (Sat.Literal.pos 2852) (Sat.Literal.pos 107) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation2 107 (assignment s)
    (Sat.Literal.pos 2853) (Sat.Literal.pos 2852) (Sat.Literal.pos 107) (Sat.Literal.pos 103) (positive_of_descriptor s 2853 (.lex permutation2 107) (by rfl)) (lex_2_107_prefix s) (positive_select s 107) (lex_2_107_image s)

theorem lex_2_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.pos 107), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation2 107 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2852) (Sat.Literal.pos 107) (Sat.Literal.pos 103) (lex_2_107_prefix s) (positive_select s 107) (lex_2_107_image s)

theorem lex_2_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.pos 2852)] :=
  (lex_2_107_gate s).prop _ (List.Mem.head _)

theorem lex_2_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.neg 107), (Sat.Literal.pos 103)] :=
  (lex_2_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.pos 107), (Sat.Literal.neg 103)] :=
  (lex_2_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.neg 107), (Sat.Literal.neg 103), (Sat.Literal.pos 2853)] :=
  (lex_2_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2852), (Sat.Literal.pos 107), (Sat.Literal.pos 103), (Sat.Literal.pos 2853)] :=
  (lex_2_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2853) = lexBefore s permutation2 106 := by
  exact (positive_lex_of_descriptor s 2853 permutation2 107 (by rfl)).trans ((lex_skipped s permutation2 106 107 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation2 106) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation2 106 by rw [image2_eq]; rfl))

theorem lex_2_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2854) (Sat.Literal.pos 2853) (Sat.Literal.pos 106) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation2 106 (assignment s)
    (Sat.Literal.pos 2854) (Sat.Literal.pos 2853) (Sat.Literal.pos 106) (Sat.Literal.pos 102) (positive_of_descriptor s 2854 (.lex permutation2 106) (by rfl)) (lex_2_106_prefix s) (positive_select s 106) (lex_2_106_image s)

theorem lex_2_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.pos 106), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation2 106 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2853) (Sat.Literal.pos 106) (Sat.Literal.pos 102) (lex_2_106_prefix s) (positive_select s 106) (lex_2_106_image s)

theorem lex_2_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.pos 2853)] :=
  (lex_2_106_gate s).prop _ (List.Mem.head _)

theorem lex_2_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.neg 106), (Sat.Literal.pos 102)] :=
  (lex_2_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.pos 106), (Sat.Literal.neg 102)] :=
  (lex_2_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.neg 106), (Sat.Literal.neg 102), (Sat.Literal.pos 2854)] :=
  (lex_2_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2853), (Sat.Literal.pos 106), (Sat.Literal.pos 102), (Sat.Literal.pos 2854)] :=
  (lex_2_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2854) = lexBefore s permutation2 105 := by
  exact (positive_lex_of_descriptor s 2854 permutation2 106 (by rfl)).trans ((lex_skipped s permutation2 105 106 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation2 105) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation2 105 by rw [image2_eq]; rfl))

theorem lex_2_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2855) (Sat.Literal.pos 2854) (Sat.Literal.pos 105) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation2 105 (assignment s)
    (Sat.Literal.pos 2855) (Sat.Literal.pos 2854) (Sat.Literal.pos 105) (Sat.Literal.pos 101) (positive_of_descriptor s 2855 (.lex permutation2 105) (by rfl)) (lex_2_105_prefix s) (positive_select s 105) (lex_2_105_image s)

theorem lex_2_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.pos 105), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation2 105 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2854) (Sat.Literal.pos 105) (Sat.Literal.pos 101) (lex_2_105_prefix s) (positive_select s 105) (lex_2_105_image s)

theorem lex_2_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.pos 2854)] :=
  (lex_2_105_gate s).prop _ (List.Mem.head _)

theorem lex_2_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.neg 105), (Sat.Literal.pos 101)] :=
  (lex_2_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.pos 105), (Sat.Literal.neg 101)] :=
  (lex_2_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.neg 105), (Sat.Literal.neg 101), (Sat.Literal.pos 2855)] :=
  (lex_2_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2854), (Sat.Literal.pos 105), (Sat.Literal.pos 101), (Sat.Literal.pos 2855)] :=
  (lex_2_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2855) = lexBefore s permutation2 104 := by
  exact (positive_lex_of_descriptor s 2855 permutation2 105 (by rfl)).trans ((lex_skipped s permutation2 104 105 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation2 104) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation2 104 by rw [image2_eq]; rfl))

theorem lex_2_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2856) (Sat.Literal.pos 2855) (Sat.Literal.pos 104) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation2 104 (assignment s)
    (Sat.Literal.pos 2856) (Sat.Literal.pos 2855) (Sat.Literal.pos 104) (Sat.Literal.pos 100) (positive_of_descriptor s 2856 (.lex permutation2 104) (by rfl)) (lex_2_104_prefix s) (positive_select s 104) (lex_2_104_image s)

theorem lex_2_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.pos 104), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation2 104 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2855) (Sat.Literal.pos 104) (Sat.Literal.pos 100) (lex_2_104_prefix s) (positive_select s 104) (lex_2_104_image s)

theorem lex_2_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.pos 2855)] :=
  (lex_2_104_gate s).prop _ (List.Mem.head _)

theorem lex_2_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.neg 104), (Sat.Literal.pos 100)] :=
  (lex_2_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.pos 104), (Sat.Literal.neg 100)] :=
  (lex_2_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.neg 104), (Sat.Literal.neg 100), (Sat.Literal.pos 2856)] :=
  (lex_2_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2855), (Sat.Literal.pos 104), (Sat.Literal.pos 100), (Sat.Literal.pos 2856)] :=
  (lex_2_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2856) = lexBefore s permutation2 103 := by
  exact (positive_lex_of_descriptor s 2856 permutation2 104 (by rfl)).trans ((lex_skipped s permutation2 103 104 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation2 103) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation2 103 by rw [image2_eq]; rfl))

theorem lex_2_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2857) (Sat.Literal.pos 2856) (Sat.Literal.pos 103) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation2 103 (assignment s)
    (Sat.Literal.pos 2857) (Sat.Literal.pos 2856) (Sat.Literal.pos 103) (Sat.Literal.pos 107) (positive_of_descriptor s 2857 (.lex permutation2 103) (by rfl)) (lex_2_103_prefix s) (positive_select s 103) (lex_2_103_image s)

theorem lex_2_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.pos 103), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation2 103 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2856) (Sat.Literal.pos 103) (Sat.Literal.pos 107) (lex_2_103_prefix s) (positive_select s 103) (lex_2_103_image s)

theorem lex_2_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.pos 2856)] :=
  (lex_2_103_gate s).prop _ (List.Mem.head _)

theorem lex_2_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.neg 103), (Sat.Literal.pos 107)] :=
  (lex_2_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.pos 103), (Sat.Literal.neg 107)] :=
  (lex_2_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.neg 103), (Sat.Literal.neg 107), (Sat.Literal.pos 2857)] :=
  (lex_2_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2856), (Sat.Literal.pos 103), (Sat.Literal.pos 107), (Sat.Literal.pos 2857)] :=
  (lex_2_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2857) = lexBefore s permutation2 102 := by
  exact (positive_lex_of_descriptor s 2857 permutation2 103 (by rfl)).trans ((lex_skipped s permutation2 102 103 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation2 102) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation2 102 by rw [image2_eq]; rfl))

theorem lex_2_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2858) (Sat.Literal.pos 2857) (Sat.Literal.pos 102) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation2 102 (assignment s)
    (Sat.Literal.pos 2858) (Sat.Literal.pos 2857) (Sat.Literal.pos 102) (Sat.Literal.pos 106) (positive_of_descriptor s 2858 (.lex permutation2 102) (by rfl)) (lex_2_102_prefix s) (positive_select s 102) (lex_2_102_image s)

theorem lex_2_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.pos 102), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation2 102 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2857) (Sat.Literal.pos 102) (Sat.Literal.pos 106) (lex_2_102_prefix s) (positive_select s 102) (lex_2_102_image s)

theorem lex_2_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.pos 2857)] :=
  (lex_2_102_gate s).prop _ (List.Mem.head _)

theorem lex_2_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.neg 102), (Sat.Literal.pos 106)] :=
  (lex_2_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.pos 102), (Sat.Literal.neg 106)] :=
  (lex_2_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.neg 102), (Sat.Literal.neg 106), (Sat.Literal.pos 2858)] :=
  (lex_2_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2857), (Sat.Literal.pos 102), (Sat.Literal.pos 106), (Sat.Literal.pos 2858)] :=
  (lex_2_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2858) = lexBefore s permutation2 101 := by
  exact (positive_lex_of_descriptor s 2858 permutation2 102 (by rfl)).trans ((lex_skipped s permutation2 101 102 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation2 101) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation2 101 by rw [image2_eq]; rfl))

theorem lex_2_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2859) (Sat.Literal.pos 2858) (Sat.Literal.pos 101) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation2 101 (assignment s)
    (Sat.Literal.pos 2859) (Sat.Literal.pos 2858) (Sat.Literal.pos 101) (Sat.Literal.pos 105) (positive_of_descriptor s 2859 (.lex permutation2 101) (by rfl)) (lex_2_101_prefix s) (positive_select s 101) (lex_2_101_image s)

theorem lex_2_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.pos 101), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation2 101 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2858) (Sat.Literal.pos 101) (Sat.Literal.pos 105) (lex_2_101_prefix s) (positive_select s 101) (lex_2_101_image s)

theorem lex_2_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.pos 2858)] :=
  (lex_2_101_gate s).prop _ (List.Mem.head _)

theorem lex_2_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.neg 101), (Sat.Literal.pos 105)] :=
  (lex_2_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.pos 101), (Sat.Literal.neg 105)] :=
  (lex_2_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.neg 101), (Sat.Literal.neg 105), (Sat.Literal.pos 2859)] :=
  (lex_2_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2858), (Sat.Literal.pos 101), (Sat.Literal.pos 105), (Sat.Literal.pos 2859)] :=
  (lex_2_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2859) = lexBefore s permutation2 100 := by
  exact (positive_lex_of_descriptor s 2859 permutation2 101 (by rfl)).trans ((lex_skipped s permutation2 100 101 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation2 100) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation2 100 by rw [image2_eq]; rfl))

theorem lex_2_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2860) (Sat.Literal.pos 2859) (Sat.Literal.pos 100) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation2 100 (assignment s)
    (Sat.Literal.pos 2860) (Sat.Literal.pos 2859) (Sat.Literal.pos 100) (Sat.Literal.pos 104) (positive_of_descriptor s 2860 (.lex permutation2 100) (by rfl)) (lex_2_100_prefix s) (positive_select s 100) (lex_2_100_image s)

theorem lex_2_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.pos 100), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation2 100 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2859) (Sat.Literal.pos 100) (Sat.Literal.pos 104) (lex_2_100_prefix s) (positive_select s 100) (lex_2_100_image s)

theorem lex_2_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.pos 2859)] :=
  (lex_2_100_gate s).prop _ (List.Mem.head _)

theorem lex_2_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.neg 100), (Sat.Literal.pos 104)] :=
  (lex_2_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.pos 100), (Sat.Literal.neg 104)] :=
  (lex_2_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.neg 100), (Sat.Literal.neg 104), (Sat.Literal.pos 2860)] :=
  (lex_2_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2859), (Sat.Literal.pos 100), (Sat.Literal.pos 104), (Sat.Literal.pos 2860)] :=
  (lex_2_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2860) = lexBefore s permutation2 91 := by
  exact (positive_lex_of_descriptor s 2860 permutation2 100 (by rfl)).trans ((lex_skipped s permutation2 91 100 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 92 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation2 91) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation2 91 by rw [image2_eq]; rfl))

theorem lex_2_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2861) (Sat.Literal.pos 2860) (Sat.Literal.pos 91) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation2 91 (assignment s)
    (Sat.Literal.pos 2861) (Sat.Literal.pos 2860) (Sat.Literal.pos 91) (Sat.Literal.pos 87) (positive_of_descriptor s 2861 (.lex permutation2 91) (by rfl)) (lex_2_91_prefix s) (positive_select s 91) (lex_2_91_image s)

theorem lex_2_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.pos 91), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation2 91 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2860) (Sat.Literal.pos 91) (Sat.Literal.pos 87) (lex_2_91_prefix s) (positive_select s 91) (lex_2_91_image s)

theorem lex_2_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.pos 2860)] :=
  (lex_2_91_gate s).prop _ (List.Mem.head _)

theorem lex_2_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.neg 91), (Sat.Literal.pos 87)] :=
  (lex_2_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.pos 91), (Sat.Literal.neg 87)] :=
  (lex_2_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.neg 91), (Sat.Literal.neg 87), (Sat.Literal.pos 2861)] :=
  (lex_2_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2860), (Sat.Literal.pos 91), (Sat.Literal.pos 87), (Sat.Literal.pos 2861)] :=
  (lex_2_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2861) = lexBefore s permutation2 90 := by
  exact (positive_lex_of_descriptor s 2861 permutation2 91 (by rfl)).trans ((lex_skipped s permutation2 90 91 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation2 90) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation2 90 by rw [image2_eq]; rfl))

theorem lex_2_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2862) (Sat.Literal.pos 2861) (Sat.Literal.pos 90) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation2 90 (assignment s)
    (Sat.Literal.pos 2862) (Sat.Literal.pos 2861) (Sat.Literal.pos 90) (Sat.Literal.pos 86) (positive_of_descriptor s 2862 (.lex permutation2 90) (by rfl)) (lex_2_90_prefix s) (positive_select s 90) (lex_2_90_image s)

theorem lex_2_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.pos 90), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation2 90 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2861) (Sat.Literal.pos 90) (Sat.Literal.pos 86) (lex_2_90_prefix s) (positive_select s 90) (lex_2_90_image s)

theorem lex_2_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.pos 2861)] :=
  (lex_2_90_gate s).prop _ (List.Mem.head _)

theorem lex_2_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.neg 90), (Sat.Literal.pos 86)] :=
  (lex_2_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.pos 90), (Sat.Literal.neg 86)] :=
  (lex_2_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.neg 90), (Sat.Literal.neg 86), (Sat.Literal.pos 2862)] :=
  (lex_2_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2861), (Sat.Literal.pos 90), (Sat.Literal.pos 86), (Sat.Literal.pos 2862)] :=
  (lex_2_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2862) = lexBefore s permutation2 89 := by
  exact (positive_lex_of_descriptor s 2862 permutation2 90 (by rfl)).trans ((lex_skipped s permutation2 89 90 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation2 89) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation2 89 by rw [image2_eq]; rfl))

theorem lex_2_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2863) (Sat.Literal.pos 2862) (Sat.Literal.pos 89) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation2 89 (assignment s)
    (Sat.Literal.pos 2863) (Sat.Literal.pos 2862) (Sat.Literal.pos 89) (Sat.Literal.pos 85) (positive_of_descriptor s 2863 (.lex permutation2 89) (by rfl)) (lex_2_89_prefix s) (positive_select s 89) (lex_2_89_image s)

theorem lex_2_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.pos 89), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation2 89 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2862) (Sat.Literal.pos 89) (Sat.Literal.pos 85) (lex_2_89_prefix s) (positive_select s 89) (lex_2_89_image s)

theorem lex_2_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.pos 2862)] :=
  (lex_2_89_gate s).prop _ (List.Mem.head _)

theorem lex_2_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.neg 89), (Sat.Literal.pos 85)] :=
  (lex_2_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.pos 89), (Sat.Literal.neg 85)] :=
  (lex_2_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.neg 89), (Sat.Literal.neg 85), (Sat.Literal.pos 2863)] :=
  (lex_2_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2862), (Sat.Literal.pos 89), (Sat.Literal.pos 85), (Sat.Literal.pos 2863)] :=
  (lex_2_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2863) = lexBefore s permutation2 88 := by
  exact (positive_lex_of_descriptor s 2863 permutation2 89 (by rfl)).trans ((lex_skipped s permutation2 88 89 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation2 88) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation2 88 by rw [image2_eq]; rfl))

theorem lex_2_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2864) (Sat.Literal.pos 2863) (Sat.Literal.pos 88) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation2 88 (assignment s)
    (Sat.Literal.pos 2864) (Sat.Literal.pos 2863) (Sat.Literal.pos 88) (Sat.Literal.pos 84) (positive_of_descriptor s 2864 (.lex permutation2 88) (by rfl)) (lex_2_88_prefix s) (positive_select s 88) (lex_2_88_image s)

theorem lex_2_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.pos 88), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation2 88 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2863) (Sat.Literal.pos 88) (Sat.Literal.pos 84) (lex_2_88_prefix s) (positive_select s 88) (lex_2_88_image s)

theorem lex_2_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.pos 2863)] :=
  (lex_2_88_gate s).prop _ (List.Mem.head _)

theorem lex_2_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.neg 88), (Sat.Literal.pos 84)] :=
  (lex_2_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.pos 88), (Sat.Literal.neg 84)] :=
  (lex_2_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.neg 88), (Sat.Literal.neg 84), (Sat.Literal.pos 2864)] :=
  (lex_2_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2863), (Sat.Literal.pos 88), (Sat.Literal.pos 84), (Sat.Literal.pos 2864)] :=
  (lex_2_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2864) = lexBefore s permutation2 87 := by
  exact (positive_lex_of_descriptor s 2864 permutation2 88 (by rfl)).trans ((lex_skipped s permutation2 87 88 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation2 87) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation2 87 by rw [image2_eq]; rfl))

theorem lex_2_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2865) (Sat.Literal.pos 2864) (Sat.Literal.pos 87) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation2 87 (assignment s)
    (Sat.Literal.pos 2865) (Sat.Literal.pos 2864) (Sat.Literal.pos 87) (Sat.Literal.pos 91) (positive_of_descriptor s 2865 (.lex permutation2 87) (by rfl)) (lex_2_87_prefix s) (positive_select s 87) (lex_2_87_image s)

theorem lex_2_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.pos 87), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation2 87 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2864) (Sat.Literal.pos 87) (Sat.Literal.pos 91) (lex_2_87_prefix s) (positive_select s 87) (lex_2_87_image s)

theorem lex_2_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.pos 2864)] :=
  (lex_2_87_gate s).prop _ (List.Mem.head _)

theorem lex_2_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.neg 87), (Sat.Literal.pos 91)] :=
  (lex_2_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.pos 87), (Sat.Literal.neg 91)] :=
  (lex_2_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.neg 87), (Sat.Literal.neg 91), (Sat.Literal.pos 2865)] :=
  (lex_2_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2864), (Sat.Literal.pos 87), (Sat.Literal.pos 91), (Sat.Literal.pos 2865)] :=
  (lex_2_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2865) = lexBefore s permutation2 86 := by
  exact (positive_lex_of_descriptor s 2865 permutation2 87 (by rfl)).trans ((lex_skipped s permutation2 86 87 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation2 86) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation2 86 by rw [image2_eq]; rfl))

theorem lex_2_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2866) (Sat.Literal.pos 2865) (Sat.Literal.pos 86) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation2 86 (assignment s)
    (Sat.Literal.pos 2866) (Sat.Literal.pos 2865) (Sat.Literal.pos 86) (Sat.Literal.pos 90) (positive_of_descriptor s 2866 (.lex permutation2 86) (by rfl)) (lex_2_86_prefix s) (positive_select s 86) (lex_2_86_image s)

theorem lex_2_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.pos 86), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation2 86 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2865) (Sat.Literal.pos 86) (Sat.Literal.pos 90) (lex_2_86_prefix s) (positive_select s 86) (lex_2_86_image s)

theorem lex_2_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.pos 2865)] :=
  (lex_2_86_gate s).prop _ (List.Mem.head _)

theorem lex_2_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.neg 86), (Sat.Literal.pos 90)] :=
  (lex_2_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.pos 86), (Sat.Literal.neg 90)] :=
  (lex_2_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.neg 86), (Sat.Literal.neg 90), (Sat.Literal.pos 2866)] :=
  (lex_2_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2865), (Sat.Literal.pos 86), (Sat.Literal.pos 90), (Sat.Literal.pos 2866)] :=
  (lex_2_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2866) = lexBefore s permutation2 85 := by
  exact (positive_lex_of_descriptor s 2866 permutation2 86 (by rfl)).trans ((lex_skipped s permutation2 85 86 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation2 85) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation2 85 by rw [image2_eq]; rfl))

theorem lex_2_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2867) (Sat.Literal.pos 2866) (Sat.Literal.pos 85) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation2 85 (assignment s)
    (Sat.Literal.pos 2867) (Sat.Literal.pos 2866) (Sat.Literal.pos 85) (Sat.Literal.pos 89) (positive_of_descriptor s 2867 (.lex permutation2 85) (by rfl)) (lex_2_85_prefix s) (positive_select s 85) (lex_2_85_image s)

theorem lex_2_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.pos 85), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation2 85 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2866) (Sat.Literal.pos 85) (Sat.Literal.pos 89) (lex_2_85_prefix s) (positive_select s 85) (lex_2_85_image s)

theorem lex_2_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.pos 2866)] :=
  (lex_2_85_gate s).prop _ (List.Mem.head _)

theorem lex_2_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.neg 85), (Sat.Literal.pos 89)] :=
  (lex_2_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.pos 85), (Sat.Literal.neg 89)] :=
  (lex_2_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.neg 85), (Sat.Literal.neg 89), (Sat.Literal.pos 2867)] :=
  (lex_2_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2866), (Sat.Literal.pos 85), (Sat.Literal.pos 89), (Sat.Literal.pos 2867)] :=
  (lex_2_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2867) = lexBefore s permutation2 84 := by
  exact (positive_lex_of_descriptor s 2867 permutation2 85 (by rfl)).trans ((lex_skipped s permutation2 84 85 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation2 84) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation2 84 by rw [image2_eq]; rfl))

theorem lex_2_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2868) (Sat.Literal.pos 2867) (Sat.Literal.pos 84) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation2 84 (assignment s)
    (Sat.Literal.pos 2868) (Sat.Literal.pos 2867) (Sat.Literal.pos 84) (Sat.Literal.pos 88) (positive_of_descriptor s 2868 (.lex permutation2 84) (by rfl)) (lex_2_84_prefix s) (positive_select s 84) (lex_2_84_image s)

theorem lex_2_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.pos 84), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation2 84 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2867) (Sat.Literal.pos 84) (Sat.Literal.pos 88) (lex_2_84_prefix s) (positive_select s 84) (lex_2_84_image s)

theorem lex_2_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.pos 2867)] :=
  (lex_2_84_gate s).prop _ (List.Mem.head _)

theorem lex_2_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.neg 84), (Sat.Literal.pos 88)] :=
  (lex_2_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.pos 84), (Sat.Literal.neg 88)] :=
  (lex_2_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.neg 84), (Sat.Literal.neg 88), (Sat.Literal.pos 2868)] :=
  (lex_2_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2867), (Sat.Literal.pos 84), (Sat.Literal.pos 88), (Sat.Literal.pos 2868)] :=
  (lex_2_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2868) = lexBefore s permutation2 75 := by
  exact (positive_lex_of_descriptor s 2868 permutation2 84 (by rfl)).trans ((lex_skipped s permutation2 75 84 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 76 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation2 75) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation2 75 by rw [image2_eq]; rfl))

theorem lex_2_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2869) (Sat.Literal.pos 2868) (Sat.Literal.pos 75) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation2 75 (assignment s)
    (Sat.Literal.pos 2869) (Sat.Literal.pos 2868) (Sat.Literal.pos 75) (Sat.Literal.pos 71) (positive_of_descriptor s 2869 (.lex permutation2 75) (by rfl)) (lex_2_75_prefix s) (positive_select s 75) (lex_2_75_image s)

theorem lex_2_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.pos 75), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation2 75 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2868) (Sat.Literal.pos 75) (Sat.Literal.pos 71) (lex_2_75_prefix s) (positive_select s 75) (lex_2_75_image s)

theorem lex_2_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.pos 2868)] :=
  (lex_2_75_gate s).prop _ (List.Mem.head _)

theorem lex_2_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.neg 75), (Sat.Literal.pos 71)] :=
  (lex_2_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.pos 75), (Sat.Literal.neg 71)] :=
  (lex_2_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.neg 75), (Sat.Literal.neg 71), (Sat.Literal.pos 2869)] :=
  (lex_2_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2868), (Sat.Literal.pos 75), (Sat.Literal.pos 71), (Sat.Literal.pos 2869)] :=
  (lex_2_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2869) = lexBefore s permutation2 74 := by
  exact (positive_lex_of_descriptor s 2869 permutation2 75 (by rfl)).trans ((lex_skipped s permutation2 74 75 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation2 74) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation2 74 by rw [image2_eq]; rfl))

theorem lex_2_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2870) (Sat.Literal.pos 2869) (Sat.Literal.pos 74) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation2 74 (assignment s)
    (Sat.Literal.pos 2870) (Sat.Literal.pos 2869) (Sat.Literal.pos 74) (Sat.Literal.pos 70) (positive_of_descriptor s 2870 (.lex permutation2 74) (by rfl)) (lex_2_74_prefix s) (positive_select s 74) (lex_2_74_image s)

theorem lex_2_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.pos 74), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation2 74 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2869) (Sat.Literal.pos 74) (Sat.Literal.pos 70) (lex_2_74_prefix s) (positive_select s 74) (lex_2_74_image s)

theorem lex_2_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.pos 2869)] :=
  (lex_2_74_gate s).prop _ (List.Mem.head _)

theorem lex_2_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.neg 74), (Sat.Literal.pos 70)] :=
  (lex_2_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.pos 74), (Sat.Literal.neg 70)] :=
  (lex_2_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.neg 74), (Sat.Literal.neg 70), (Sat.Literal.pos 2870)] :=
  (lex_2_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2869), (Sat.Literal.pos 74), (Sat.Literal.pos 70), (Sat.Literal.pos 2870)] :=
  (lex_2_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2870) = lexBefore s permutation2 73 := by
  exact (positive_lex_of_descriptor s 2870 permutation2 74 (by rfl)).trans ((lex_skipped s permutation2 73 74 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation2 73) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation2 73 by rw [image2_eq]; rfl))

theorem lex_2_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2871) (Sat.Literal.pos 2870) (Sat.Literal.pos 73) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation2 73 (assignment s)
    (Sat.Literal.pos 2871) (Sat.Literal.pos 2870) (Sat.Literal.pos 73) (Sat.Literal.pos 69) (positive_of_descriptor s 2871 (.lex permutation2 73) (by rfl)) (lex_2_73_prefix s) (positive_select s 73) (lex_2_73_image s)

theorem lex_2_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.pos 73), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation2 73 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2870) (Sat.Literal.pos 73) (Sat.Literal.pos 69) (lex_2_73_prefix s) (positive_select s 73) (lex_2_73_image s)

theorem lex_2_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.pos 2870)] :=
  (lex_2_73_gate s).prop _ (List.Mem.head _)

theorem lex_2_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.neg 73), (Sat.Literal.pos 69)] :=
  (lex_2_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.pos 73), (Sat.Literal.neg 69)] :=
  (lex_2_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.neg 73), (Sat.Literal.neg 69), (Sat.Literal.pos 2871)] :=
  (lex_2_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2870), (Sat.Literal.pos 73), (Sat.Literal.pos 69), (Sat.Literal.pos 2871)] :=
  (lex_2_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2871) = lexBefore s permutation2 72 := by
  exact (positive_lex_of_descriptor s 2871 permutation2 73 (by rfl)).trans ((lex_skipped s permutation2 72 73 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation2 72) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation2 72 by rw [image2_eq]; rfl))

theorem lex_2_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2872) (Sat.Literal.pos 2871) (Sat.Literal.pos 72) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation2 72 (assignment s)
    (Sat.Literal.pos 2872) (Sat.Literal.pos 2871) (Sat.Literal.pos 72) (Sat.Literal.pos 68) (positive_of_descriptor s 2872 (.lex permutation2 72) (by rfl)) (lex_2_72_prefix s) (positive_select s 72) (lex_2_72_image s)

theorem lex_2_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.pos 72), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation2 72 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2871) (Sat.Literal.pos 72) (Sat.Literal.pos 68) (lex_2_72_prefix s) (positive_select s 72) (lex_2_72_image s)

theorem lex_2_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.pos 2871)] :=
  (lex_2_72_gate s).prop _ (List.Mem.head _)

theorem lex_2_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.neg 72), (Sat.Literal.pos 68)] :=
  (lex_2_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.pos 72), (Sat.Literal.neg 68)] :=
  (lex_2_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.neg 72), (Sat.Literal.neg 68), (Sat.Literal.pos 2872)] :=
  (lex_2_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2871), (Sat.Literal.pos 72), (Sat.Literal.pos 68), (Sat.Literal.pos 2872)] :=
  (lex_2_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2872) = lexBefore s permutation2 71 := by
  exact (positive_lex_of_descriptor s 2872 permutation2 72 (by rfl)).trans ((lex_skipped s permutation2 71 72 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation2 71) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation2 71 by rw [image2_eq]; rfl))

theorem lex_2_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2873) (Sat.Literal.pos 2872) (Sat.Literal.pos 71) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation2 71 (assignment s)
    (Sat.Literal.pos 2873) (Sat.Literal.pos 2872) (Sat.Literal.pos 71) (Sat.Literal.pos 75) (positive_of_descriptor s 2873 (.lex permutation2 71) (by rfl)) (lex_2_71_prefix s) (positive_select s 71) (lex_2_71_image s)

theorem lex_2_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.pos 71), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation2 71 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2872) (Sat.Literal.pos 71) (Sat.Literal.pos 75) (lex_2_71_prefix s) (positive_select s 71) (lex_2_71_image s)

theorem lex_2_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.pos 2872)] :=
  (lex_2_71_gate s).prop _ (List.Mem.head _)

theorem lex_2_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.neg 71), (Sat.Literal.pos 75)] :=
  (lex_2_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.pos 71), (Sat.Literal.neg 75)] :=
  (lex_2_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.neg 71), (Sat.Literal.neg 75), (Sat.Literal.pos 2873)] :=
  (lex_2_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2872), (Sat.Literal.pos 71), (Sat.Literal.pos 75), (Sat.Literal.pos 2873)] :=
  (lex_2_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2873) = lexBefore s permutation2 70 := by
  exact (positive_lex_of_descriptor s 2873 permutation2 71 (by rfl)).trans ((lex_skipped s permutation2 70 71 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation2 70) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation2 70 by rw [image2_eq]; rfl))

theorem lex_2_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2874) (Sat.Literal.pos 2873) (Sat.Literal.pos 70) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation2 70 (assignment s)
    (Sat.Literal.pos 2874) (Sat.Literal.pos 2873) (Sat.Literal.pos 70) (Sat.Literal.pos 74) (positive_of_descriptor s 2874 (.lex permutation2 70) (by rfl)) (lex_2_70_prefix s) (positive_select s 70) (lex_2_70_image s)

theorem lex_2_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.pos 70), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation2 70 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2873) (Sat.Literal.pos 70) (Sat.Literal.pos 74) (lex_2_70_prefix s) (positive_select s 70) (lex_2_70_image s)

theorem lex_2_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.pos 2873)] :=
  (lex_2_70_gate s).prop _ (List.Mem.head _)

theorem lex_2_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.neg 70), (Sat.Literal.pos 74)] :=
  (lex_2_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.pos 70), (Sat.Literal.neg 74)] :=
  (lex_2_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.neg 70), (Sat.Literal.neg 74), (Sat.Literal.pos 2874)] :=
  (lex_2_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2873), (Sat.Literal.pos 70), (Sat.Literal.pos 74), (Sat.Literal.pos 2874)] :=
  (lex_2_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2874) = lexBefore s permutation2 69 := by
  exact (positive_lex_of_descriptor s 2874 permutation2 70 (by rfl)).trans ((lex_skipped s permutation2 69 70 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation2 69) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation2 69 by rw [image2_eq]; rfl))

theorem lex_2_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2875) (Sat.Literal.pos 2874) (Sat.Literal.pos 69) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation2 69 (assignment s)
    (Sat.Literal.pos 2875) (Sat.Literal.pos 2874) (Sat.Literal.pos 69) (Sat.Literal.pos 73) (positive_of_descriptor s 2875 (.lex permutation2 69) (by rfl)) (lex_2_69_prefix s) (positive_select s 69) (lex_2_69_image s)

theorem lex_2_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.pos 69), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation2 69 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2874) (Sat.Literal.pos 69) (Sat.Literal.pos 73) (lex_2_69_prefix s) (positive_select s 69) (lex_2_69_image s)

theorem lex_2_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.pos 2874)] :=
  (lex_2_69_gate s).prop _ (List.Mem.head _)

theorem lex_2_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.neg 69), (Sat.Literal.pos 73)] :=
  (lex_2_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.pos 69), (Sat.Literal.neg 73)] :=
  (lex_2_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.neg 69), (Sat.Literal.neg 73), (Sat.Literal.pos 2875)] :=
  (lex_2_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2874), (Sat.Literal.pos 69), (Sat.Literal.pos 73), (Sat.Literal.pos 2875)] :=
  (lex_2_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2875) = lexBefore s permutation2 68 := by
  exact (positive_lex_of_descriptor s 2875 permutation2 69 (by rfl)).trans ((lex_skipped s permutation2 68 69 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation2 68) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation2 68 by rw [image2_eq]; rfl))

theorem lex_2_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2876) (Sat.Literal.pos 2875) (Sat.Literal.pos 68) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation2 68 (assignment s)
    (Sat.Literal.pos 2876) (Sat.Literal.pos 2875) (Sat.Literal.pos 68) (Sat.Literal.pos 72) (positive_of_descriptor s 2876 (.lex permutation2 68) (by rfl)) (lex_2_68_prefix s) (positive_select s 68) (lex_2_68_image s)

theorem lex_2_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.pos 68), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation2 68 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2875) (Sat.Literal.pos 68) (Sat.Literal.pos 72) (lex_2_68_prefix s) (positive_select s 68) (lex_2_68_image s)

theorem lex_2_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.pos 2875)] :=
  (lex_2_68_gate s).prop _ (List.Mem.head _)

theorem lex_2_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.neg 68), (Sat.Literal.pos 72)] :=
  (lex_2_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.pos 68), (Sat.Literal.neg 72)] :=
  (lex_2_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.neg 68), (Sat.Literal.neg 72), (Sat.Literal.pos 2876)] :=
  (lex_2_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2875), (Sat.Literal.pos 68), (Sat.Literal.pos 72), (Sat.Literal.pos 2876)] :=
  (lex_2_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_59_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2876) = lexBefore s permutation2 59 := by
  exact (positive_lex_of_descriptor s 2876 permutation2 68 (by rfl)).trans ((lex_skipped s permutation2 59 68 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 60 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_59_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation2 59) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation2 59 by rw [image2_eq]; rfl))

theorem lex_2_59_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2877) (Sat.Literal.pos 2876) (Sat.Literal.pos 59) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation2 59 (assignment s)
    (Sat.Literal.pos 2877) (Sat.Literal.pos 2876) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (positive_of_descriptor s 2877 (.lex permutation2 59) (by rfl)) (lex_2_59_prefix s) (positive_select s 59) (lex_2_59_image s)

theorem lex_2_59_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation2 59 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2876) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (lex_2_59_prefix s) (positive_select s 59) (lex_2_59_image s)

theorem lex_2_59_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.pos 2876)] :=
  (lex_2_59_gate s).prop _ (List.Mem.head _)

theorem lex_2_59_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.neg 59), (Sat.Literal.pos 55)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_59_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_59_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.neg 59), (Sat.Literal.neg 55), (Sat.Literal.pos 2877)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_59_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2876), (Sat.Literal.pos 59), (Sat.Literal.pos 55), (Sat.Literal.pos 2877)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2877) = lexBefore s permutation2 58 := by
  exact (positive_lex_of_descriptor s 2877 permutation2 59 (by rfl)).trans ((lex_skipped s permutation2 58 59 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation2 58) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation2 58 by rw [image2_eq]; rfl))

theorem lex_2_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2878) (Sat.Literal.pos 2877) (Sat.Literal.pos 58) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation2 58 (assignment s)
    (Sat.Literal.pos 2878) (Sat.Literal.pos 2877) (Sat.Literal.pos 58) (Sat.Literal.pos 54) (positive_of_descriptor s 2878 (.lex permutation2 58) (by rfl)) (lex_2_58_prefix s) (positive_select s 58) (lex_2_58_image s)

theorem lex_2_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.pos 58), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation2 58 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2877) (Sat.Literal.pos 58) (Sat.Literal.pos 54) (lex_2_58_prefix s) (positive_select s 58) (lex_2_58_image s)

theorem lex_2_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.pos 2877)] :=
  (lex_2_58_gate s).prop _ (List.Mem.head _)

theorem lex_2_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.neg 58), (Sat.Literal.pos 54)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.pos 58), (Sat.Literal.neg 54)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.neg 58), (Sat.Literal.neg 54), (Sat.Literal.pos 2878)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2877), (Sat.Literal.pos 58), (Sat.Literal.pos 54), (Sat.Literal.pos 2878)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2878) = lexBefore s permutation2 57 := by
  exact (positive_lex_of_descriptor s 2878 permutation2 58 (by rfl)).trans ((lex_skipped s permutation2 57 58 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation2 57) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation2 57 by rw [image2_eq]; rfl))

theorem lex_2_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2879) (Sat.Literal.pos 2878) (Sat.Literal.pos 57) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation2 57 (assignment s)
    (Sat.Literal.pos 2879) (Sat.Literal.pos 2878) (Sat.Literal.pos 57) (Sat.Literal.pos 53) (positive_of_descriptor s 2879 (.lex permutation2 57) (by rfl)) (lex_2_57_prefix s) (positive_select s 57) (lex_2_57_image s)

theorem lex_2_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.pos 57), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation2 57 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2878) (Sat.Literal.pos 57) (Sat.Literal.pos 53) (lex_2_57_prefix s) (positive_select s 57) (lex_2_57_image s)

theorem lex_2_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.pos 2878)] :=
  (lex_2_57_gate s).prop _ (List.Mem.head _)

theorem lex_2_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.neg 57), (Sat.Literal.pos 53)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.pos 57), (Sat.Literal.neg 53)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.neg 57), (Sat.Literal.neg 53), (Sat.Literal.pos 2879)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2878), (Sat.Literal.pos 57), (Sat.Literal.pos 53), (Sat.Literal.pos 2879)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2879) = lexBefore s permutation2 56 := by
  exact (positive_lex_of_descriptor s 2879 permutation2 57 (by rfl)).trans ((lex_skipped s permutation2 56 57 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation2 56) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation2 56 by rw [image2_eq]; rfl))

theorem lex_2_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2880) (Sat.Literal.pos 2879) (Sat.Literal.pos 56) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation2 56 (assignment s)
    (Sat.Literal.pos 2880) (Sat.Literal.pos 2879) (Sat.Literal.pos 56) (Sat.Literal.pos 52) (positive_of_descriptor s 2880 (.lex permutation2 56) (by rfl)) (lex_2_56_prefix s) (positive_select s 56) (lex_2_56_image s)

theorem lex_2_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.pos 56), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation2 56 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2879) (Sat.Literal.pos 56) (Sat.Literal.pos 52) (lex_2_56_prefix s) (positive_select s 56) (lex_2_56_image s)

theorem lex_2_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.pos 2879)] :=
  (lex_2_56_gate s).prop _ (List.Mem.head _)

theorem lex_2_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.neg 56), (Sat.Literal.pos 52)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.pos 56), (Sat.Literal.neg 52)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.neg 56), (Sat.Literal.neg 52), (Sat.Literal.pos 2880)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2879), (Sat.Literal.pos 56), (Sat.Literal.pos 52), (Sat.Literal.pos 2880)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2880) = lexBefore s permutation2 55 := by
  exact (positive_lex_of_descriptor s 2880 permutation2 56 (by rfl)).trans ((lex_skipped s permutation2 55 56 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation2 55) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation2 55 by rw [image2_eq]; rfl))

theorem lex_2_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2881) (Sat.Literal.pos 2880) (Sat.Literal.pos 55) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation2 55 (assignment s)
    (Sat.Literal.pos 2881) (Sat.Literal.pos 2880) (Sat.Literal.pos 55) (Sat.Literal.pos 59) (positive_of_descriptor s 2881 (.lex permutation2 55) (by rfl)) (lex_2_55_prefix s) (positive_select s 55) (lex_2_55_image s)

theorem lex_2_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.pos 55), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation2 55 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2880) (Sat.Literal.pos 55) (Sat.Literal.pos 59) (lex_2_55_prefix s) (positive_select s 55) (lex_2_55_image s)

theorem lex_2_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.pos 2880)] :=
  (lex_2_55_gate s).prop _ (List.Mem.head _)

theorem lex_2_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.neg 55), (Sat.Literal.pos 59)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.pos 55), (Sat.Literal.neg 59)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.neg 55), (Sat.Literal.neg 59), (Sat.Literal.pos 2881)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2880), (Sat.Literal.pos 55), (Sat.Literal.pos 59), (Sat.Literal.pos 2881)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2881) = lexBefore s permutation2 54 := by
  exact (positive_lex_of_descriptor s 2881 permutation2 55 (by rfl)).trans ((lex_skipped s permutation2 54 55 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation2 54) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation2 54 by rw [image2_eq]; rfl))

theorem lex_2_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2882) (Sat.Literal.pos 2881) (Sat.Literal.pos 54) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation2 54 (assignment s)
    (Sat.Literal.pos 2882) (Sat.Literal.pos 2881) (Sat.Literal.pos 54) (Sat.Literal.pos 58) (positive_of_descriptor s 2882 (.lex permutation2 54) (by rfl)) (lex_2_54_prefix s) (positive_select s 54) (lex_2_54_image s)

theorem lex_2_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.pos 54), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation2 54 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2881) (Sat.Literal.pos 54) (Sat.Literal.pos 58) (lex_2_54_prefix s) (positive_select s 54) (lex_2_54_image s)

theorem lex_2_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.pos 2881)] :=
  (lex_2_54_gate s).prop _ (List.Mem.head _)

theorem lex_2_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.neg 54), (Sat.Literal.pos 58)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.pos 54), (Sat.Literal.neg 58)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.neg 54), (Sat.Literal.neg 58), (Sat.Literal.pos 2882)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2881), (Sat.Literal.pos 54), (Sat.Literal.pos 58), (Sat.Literal.pos 2882)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2882) = lexBefore s permutation2 53 := by
  exact (positive_lex_of_descriptor s 2882 permutation2 54 (by rfl)).trans ((lex_skipped s permutation2 53 54 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation2 53) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation2 53 by rw [image2_eq]; rfl))

theorem lex_2_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2883) (Sat.Literal.pos 2882) (Sat.Literal.pos 53) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation2 53 (assignment s)
    (Sat.Literal.pos 2883) (Sat.Literal.pos 2882) (Sat.Literal.pos 53) (Sat.Literal.pos 57) (positive_of_descriptor s 2883 (.lex permutation2 53) (by rfl)) (lex_2_53_prefix s) (positive_select s 53) (lex_2_53_image s)

theorem lex_2_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.pos 53), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation2 53 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2882) (Sat.Literal.pos 53) (Sat.Literal.pos 57) (lex_2_53_prefix s) (positive_select s 53) (lex_2_53_image s)

theorem lex_2_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.pos 2882)] :=
  (lex_2_53_gate s).prop _ (List.Mem.head _)

theorem lex_2_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.neg 53), (Sat.Literal.pos 57)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.pos 53), (Sat.Literal.neg 57)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.neg 53), (Sat.Literal.neg 57), (Sat.Literal.pos 2883)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2882), (Sat.Literal.pos 53), (Sat.Literal.pos 57), (Sat.Literal.pos 2883)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2883) = lexBefore s permutation2 52 := by
  exact (positive_lex_of_descriptor s 2883 permutation2 53 (by rfl)).trans ((lex_skipped s permutation2 52 53 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation2 52) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation2 52 by rw [image2_eq]; rfl))

theorem lex_2_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2884) (Sat.Literal.pos 2883) (Sat.Literal.pos 52) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation2 52 (assignment s)
    (Sat.Literal.pos 2884) (Sat.Literal.pos 2883) (Sat.Literal.pos 52) (Sat.Literal.pos 56) (positive_of_descriptor s 2884 (.lex permutation2 52) (by rfl)) (lex_2_52_prefix s) (positive_select s 52) (lex_2_52_image s)

theorem lex_2_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.pos 52), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation2 52 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2883) (Sat.Literal.pos 52) (Sat.Literal.pos 56) (lex_2_52_prefix s) (positive_select s 52) (lex_2_52_image s)

theorem lex_2_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.pos 2883)] :=
  (lex_2_52_gate s).prop _ (List.Mem.head _)

theorem lex_2_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.neg 52), (Sat.Literal.pos 56)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.pos 52), (Sat.Literal.neg 56)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.neg 52), (Sat.Literal.neg 56), (Sat.Literal.pos 2884)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2883), (Sat.Literal.pos 52), (Sat.Literal.pos 56), (Sat.Literal.pos 2884)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2884) = lexBefore s permutation2 43 := by
  exact (positive_lex_of_descriptor s 2884 permutation2 52 (by rfl)).trans ((lex_skipped s permutation2 43 52 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 44 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation2 43) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation2 43 by rw [image2_eq]; rfl))

theorem lex_2_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2885) (Sat.Literal.pos 2884) (Sat.Literal.pos 43) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation2 43 (assignment s)
    (Sat.Literal.pos 2885) (Sat.Literal.pos 2884) (Sat.Literal.pos 43) (Sat.Literal.pos 39) (positive_of_descriptor s 2885 (.lex permutation2 43) (by rfl)) (lex_2_43_prefix s) (positive_select s 43) (lex_2_43_image s)

theorem lex_2_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.pos 43), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation2 43 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2884) (Sat.Literal.pos 43) (Sat.Literal.pos 39) (lex_2_43_prefix s) (positive_select s 43) (lex_2_43_image s)

theorem lex_2_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.pos 2884)] :=
  (lex_2_43_gate s).prop _ (List.Mem.head _)

theorem lex_2_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.neg 43), (Sat.Literal.pos 39)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.pos 43), (Sat.Literal.neg 39)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.neg 43), (Sat.Literal.neg 39), (Sat.Literal.pos 2885)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2884), (Sat.Literal.pos 43), (Sat.Literal.pos 39), (Sat.Literal.pos 2885)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2885) = lexBefore s permutation2 42 := by
  exact (positive_lex_of_descriptor s 2885 permutation2 43 (by rfl)).trans ((lex_skipped s permutation2 42 43 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation2 42) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation2 42 by rw [image2_eq]; rfl))

theorem lex_2_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2886) (Sat.Literal.pos 2885) (Sat.Literal.pos 42) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation2 42 (assignment s)
    (Sat.Literal.pos 2886) (Sat.Literal.pos 2885) (Sat.Literal.pos 42) (Sat.Literal.pos 38) (positive_of_descriptor s 2886 (.lex permutation2 42) (by rfl)) (lex_2_42_prefix s) (positive_select s 42) (lex_2_42_image s)

theorem lex_2_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.pos 42), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation2 42 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2885) (Sat.Literal.pos 42) (Sat.Literal.pos 38) (lex_2_42_prefix s) (positive_select s 42) (lex_2_42_image s)

theorem lex_2_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.pos 2885)] :=
  (lex_2_42_gate s).prop _ (List.Mem.head _)

theorem lex_2_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.neg 42), (Sat.Literal.pos 38)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.pos 42), (Sat.Literal.neg 38)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.neg 42), (Sat.Literal.neg 38), (Sat.Literal.pos 2886)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2885), (Sat.Literal.pos 42), (Sat.Literal.pos 38), (Sat.Literal.pos 2886)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2886) = lexBefore s permutation2 41 := by
  exact (positive_lex_of_descriptor s 2886 permutation2 42 (by rfl)).trans ((lex_skipped s permutation2 41 42 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation2 41) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation2 41 by rw [image2_eq]; rfl))

theorem lex_2_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2887) (Sat.Literal.pos 2886) (Sat.Literal.pos 41) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation2 41 (assignment s)
    (Sat.Literal.pos 2887) (Sat.Literal.pos 2886) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (positive_of_descriptor s 2887 (.lex permutation2 41) (by rfl)) (lex_2_41_prefix s) (positive_select s 41) (lex_2_41_image s)

theorem lex_2_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation2 41 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2886) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (lex_2_41_prefix s) (positive_select s 41) (lex_2_41_image s)

theorem lex_2_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.pos 2886)] :=
  (lex_2_41_gate s).prop _ (List.Mem.head _)

theorem lex_2_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.neg 41), (Sat.Literal.pos 37)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.neg 41), (Sat.Literal.neg 37), (Sat.Literal.pos 2887)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2886), (Sat.Literal.pos 41), (Sat.Literal.pos 37), (Sat.Literal.pos 2887)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2887) = lexBefore s permutation2 40 := by
  exact (positive_lex_of_descriptor s 2887 permutation2 41 (by rfl)).trans ((lex_skipped s permutation2 40 41 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation2 40) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation2 40 by rw [image2_eq]; rfl))

theorem lex_2_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2888) (Sat.Literal.pos 2887) (Sat.Literal.pos 40) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation2 40 (assignment s)
    (Sat.Literal.pos 2888) (Sat.Literal.pos 2887) (Sat.Literal.pos 40) (Sat.Literal.pos 36) (positive_of_descriptor s 2888 (.lex permutation2 40) (by rfl)) (lex_2_40_prefix s) (positive_select s 40) (lex_2_40_image s)

theorem lex_2_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.pos 40), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation2 40 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2887) (Sat.Literal.pos 40) (Sat.Literal.pos 36) (lex_2_40_prefix s) (positive_select s 40) (lex_2_40_image s)

theorem lex_2_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.pos 2887)] :=
  (lex_2_40_gate s).prop _ (List.Mem.head _)

theorem lex_2_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.neg 40), (Sat.Literal.pos 36)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.pos 40), (Sat.Literal.neg 36)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.neg 40), (Sat.Literal.neg 36), (Sat.Literal.pos 2888)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2887), (Sat.Literal.pos 40), (Sat.Literal.pos 36), (Sat.Literal.pos 2888)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2888) = lexBefore s permutation2 39 := by
  exact (positive_lex_of_descriptor s 2888 permutation2 40 (by rfl)).trans ((lex_skipped s permutation2 39 40 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation2 39) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 256) = permuteMask permutation2 39 by rw [image2_eq]; rfl))

theorem lex_2_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2889) (Sat.Literal.pos 2888) (Sat.Literal.pos 39) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation2 39 (assignment s)
    (Sat.Literal.pos 2889) (Sat.Literal.pos 2888) (Sat.Literal.pos 39) (Sat.Literal.pos 43) (positive_of_descriptor s 2889 (.lex permutation2 39) (by rfl)) (lex_2_39_prefix s) (positive_select s 39) (lex_2_39_image s)

theorem lex_2_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.pos 39), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation2 39 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2888) (Sat.Literal.pos 39) (Sat.Literal.pos 43) (lex_2_39_prefix s) (positive_select s 39) (lex_2_39_image s)

theorem lex_2_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.pos 2888)] :=
  (lex_2_39_gate s).prop _ (List.Mem.head _)

theorem lex_2_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.neg 39), (Sat.Literal.pos 43)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.pos 39), (Sat.Literal.neg 43)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.neg 39), (Sat.Literal.neg 43), (Sat.Literal.pos 2889)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2888), (Sat.Literal.pos 39), (Sat.Literal.pos 43), (Sat.Literal.pos 2889)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2889) = lexBefore s permutation2 38 := by
  exact (positive_lex_of_descriptor s 2889 permutation2 39 (by rfl)).trans ((lex_skipped s permutation2 38 39 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation2 38) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation2 38 by rw [image2_eq]; rfl))

theorem lex_2_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2890) (Sat.Literal.pos 2889) (Sat.Literal.pos 38) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation2 38 (assignment s)
    (Sat.Literal.pos 2890) (Sat.Literal.pos 2889) (Sat.Literal.pos 38) (Sat.Literal.pos 42) (positive_of_descriptor s 2890 (.lex permutation2 38) (by rfl)) (lex_2_38_prefix s) (positive_select s 38) (lex_2_38_image s)

theorem lex_2_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.pos 38), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation2 38 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2889) (Sat.Literal.pos 38) (Sat.Literal.pos 42) (lex_2_38_prefix s) (positive_select s 38) (lex_2_38_image s)

theorem lex_2_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.pos 2889)] :=
  (lex_2_38_gate s).prop _ (List.Mem.head _)

theorem lex_2_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.neg 38), (Sat.Literal.pos 42)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.pos 38), (Sat.Literal.neg 42)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.neg 38), (Sat.Literal.neg 42), (Sat.Literal.pos 2890)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2889), (Sat.Literal.pos 38), (Sat.Literal.pos 42), (Sat.Literal.pos 2890)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2890) = lexBefore s permutation2 37 := by
  exact (positive_lex_of_descriptor s 2890 permutation2 38 (by rfl)).trans ((lex_skipped s permutation2 37 38 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation2 37) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation2 37 by rw [image2_eq]; rfl))

theorem lex_2_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2891) (Sat.Literal.pos 2890) (Sat.Literal.pos 37) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation2 37 (assignment s)
    (Sat.Literal.pos 2891) (Sat.Literal.pos 2890) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (positive_of_descriptor s 2891 (.lex permutation2 37) (by rfl)) (lex_2_37_prefix s) (positive_select s 37) (lex_2_37_image s)

theorem lex_2_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation2 37 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2890) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (lex_2_37_prefix s) (positive_select s 37) (lex_2_37_image s)

theorem lex_2_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.pos 2890)] :=
  (lex_2_37_gate s).prop _ (List.Mem.head _)

theorem lex_2_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.neg 37), (Sat.Literal.pos 41)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.neg 37), (Sat.Literal.neg 41), (Sat.Literal.pos 2891)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2890), (Sat.Literal.pos 37), (Sat.Literal.pos 41), (Sat.Literal.pos 2891)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2891) = lexBefore s permutation2 36 := by
  exact (positive_lex_of_descriptor s 2891 permutation2 37 (by rfl)).trans ((lex_skipped s permutation2 36 37 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation2 36) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation2 36 by rw [image2_eq]; rfl))

theorem lex_2_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2892) (Sat.Literal.pos 2891) (Sat.Literal.pos 36) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation2 36 (assignment s)
    (Sat.Literal.pos 2892) (Sat.Literal.pos 2891) (Sat.Literal.pos 36) (Sat.Literal.pos 40) (positive_of_descriptor s 2892 (.lex permutation2 36) (by rfl)) (lex_2_36_prefix s) (positive_select s 36) (lex_2_36_image s)

theorem lex_2_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.pos 36), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation2 36 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2891) (Sat.Literal.pos 36) (Sat.Literal.pos 40) (lex_2_36_prefix s) (positive_select s 36) (lex_2_36_image s)

theorem lex_2_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.pos 2891)] :=
  (lex_2_36_gate s).prop _ (List.Mem.head _)

theorem lex_2_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.neg 36), (Sat.Literal.pos 40)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.pos 36), (Sat.Literal.neg 40)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.neg 36), (Sat.Literal.neg 40), (Sat.Literal.pos 2892)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2891), (Sat.Literal.pos 36), (Sat.Literal.pos 40), (Sat.Literal.pos 2892)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2892) = lexBefore s permutation2 27 := by
  exact (positive_lex_of_descriptor s 2892 permutation2 36 (by rfl)).trans ((lex_skipped s permutation2 27 36 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 28 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation2 27) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation2 27 by rw [image2_eq]; rfl))

theorem lex_2_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2893) (Sat.Literal.pos 2892) (Sat.Literal.pos 27) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation2 27 (assignment s)
    (Sat.Literal.pos 2893) (Sat.Literal.pos 2892) (Sat.Literal.pos 27) (Sat.Literal.pos 23) (positive_of_descriptor s 2893 (.lex permutation2 27) (by rfl)) (lex_2_27_prefix s) (positive_select s 27) (lex_2_27_image s)

theorem lex_2_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.pos 27), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation2 27 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2892) (Sat.Literal.pos 27) (Sat.Literal.pos 23) (lex_2_27_prefix s) (positive_select s 27) (lex_2_27_image s)

theorem lex_2_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.pos 2892)] :=
  (lex_2_27_gate s).prop _ (List.Mem.head _)

theorem lex_2_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.neg 27), (Sat.Literal.pos 23)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.pos 27), (Sat.Literal.neg 23)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.neg 27), (Sat.Literal.neg 23), (Sat.Literal.pos 2893)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2892), (Sat.Literal.pos 27), (Sat.Literal.pos 23), (Sat.Literal.pos 2893)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2893) = lexBefore s permutation2 26 := by
  exact (positive_lex_of_descriptor s 2893 permutation2 27 (by rfl)).trans ((lex_skipped s permutation2 26 27 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation2 26) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation2 26 by rw [image2_eq]; rfl))

theorem lex_2_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2894) (Sat.Literal.pos 2893) (Sat.Literal.pos 26) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation2 26 (assignment s)
    (Sat.Literal.pos 2894) (Sat.Literal.pos 2893) (Sat.Literal.pos 26) (Sat.Literal.pos 22) (positive_of_descriptor s 2894 (.lex permutation2 26) (by rfl)) (lex_2_26_prefix s) (positive_select s 26) (lex_2_26_image s)

theorem lex_2_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.pos 26), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation2 26 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2893) (Sat.Literal.pos 26) (Sat.Literal.pos 22) (lex_2_26_prefix s) (positive_select s 26) (lex_2_26_image s)

theorem lex_2_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.pos 2893)] :=
  (lex_2_26_gate s).prop _ (List.Mem.head _)

theorem lex_2_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.neg 26), (Sat.Literal.pos 22)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.pos 26), (Sat.Literal.neg 22)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.neg 26), (Sat.Literal.neg 22), (Sat.Literal.pos 2894)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2893), (Sat.Literal.pos 26), (Sat.Literal.pos 22), (Sat.Literal.pos 2894)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2894) = lexBefore s permutation2 25 := by
  exact (positive_lex_of_descriptor s 2894 permutation2 26 (by rfl)).trans ((lex_skipped s permutation2 25 26 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation2 25) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation2 25 by rw [image2_eq]; rfl))

theorem lex_2_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2895) (Sat.Literal.pos 2894) (Sat.Literal.pos 25) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation2 25 (assignment s)
    (Sat.Literal.pos 2895) (Sat.Literal.pos 2894) (Sat.Literal.pos 25) (Sat.Literal.pos 21) (positive_of_descriptor s 2895 (.lex permutation2 25) (by rfl)) (lex_2_25_prefix s) (positive_select s 25) (lex_2_25_image s)

theorem lex_2_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.pos 25), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation2 25 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2894) (Sat.Literal.pos 25) (Sat.Literal.pos 21) (lex_2_25_prefix s) (positive_select s 25) (lex_2_25_image s)

theorem lex_2_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.pos 2894)] :=
  (lex_2_25_gate s).prop _ (List.Mem.head _)

theorem lex_2_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.neg 25), (Sat.Literal.pos 21)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.pos 25), (Sat.Literal.neg 21)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.neg 25), (Sat.Literal.neg 21), (Sat.Literal.pos 2895)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2894), (Sat.Literal.pos 25), (Sat.Literal.pos 21), (Sat.Literal.pos 2895)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2895) = lexBefore s permutation2 24 := by
  exact (positive_lex_of_descriptor s 2895 permutation2 25 (by rfl)).trans ((lex_skipped s permutation2 24 25 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation2 24) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation2 24 by rw [image2_eq]; rfl))

theorem lex_2_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2896) (Sat.Literal.pos 2895) (Sat.Literal.pos 24) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation2 24 (assignment s)
    (Sat.Literal.pos 2896) (Sat.Literal.pos 2895) (Sat.Literal.pos 24) (Sat.Literal.pos 20) (positive_of_descriptor s 2896 (.lex permutation2 24) (by rfl)) (lex_2_24_prefix s) (positive_select s 24) (lex_2_24_image s)

theorem lex_2_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.pos 24), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation2 24 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2895) (Sat.Literal.pos 24) (Sat.Literal.pos 20) (lex_2_24_prefix s) (positive_select s 24) (lex_2_24_image s)

theorem lex_2_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.pos 2895)] :=
  (lex_2_24_gate s).prop _ (List.Mem.head _)

theorem lex_2_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.neg 24), (Sat.Literal.pos 20)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.pos 24), (Sat.Literal.neg 20)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.neg 24), (Sat.Literal.neg 20), (Sat.Literal.pos 2896)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2895), (Sat.Literal.pos 24), (Sat.Literal.pos 20), (Sat.Literal.pos 2896)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2896) = lexBefore s permutation2 23 := by
  exact (positive_lex_of_descriptor s 2896 permutation2 24 (by rfl)).trans ((lex_skipped s permutation2 23 24 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation2 23) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation2 23 by rw [image2_eq]; rfl))

theorem lex_2_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2897) (Sat.Literal.pos 2896) (Sat.Literal.pos 23) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation2 23 (assignment s)
    (Sat.Literal.pos 2897) (Sat.Literal.pos 2896) (Sat.Literal.pos 23) (Sat.Literal.pos 27) (positive_of_descriptor s 2897 (.lex permutation2 23) (by rfl)) (lex_2_23_prefix s) (positive_select s 23) (lex_2_23_image s)

theorem lex_2_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.pos 23), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation2 23 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2896) (Sat.Literal.pos 23) (Sat.Literal.pos 27) (lex_2_23_prefix s) (positive_select s 23) (lex_2_23_image s)

theorem lex_2_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.pos 2896)] :=
  (lex_2_23_gate s).prop _ (List.Mem.head _)

theorem lex_2_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.neg 23), (Sat.Literal.pos 27)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.pos 23), (Sat.Literal.neg 27)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.neg 23), (Sat.Literal.neg 27), (Sat.Literal.pos 2897)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2896), (Sat.Literal.pos 23), (Sat.Literal.pos 27), (Sat.Literal.pos 2897)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2897) = lexBefore s permutation2 22 := by
  exact (positive_lex_of_descriptor s 2897 permutation2 23 (by rfl)).trans ((lex_skipped s permutation2 22 23 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation2 22) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation2 22 by rw [image2_eq]; rfl))

theorem lex_2_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2898) (Sat.Literal.pos 2897) (Sat.Literal.pos 22) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation2 22 (assignment s)
    (Sat.Literal.pos 2898) (Sat.Literal.pos 2897) (Sat.Literal.pos 22) (Sat.Literal.pos 26) (positive_of_descriptor s 2898 (.lex permutation2 22) (by rfl)) (lex_2_22_prefix s) (positive_select s 22) (lex_2_22_image s)

theorem lex_2_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.pos 22), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation2 22 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2897) (Sat.Literal.pos 22) (Sat.Literal.pos 26) (lex_2_22_prefix s) (positive_select s 22) (lex_2_22_image s)

theorem lex_2_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.pos 2897)] :=
  (lex_2_22_gate s).prop _ (List.Mem.head _)

theorem lex_2_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.neg 22), (Sat.Literal.pos 26)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.pos 22), (Sat.Literal.neg 26)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.neg 22), (Sat.Literal.neg 26), (Sat.Literal.pos 2898)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2897), (Sat.Literal.pos 22), (Sat.Literal.pos 26), (Sat.Literal.pos 2898)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2898) = lexBefore s permutation2 21 := by
  exact (positive_lex_of_descriptor s 2898 permutation2 22 (by rfl)).trans ((lex_skipped s permutation2 21 22 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation2 21) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation2 21 by rw [image2_eq]; rfl))

theorem lex_2_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2899) (Sat.Literal.pos 2898) (Sat.Literal.pos 21) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation2 21 (assignment s)
    (Sat.Literal.pos 2899) (Sat.Literal.pos 2898) (Sat.Literal.pos 21) (Sat.Literal.pos 25) (positive_of_descriptor s 2899 (.lex permutation2 21) (by rfl)) (lex_2_21_prefix s) (positive_select s 21) (lex_2_21_image s)

theorem lex_2_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.pos 21), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation2 21 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2898) (Sat.Literal.pos 21) (Sat.Literal.pos 25) (lex_2_21_prefix s) (positive_select s 21) (lex_2_21_image s)

theorem lex_2_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.pos 2898)] :=
  (lex_2_21_gate s).prop _ (List.Mem.head _)

theorem lex_2_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.neg 21), (Sat.Literal.pos 25)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.pos 21), (Sat.Literal.neg 25)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.neg 21), (Sat.Literal.neg 25), (Sat.Literal.pos 2899)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2898), (Sat.Literal.pos 21), (Sat.Literal.pos 25), (Sat.Literal.pos 2899)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2899) = lexBefore s permutation2 20 := by
  exact (positive_lex_of_descriptor s 2899 permutation2 21 (by rfl)).trans ((lex_skipped s permutation2 20 21 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation2 20) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation2 20 by rw [image2_eq]; rfl))

theorem lex_2_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2900) (Sat.Literal.pos 2899) (Sat.Literal.pos 20) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation2 20 (assignment s)
    (Sat.Literal.pos 2900) (Sat.Literal.pos 2899) (Sat.Literal.pos 20) (Sat.Literal.pos 24) (positive_of_descriptor s 2900 (.lex permutation2 20) (by rfl)) (lex_2_20_prefix s) (positive_select s 20) (lex_2_20_image s)

theorem lex_2_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.pos 20), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation2 20 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2899) (Sat.Literal.pos 20) (Sat.Literal.pos 24) (lex_2_20_prefix s) (positive_select s 20) (lex_2_20_image s)

theorem lex_2_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.pos 2899)] :=
  (lex_2_20_gate s).prop _ (List.Mem.head _)

theorem lex_2_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.neg 20), (Sat.Literal.pos 24)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.pos 20), (Sat.Literal.neg 24)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.neg 20), (Sat.Literal.neg 24), (Sat.Literal.pos 2900)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2899), (Sat.Literal.pos 20), (Sat.Literal.pos 24), (Sat.Literal.pos 2900)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2900) = lexBefore s permutation2 11 := by
  exact (positive_lex_of_descriptor s 2900 permutation2 20 (by rfl)).trans ((lex_skipped s permutation2 11 20 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 12 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation2 11) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation2 11 by rw [image2_eq]; rfl))

theorem lex_2_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2901) (Sat.Literal.pos 2900) (Sat.Literal.pos 11) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation2 11 (assignment s)
    (Sat.Literal.pos 2901) (Sat.Literal.pos 2900) (Sat.Literal.pos 11) (Sat.Literal.pos 7) (positive_of_descriptor s 2901 (.lex permutation2 11) (by rfl)) (lex_2_11_prefix s) (positive_select s 11) (lex_2_11_image s)

theorem lex_2_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.pos 11), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation2 11 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2900) (Sat.Literal.pos 11) (Sat.Literal.pos 7) (lex_2_11_prefix s) (positive_select s 11) (lex_2_11_image s)

theorem lex_2_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.pos 2900)] :=
  (lex_2_11_gate s).prop _ (List.Mem.head _)

theorem lex_2_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.neg 11), (Sat.Literal.pos 7)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.pos 11), (Sat.Literal.neg 7)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.neg 11), (Sat.Literal.neg 7), (Sat.Literal.pos 2901)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2900), (Sat.Literal.pos 11), (Sat.Literal.pos 7), (Sat.Literal.pos 2901)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2901) = lexBefore s permutation2 10 := by
  exact (positive_lex_of_descriptor s 2901 permutation2 11 (by rfl)).trans ((lex_skipped s permutation2 10 11 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation2 10) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation2 10 by rw [image2_eq]; rfl))

theorem lex_2_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2902) (Sat.Literal.pos 2901) (Sat.Literal.pos 10) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation2 10 (assignment s)
    (Sat.Literal.pos 2902) (Sat.Literal.pos 2901) (Sat.Literal.pos 10) (Sat.Literal.pos 6) (positive_of_descriptor s 2902 (.lex permutation2 10) (by rfl)) (lex_2_10_prefix s) (positive_select s 10) (lex_2_10_image s)

theorem lex_2_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.pos 10), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation2 10 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2901) (Sat.Literal.pos 10) (Sat.Literal.pos 6) (lex_2_10_prefix s) (positive_select s 10) (lex_2_10_image s)

theorem lex_2_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.pos 2901)] :=
  (lex_2_10_gate s).prop _ (List.Mem.head _)

theorem lex_2_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.neg 10), (Sat.Literal.pos 6)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.pos 10), (Sat.Literal.neg 6)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.neg 10), (Sat.Literal.neg 6), (Sat.Literal.pos 2902)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2901), (Sat.Literal.pos 10), (Sat.Literal.pos 6), (Sat.Literal.pos 2902)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2902) = lexBefore s permutation2 9 := by
  exact (positive_lex_of_descriptor s 2902 permutation2 10 (by rfl)).trans ((lex_skipped s permutation2 9 10 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation2 9) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation2 9 by rw [image2_eq]; rfl))

theorem lex_2_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2903) (Sat.Literal.pos 2902) (Sat.Literal.pos 9) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation2 9 (assignment s)
    (Sat.Literal.pos 2903) (Sat.Literal.pos 2902) (Sat.Literal.pos 9) (Sat.Literal.pos 5) (positive_of_descriptor s 2903 (.lex permutation2 9) (by rfl)) (lex_2_9_prefix s) (positive_select s 9) (lex_2_9_image s)

theorem lex_2_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.pos 9), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation2 9 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2902) (Sat.Literal.pos 9) (Sat.Literal.pos 5) (lex_2_9_prefix s) (positive_select s 9) (lex_2_9_image s)

theorem lex_2_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.pos 2902)] :=
  (lex_2_9_gate s).prop _ (List.Mem.head _)

theorem lex_2_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.neg 9), (Sat.Literal.pos 5)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.pos 9), (Sat.Literal.neg 5)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.neg 9), (Sat.Literal.neg 5), (Sat.Literal.pos 2903)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2902), (Sat.Literal.pos 9), (Sat.Literal.pos 5), (Sat.Literal.pos 2903)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2903) = lexBefore s permutation2 8 := by
  exact (positive_lex_of_descriptor s 2903 permutation2 9 (by rfl)).trans ((lex_skipped s permutation2 8 9 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation2 8) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation2 8 by rw [image2_eq]; rfl))

theorem lex_2_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2904) (Sat.Literal.pos 2903) (Sat.Literal.pos 8) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation2 8 (assignment s)
    (Sat.Literal.pos 2904) (Sat.Literal.pos 2903) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (positive_of_descriptor s 2904 (.lex permutation2 8) (by rfl)) (lex_2_8_prefix s) (positive_select s 8) (lex_2_8_image s)

theorem lex_2_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation2 8 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2903) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (lex_2_8_prefix s) (positive_select s 8) (lex_2_8_image s)

theorem lex_2_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.pos 2903)] :=
  (lex_2_8_gate s).prop _ (List.Mem.head _)

theorem lex_2_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.neg 8), (Sat.Literal.pos 4)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.neg 8), (Sat.Literal.neg 4), (Sat.Literal.pos 2904)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2903), (Sat.Literal.pos 8), (Sat.Literal.pos 4), (Sat.Literal.pos 2904)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2904) = lexBefore s permutation2 7 := by
  exact (positive_lex_of_descriptor s 2904 permutation2 8 (by rfl)).trans ((lex_skipped s permutation2 7 8 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation2 7) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation2 7 by rw [image2_eq]; rfl))

theorem lex_2_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2905) (Sat.Literal.pos 2904) (Sat.Literal.pos 7) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation2 7 (assignment s)
    (Sat.Literal.pos 2905) (Sat.Literal.pos 2904) (Sat.Literal.pos 7) (Sat.Literal.pos 11) (positive_of_descriptor s 2905 (.lex permutation2 7) (by rfl)) (lex_2_7_prefix s) (positive_select s 7) (lex_2_7_image s)

theorem lex_2_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.pos 7), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation2 7 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2904) (Sat.Literal.pos 7) (Sat.Literal.pos 11) (lex_2_7_prefix s) (positive_select s 7) (lex_2_7_image s)

theorem lex_2_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.pos 2904)] :=
  (lex_2_7_gate s).prop _ (List.Mem.head _)

theorem lex_2_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.neg 7), (Sat.Literal.pos 11)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.pos 7), (Sat.Literal.neg 11)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.neg 7), (Sat.Literal.neg 11), (Sat.Literal.pos 2905)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2904), (Sat.Literal.pos 7), (Sat.Literal.pos 11), (Sat.Literal.pos 2905)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2905) = lexBefore s permutation2 6 := by
  exact (positive_lex_of_descriptor s 2905 permutation2 7 (by rfl)).trans ((lex_skipped s permutation2 6 7 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation2 6) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation2 6 by rw [image2_eq]; rfl))

theorem lex_2_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2906) (Sat.Literal.pos 2905) (Sat.Literal.pos 6) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation2 6 (assignment s)
    (Sat.Literal.pos 2906) (Sat.Literal.pos 2905) (Sat.Literal.pos 6) (Sat.Literal.pos 10) (positive_of_descriptor s 2906 (.lex permutation2 6) (by rfl)) (lex_2_6_prefix s) (positive_select s 6) (lex_2_6_image s)

theorem lex_2_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.pos 6), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation2 6 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2905) (Sat.Literal.pos 6) (Sat.Literal.pos 10) (lex_2_6_prefix s) (positive_select s 6) (lex_2_6_image s)

theorem lex_2_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.pos 2905)] :=
  (lex_2_6_gate s).prop _ (List.Mem.head _)

theorem lex_2_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.neg 6), (Sat.Literal.pos 10)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.pos 6), (Sat.Literal.neg 10)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.neg 6), (Sat.Literal.neg 10), (Sat.Literal.pos 2906)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2905), (Sat.Literal.pos 6), (Sat.Literal.pos 10), (Sat.Literal.pos 2906)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2906) = lexBefore s permutation2 5 := by
  exact (positive_lex_of_descriptor s 2906 permutation2 6 (by rfl)).trans ((lex_skipped s permutation2 5 6 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation2 5) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation2 5 by rw [image2_eq]; rfl))

theorem lex_2_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2907) (Sat.Literal.pos 2906) (Sat.Literal.pos 5) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation2 5 (assignment s)
    (Sat.Literal.pos 2907) (Sat.Literal.pos 2906) (Sat.Literal.pos 5) (Sat.Literal.pos 9) (positive_of_descriptor s 2907 (.lex permutation2 5) (by rfl)) (lex_2_5_prefix s) (positive_select s 5) (lex_2_5_image s)

theorem lex_2_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.pos 5), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation2 5 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2906) (Sat.Literal.pos 5) (Sat.Literal.pos 9) (lex_2_5_prefix s) (positive_select s 5) (lex_2_5_image s)

theorem lex_2_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.pos 2906)] :=
  (lex_2_5_gate s).prop _ (List.Mem.head _)

theorem lex_2_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.neg 5), (Sat.Literal.pos 9)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.pos 5), (Sat.Literal.neg 9)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.neg 5), (Sat.Literal.neg 9), (Sat.Literal.pos 2907)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2906), (Sat.Literal.pos 5), (Sat.Literal.pos 9), (Sat.Literal.pos 2907)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2907) = lexBefore s permutation2 4 := by
  exact (positive_lex_of_descriptor s 2907 permutation2 5 (by rfl)).trans ((lex_skipped s permutation2 4 5 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation2 4) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation2 4 by rw [image2_eq]; rfl))

theorem lex_2_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2908) (Sat.Literal.pos 2907) (Sat.Literal.pos 4) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation2 4 (assignment s)
    (Sat.Literal.pos 2908) (Sat.Literal.pos 2907) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (positive_of_descriptor s 2908 (.lex permutation2 4) (by rfl)) (lex_2_4_prefix s) (positive_select s 4) (lex_2_4_image s)

theorem lex_2_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation2 4 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 2907) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (lex_2_4_prefix s) (positive_select s 4) (lex_2_4_image s)

theorem lex_2_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2908), (Sat.Literal.pos 2907)] :=
  (lex_2_4_gate s).prop _ (List.Mem.head _)

theorem lex_2_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2908), (Sat.Literal.neg 4), (Sat.Literal.pos 8)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2908), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.neg 4), (Sat.Literal.neg 8), (Sat.Literal.pos 2908)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2907), (Sat.Literal.pos 4), (Sat.Literal.pos 8), (Sat.Literal.pos 2908)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation3 247 := by
  exact (negative_falsum s).trans ((lex_first s permutation3 247 (by intro j hj; rw [image3_eq]; exact fixedOnRange_spec image3 248 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_3_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation3 247) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation3 247 by rw [image3_eq]; rfl))

theorem lex_3_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2909) (Sat.Literal.neg 256) (Sat.Literal.pos 247) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation3 247 (assignment s)
    (Sat.Literal.pos 2909) (Sat.Literal.neg 256) (Sat.Literal.pos 247) (Sat.Literal.pos 239) (positive_of_descriptor s 2909 (.lex permutation3 247) (by rfl)) (lex_3_247_prefix s) (positive_select s 247) (lex_3_247_image s)

theorem lex_3_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 247), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation3 247 (hmax permutation3) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 247) (Sat.Literal.pos 239) (lex_3_247_prefix s) (positive_select s 247) (lex_3_247_image s)

theorem lex_3_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.neg 256)] :=
  (lex_3_247_gate s).prop _ (List.Mem.head _)

theorem lex_3_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.neg 247), (Sat.Literal.pos 239)] :=
  (lex_3_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.pos 247), (Sat.Literal.neg 239)] :=
  (lex_3_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 247), (Sat.Literal.neg 239), (Sat.Literal.pos 2909)] :=
  (lex_3_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 247), (Sat.Literal.pos 239), (Sat.Literal.pos 2909)] :=
  (lex_3_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2909) = lexBefore s permutation3 246 := by
  exact (positive_lex_of_descriptor s 2909 permutation3 247 (by rfl)).trans ((lex_skipped s permutation3 246 247 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation3 246) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation3 246 by rw [image3_eq]; rfl))

theorem lex_3_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2910) (Sat.Literal.pos 2909) (Sat.Literal.pos 246) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation3 246 (assignment s)
    (Sat.Literal.pos 2910) (Sat.Literal.pos 2909) (Sat.Literal.pos 246) (Sat.Literal.pos 238) (positive_of_descriptor s 2910 (.lex permutation3 246) (by rfl)) (lex_3_246_prefix s) (positive_select s 246) (lex_3_246_image s)

theorem lex_3_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.pos 246), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation3 246 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2909) (Sat.Literal.pos 246) (Sat.Literal.pos 238) (lex_3_246_prefix s) (positive_select s 246) (lex_3_246_image s)

theorem lex_3_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.pos 2909)] :=
  (lex_3_246_gate s).prop _ (List.Mem.head _)

theorem lex_3_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.neg 246), (Sat.Literal.pos 238)] :=
  (lex_3_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.pos 246), (Sat.Literal.neg 238)] :=
  (lex_3_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.neg 246), (Sat.Literal.neg 238), (Sat.Literal.pos 2910)] :=
  (lex_3_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2909), (Sat.Literal.pos 246), (Sat.Literal.pos 238), (Sat.Literal.pos 2910)] :=
  (lex_3_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2910) = lexBefore s permutation3 245 := by
  exact (positive_lex_of_descriptor s 2910 permutation3 246 (by rfl)).trans ((lex_skipped s permutation3 245 246 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation3 245) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation3 245 by rw [image3_eq]; rfl))

theorem lex_3_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2911) (Sat.Literal.pos 2910) (Sat.Literal.pos 245) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation3 245 (assignment s)
    (Sat.Literal.pos 2911) (Sat.Literal.pos 2910) (Sat.Literal.pos 245) (Sat.Literal.pos 237) (positive_of_descriptor s 2911 (.lex permutation3 245) (by rfl)) (lex_3_245_prefix s) (positive_select s 245) (lex_3_245_image s)

theorem lex_3_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.pos 245), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation3 245 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2910) (Sat.Literal.pos 245) (Sat.Literal.pos 237) (lex_3_245_prefix s) (positive_select s 245) (lex_3_245_image s)

theorem lex_3_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.pos 2910)] :=
  (lex_3_245_gate s).prop _ (List.Mem.head _)

theorem lex_3_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.neg 245), (Sat.Literal.pos 237)] :=
  (lex_3_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.pos 245), (Sat.Literal.neg 237)] :=
  (lex_3_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.neg 245), (Sat.Literal.neg 237), (Sat.Literal.pos 2911)] :=
  (lex_3_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2910), (Sat.Literal.pos 245), (Sat.Literal.pos 237), (Sat.Literal.pos 2911)] :=
  (lex_3_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2911) = lexBefore s permutation3 244 := by
  exact (positive_lex_of_descriptor s 2911 permutation3 245 (by rfl)).trans ((lex_skipped s permutation3 244 245 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation3 244) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation3 244 by rw [image3_eq]; rfl))

theorem lex_3_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2912) (Sat.Literal.pos 2911) (Sat.Literal.pos 244) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation3 244 (assignment s)
    (Sat.Literal.pos 2912) (Sat.Literal.pos 2911) (Sat.Literal.pos 244) (Sat.Literal.pos 236) (positive_of_descriptor s 2912 (.lex permutation3 244) (by rfl)) (lex_3_244_prefix s) (positive_select s 244) (lex_3_244_image s)

theorem lex_3_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.pos 244), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation3 244 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2911) (Sat.Literal.pos 244) (Sat.Literal.pos 236) (lex_3_244_prefix s) (positive_select s 244) (lex_3_244_image s)

theorem lex_3_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.pos 2911)] :=
  (lex_3_244_gate s).prop _ (List.Mem.head _)

theorem lex_3_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.neg 244), (Sat.Literal.pos 236)] :=
  (lex_3_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.pos 244), (Sat.Literal.neg 236)] :=
  (lex_3_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.neg 244), (Sat.Literal.neg 236), (Sat.Literal.pos 2912)] :=
  (lex_3_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2911), (Sat.Literal.pos 244), (Sat.Literal.pos 236), (Sat.Literal.pos 2912)] :=
  (lex_3_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2912) = lexBefore s permutation3 243 := by
  exact (positive_lex_of_descriptor s 2912 permutation3 244 (by rfl)).trans ((lex_skipped s permutation3 243 244 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation3 243) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation3 243 by rw [image3_eq]; rfl))

theorem lex_3_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2913) (Sat.Literal.pos 2912) (Sat.Literal.pos 243) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation3 243 (assignment s)
    (Sat.Literal.pos 2913) (Sat.Literal.pos 2912) (Sat.Literal.pos 243) (Sat.Literal.pos 235) (positive_of_descriptor s 2913 (.lex permutation3 243) (by rfl)) (lex_3_243_prefix s) (positive_select s 243) (lex_3_243_image s)

theorem lex_3_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.pos 243), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation3 243 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2912) (Sat.Literal.pos 243) (Sat.Literal.pos 235) (lex_3_243_prefix s) (positive_select s 243) (lex_3_243_image s)

theorem lex_3_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.pos 2912)] :=
  (lex_3_243_gate s).prop _ (List.Mem.head _)

theorem lex_3_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.neg 243), (Sat.Literal.pos 235)] :=
  (lex_3_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.pos 243), (Sat.Literal.neg 235)] :=
  (lex_3_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.neg 243), (Sat.Literal.neg 235), (Sat.Literal.pos 2913)] :=
  (lex_3_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2912), (Sat.Literal.pos 243), (Sat.Literal.pos 235), (Sat.Literal.pos 2913)] :=
  (lex_3_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2913) = lexBefore s permutation3 242 := by
  exact (positive_lex_of_descriptor s 2913 permutation3 243 (by rfl)).trans ((lex_skipped s permutation3 242 243 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation3 242) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation3 242 by rw [image3_eq]; rfl))

theorem lex_3_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2914) (Sat.Literal.pos 2913) (Sat.Literal.pos 242) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation3 242 (assignment s)
    (Sat.Literal.pos 2914) (Sat.Literal.pos 2913) (Sat.Literal.pos 242) (Sat.Literal.pos 234) (positive_of_descriptor s 2914 (.lex permutation3 242) (by rfl)) (lex_3_242_prefix s) (positive_select s 242) (lex_3_242_image s)

theorem lex_3_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.pos 242), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation3 242 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2913) (Sat.Literal.pos 242) (Sat.Literal.pos 234) (lex_3_242_prefix s) (positive_select s 242) (lex_3_242_image s)

theorem lex_3_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.pos 2913)] :=
  (lex_3_242_gate s).prop _ (List.Mem.head _)

theorem lex_3_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.neg 242), (Sat.Literal.pos 234)] :=
  (lex_3_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.pos 242), (Sat.Literal.neg 234)] :=
  (lex_3_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.neg 242), (Sat.Literal.neg 234), (Sat.Literal.pos 2914)] :=
  (lex_3_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2913), (Sat.Literal.pos 242), (Sat.Literal.pos 234), (Sat.Literal.pos 2914)] :=
  (lex_3_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2914) = lexBefore s permutation3 241 := by
  exact (positive_lex_of_descriptor s 2914 permutation3 242 (by rfl)).trans ((lex_skipped s permutation3 241 242 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation3 241) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation3 241 by rw [image3_eq]; rfl))

theorem lex_3_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2915) (Sat.Literal.pos 2914) (Sat.Literal.pos 241) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation3 241 (assignment s)
    (Sat.Literal.pos 2915) (Sat.Literal.pos 2914) (Sat.Literal.pos 241) (Sat.Literal.pos 233) (positive_of_descriptor s 2915 (.lex permutation3 241) (by rfl)) (lex_3_241_prefix s) (positive_select s 241) (lex_3_241_image s)

theorem lex_3_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.pos 241), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation3 241 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2914) (Sat.Literal.pos 241) (Sat.Literal.pos 233) (lex_3_241_prefix s) (positive_select s 241) (lex_3_241_image s)

theorem lex_3_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.pos 2914)] :=
  (lex_3_241_gate s).prop _ (List.Mem.head _)

theorem lex_3_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.neg 241), (Sat.Literal.pos 233)] :=
  (lex_3_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.pos 241), (Sat.Literal.neg 233)] :=
  (lex_3_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.neg 241), (Sat.Literal.neg 233), (Sat.Literal.pos 2915)] :=
  (lex_3_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2914), (Sat.Literal.pos 241), (Sat.Literal.pos 233), (Sat.Literal.pos 2915)] :=
  (lex_3_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2915) = lexBefore s permutation3 240 := by
  exact (positive_lex_of_descriptor s 2915 permutation3 241 (by rfl)).trans ((lex_skipped s permutation3 240 241 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation3 240) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation3 240 by rw [image3_eq]; rfl))

theorem lex_3_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2916) (Sat.Literal.pos 2915) (Sat.Literal.pos 240) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation3 240 (assignment s)
    (Sat.Literal.pos 2916) (Sat.Literal.pos 2915) (Sat.Literal.pos 240) (Sat.Literal.pos 232) (positive_of_descriptor s 2916 (.lex permutation3 240) (by rfl)) (lex_3_240_prefix s) (positive_select s 240) (lex_3_240_image s)

theorem lex_3_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.pos 240), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation3 240 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2915) (Sat.Literal.pos 240) (Sat.Literal.pos 232) (lex_3_240_prefix s) (positive_select s 240) (lex_3_240_image s)

theorem lex_3_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.pos 2915)] :=
  (lex_3_240_gate s).prop _ (List.Mem.head _)

theorem lex_3_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.neg 240), (Sat.Literal.pos 232)] :=
  (lex_3_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.pos 240), (Sat.Literal.neg 232)] :=
  (lex_3_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.neg 240), (Sat.Literal.neg 232), (Sat.Literal.pos 2916)] :=
  (lex_3_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2915), (Sat.Literal.pos 240), (Sat.Literal.pos 232), (Sat.Literal.pos 2916)] :=
  (lex_3_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2916) = lexBefore s permutation3 239 := by
  exact (positive_lex_of_descriptor s 2916 permutation3 240 (by rfl)).trans ((lex_skipped s permutation3 239 240 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation3 239) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation3 239 by rw [image3_eq]; rfl))

theorem lex_3_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2917) (Sat.Literal.pos 2916) (Sat.Literal.pos 239) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation3 239 (assignment s)
    (Sat.Literal.pos 2917) (Sat.Literal.pos 2916) (Sat.Literal.pos 239) (Sat.Literal.pos 247) (positive_of_descriptor s 2917 (.lex permutation3 239) (by rfl)) (lex_3_239_prefix s) (positive_select s 239) (lex_3_239_image s)

theorem lex_3_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.pos 239), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation3 239 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2916) (Sat.Literal.pos 239) (Sat.Literal.pos 247) (lex_3_239_prefix s) (positive_select s 239) (lex_3_239_image s)

theorem lex_3_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.pos 2916)] :=
  (lex_3_239_gate s).prop _ (List.Mem.head _)

theorem lex_3_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.neg 239), (Sat.Literal.pos 247)] :=
  (lex_3_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.pos 239), (Sat.Literal.neg 247)] :=
  (lex_3_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.neg 239), (Sat.Literal.neg 247), (Sat.Literal.pos 2917)] :=
  (lex_3_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2916), (Sat.Literal.pos 239), (Sat.Literal.pos 247), (Sat.Literal.pos 2917)] :=
  (lex_3_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2917) = lexBefore s permutation3 238 := by
  exact (positive_lex_of_descriptor s 2917 permutation3 239 (by rfl)).trans ((lex_skipped s permutation3 238 239 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation3 238) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation3 238 by rw [image3_eq]; rfl))

theorem lex_3_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2918) (Sat.Literal.pos 2917) (Sat.Literal.pos 238) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation3 238 (assignment s)
    (Sat.Literal.pos 2918) (Sat.Literal.pos 2917) (Sat.Literal.pos 238) (Sat.Literal.pos 246) (positive_of_descriptor s 2918 (.lex permutation3 238) (by rfl)) (lex_3_238_prefix s) (positive_select s 238) (lex_3_238_image s)

theorem lex_3_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.pos 238), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation3 238 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2917) (Sat.Literal.pos 238) (Sat.Literal.pos 246) (lex_3_238_prefix s) (positive_select s 238) (lex_3_238_image s)

theorem lex_3_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.pos 2917)] :=
  (lex_3_238_gate s).prop _ (List.Mem.head _)

theorem lex_3_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.neg 238), (Sat.Literal.pos 246)] :=
  (lex_3_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.pos 238), (Sat.Literal.neg 246)] :=
  (lex_3_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.neg 238), (Sat.Literal.neg 246), (Sat.Literal.pos 2918)] :=
  (lex_3_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2917), (Sat.Literal.pos 238), (Sat.Literal.pos 246), (Sat.Literal.pos 2918)] :=
  (lex_3_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2918) = lexBefore s permutation3 237 := by
  exact (positive_lex_of_descriptor s 2918 permutation3 238 (by rfl)).trans ((lex_skipped s permutation3 237 238 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation3 237) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation3 237 by rw [image3_eq]; rfl))

theorem lex_3_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2919) (Sat.Literal.pos 2918) (Sat.Literal.pos 237) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation3 237 (assignment s)
    (Sat.Literal.pos 2919) (Sat.Literal.pos 2918) (Sat.Literal.pos 237) (Sat.Literal.pos 245) (positive_of_descriptor s 2919 (.lex permutation3 237) (by rfl)) (lex_3_237_prefix s) (positive_select s 237) (lex_3_237_image s)

theorem lex_3_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.pos 237), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation3 237 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2918) (Sat.Literal.pos 237) (Sat.Literal.pos 245) (lex_3_237_prefix s) (positive_select s 237) (lex_3_237_image s)

theorem lex_3_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.pos 2918)] :=
  (lex_3_237_gate s).prop _ (List.Mem.head _)

theorem lex_3_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.neg 237), (Sat.Literal.pos 245)] :=
  (lex_3_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.pos 237), (Sat.Literal.neg 245)] :=
  (lex_3_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.neg 237), (Sat.Literal.neg 245), (Sat.Literal.pos 2919)] :=
  (lex_3_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2918), (Sat.Literal.pos 237), (Sat.Literal.pos 245), (Sat.Literal.pos 2919)] :=
  (lex_3_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2919) = lexBefore s permutation3 236 := by
  exact (positive_lex_of_descriptor s 2919 permutation3 237 (by rfl)).trans ((lex_skipped s permutation3 236 237 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation3 236) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation3 236 by rw [image3_eq]; rfl))

theorem lex_3_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2920) (Sat.Literal.pos 2919) (Sat.Literal.pos 236) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation3 236 (assignment s)
    (Sat.Literal.pos 2920) (Sat.Literal.pos 2919) (Sat.Literal.pos 236) (Sat.Literal.pos 244) (positive_of_descriptor s 2920 (.lex permutation3 236) (by rfl)) (lex_3_236_prefix s) (positive_select s 236) (lex_3_236_image s)

theorem lex_3_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.pos 236), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation3 236 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2919) (Sat.Literal.pos 236) (Sat.Literal.pos 244) (lex_3_236_prefix s) (positive_select s 236) (lex_3_236_image s)

theorem lex_3_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.pos 2919)] :=
  (lex_3_236_gate s).prop _ (List.Mem.head _)

theorem lex_3_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.neg 236), (Sat.Literal.pos 244)] :=
  (lex_3_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.pos 236), (Sat.Literal.neg 244)] :=
  (lex_3_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.neg 236), (Sat.Literal.neg 244), (Sat.Literal.pos 2920)] :=
  (lex_3_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2919), (Sat.Literal.pos 236), (Sat.Literal.pos 244), (Sat.Literal.pos 2920)] :=
  (lex_3_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2920) = lexBefore s permutation3 235 := by
  exact (positive_lex_of_descriptor s 2920 permutation3 236 (by rfl)).trans ((lex_skipped s permutation3 235 236 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation3 235) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation3 235 by rw [image3_eq]; rfl))

theorem lex_3_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2921) (Sat.Literal.pos 2920) (Sat.Literal.pos 235) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation3 235 (assignment s)
    (Sat.Literal.pos 2921) (Sat.Literal.pos 2920) (Sat.Literal.pos 235) (Sat.Literal.pos 243) (positive_of_descriptor s 2921 (.lex permutation3 235) (by rfl)) (lex_3_235_prefix s) (positive_select s 235) (lex_3_235_image s)

theorem lex_3_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.pos 235), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation3 235 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2920) (Sat.Literal.pos 235) (Sat.Literal.pos 243) (lex_3_235_prefix s) (positive_select s 235) (lex_3_235_image s)

theorem lex_3_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.pos 2920)] :=
  (lex_3_235_gate s).prop _ (List.Mem.head _)

theorem lex_3_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.neg 235), (Sat.Literal.pos 243)] :=
  (lex_3_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.pos 235), (Sat.Literal.neg 243)] :=
  (lex_3_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.neg 235), (Sat.Literal.neg 243), (Sat.Literal.pos 2921)] :=
  (lex_3_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2920), (Sat.Literal.pos 235), (Sat.Literal.pos 243), (Sat.Literal.pos 2921)] :=
  (lex_3_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2921) = lexBefore s permutation3 234 := by
  exact (positive_lex_of_descriptor s 2921 permutation3 235 (by rfl)).trans ((lex_skipped s permutation3 234 235 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation3 234) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation3 234 by rw [image3_eq]; rfl))

theorem lex_3_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2922) (Sat.Literal.pos 2921) (Sat.Literal.pos 234) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation3 234 (assignment s)
    (Sat.Literal.pos 2922) (Sat.Literal.pos 2921) (Sat.Literal.pos 234) (Sat.Literal.pos 242) (positive_of_descriptor s 2922 (.lex permutation3 234) (by rfl)) (lex_3_234_prefix s) (positive_select s 234) (lex_3_234_image s)

theorem lex_3_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.pos 234), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation3 234 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2921) (Sat.Literal.pos 234) (Sat.Literal.pos 242) (lex_3_234_prefix s) (positive_select s 234) (lex_3_234_image s)

theorem lex_3_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.pos 2921)] :=
  (lex_3_234_gate s).prop _ (List.Mem.head _)

theorem lex_3_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.neg 234), (Sat.Literal.pos 242)] :=
  (lex_3_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.pos 234), (Sat.Literal.neg 242)] :=
  (lex_3_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.neg 234), (Sat.Literal.neg 242), (Sat.Literal.pos 2922)] :=
  (lex_3_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2921), (Sat.Literal.pos 234), (Sat.Literal.pos 242), (Sat.Literal.pos 2922)] :=
  (lex_3_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2922) = lexBefore s permutation3 233 := by
  exact (positive_lex_of_descriptor s 2922 permutation3 234 (by rfl)).trans ((lex_skipped s permutation3 233 234 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation3 233) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation3 233 by rw [image3_eq]; rfl))

theorem lex_3_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2923) (Sat.Literal.pos 2922) (Sat.Literal.pos 233) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation3 233 (assignment s)
    (Sat.Literal.pos 2923) (Sat.Literal.pos 2922) (Sat.Literal.pos 233) (Sat.Literal.pos 241) (positive_of_descriptor s 2923 (.lex permutation3 233) (by rfl)) (lex_3_233_prefix s) (positive_select s 233) (lex_3_233_image s)

theorem lex_3_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.pos 233), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation3 233 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2922) (Sat.Literal.pos 233) (Sat.Literal.pos 241) (lex_3_233_prefix s) (positive_select s 233) (lex_3_233_image s)

theorem lex_3_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.pos 2922)] :=
  (lex_3_233_gate s).prop _ (List.Mem.head _)

theorem lex_3_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.neg 233), (Sat.Literal.pos 241)] :=
  (lex_3_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.pos 233), (Sat.Literal.neg 241)] :=
  (lex_3_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.neg 233), (Sat.Literal.neg 241), (Sat.Literal.pos 2923)] :=
  (lex_3_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2922), (Sat.Literal.pos 233), (Sat.Literal.pos 241), (Sat.Literal.pos 2923)] :=
  (lex_3_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2923) = lexBefore s permutation3 232 := by
  exact (positive_lex_of_descriptor s 2923 permutation3 233 (by rfl)).trans ((lex_skipped s permutation3 232 233 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation3 232) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation3 232 by rw [image3_eq]; rfl))

theorem lex_3_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2924) (Sat.Literal.pos 2923) (Sat.Literal.pos 232) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation3 232 (assignment s)
    (Sat.Literal.pos 2924) (Sat.Literal.pos 2923) (Sat.Literal.pos 232) (Sat.Literal.pos 240) (positive_of_descriptor s 2924 (.lex permutation3 232) (by rfl)) (lex_3_232_prefix s) (positive_select s 232) (lex_3_232_image s)

theorem lex_3_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.pos 232), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation3 232 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 2923) (Sat.Literal.pos 232) (Sat.Literal.pos 240) (lex_3_232_prefix s) (positive_select s 232) (lex_3_232_image s)

theorem lex_3_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.pos 2923)] :=
  (lex_3_232_gate s).prop _ (List.Mem.head _)

theorem lex_3_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.neg 232), (Sat.Literal.pos 240)] :=
  (lex_3_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2924), (Sat.Literal.pos 232), (Sat.Literal.neg 240)] :=
  (lex_3_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.neg 232), (Sat.Literal.neg 240), (Sat.Literal.pos 2924)] :=
  (lex_3_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2923), (Sat.Literal.pos 232), (Sat.Literal.pos 240), (Sat.Literal.pos 2924)] :=
  (lex_3_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_2_167_gate

end Crown.CertificateData
