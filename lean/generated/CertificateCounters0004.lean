import generated.CertificateAssignment
import Crown.CertificateAssembly

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem counter_227_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247)) := by
  exact counter_gate s 226 2 (assignment s)
    (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247)
    rfl (rfl) rfl (rfl)

theorem clause_8001 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2248), (Sat.Literal.pos 2257)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247))
    [(Sat.Literal.neg 2248), (Sat.Literal.pos 2257)] [(Sat.Literal.neg 2248), (Sat.Literal.pos 2257)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_3 s)

theorem clause_8002 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2247), (Sat.Literal.pos 2257)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2247), (Sat.Literal.pos 2257)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2247), (Sat.Literal.pos 2257)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_3 s)

theorem clause_8003 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247))
    [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_3 s)

theorem clause_8004 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 2247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2257) (Sat.Literal.pos 2248) (Sat.Literal.pos 226) (Sat.Literal.pos 2247))
    [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 2247)] [(Sat.Literal.neg 2257), (Sat.Literal.pos 2248), (Sat.Literal.pos 2247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_3 s)

theorem counter_227_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248)) := by
  exact counter_gate s 226 3 (assignment s)
    (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248)
    rfl (rfl) rfl (rfl)

theorem clause_8005 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2249), (Sat.Literal.pos 2258)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248))
    [(Sat.Literal.neg 2249), (Sat.Literal.pos 2258)] [(Sat.Literal.neg 2249), (Sat.Literal.pos 2258)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_4 s)

theorem clause_8006 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2248), (Sat.Literal.pos 2258)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2248), (Sat.Literal.pos 2258)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2248), (Sat.Literal.pos 2258)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_4 s)

theorem clause_8007 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248))
    [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_4 s)

theorem clause_8008 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 2248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2258) (Sat.Literal.pos 2249) (Sat.Literal.pos 226) (Sat.Literal.pos 2248))
    [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 2248)] [(Sat.Literal.neg 2258), (Sat.Literal.pos 2249), (Sat.Literal.pos 2248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_4 s)

theorem counter_227_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249)) := by
  exact counter_gate s 226 4 (assignment s)
    (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249)
    rfl (rfl) rfl (rfl)

theorem clause_8009 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2250), (Sat.Literal.pos 2259)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249))
    [(Sat.Literal.neg 2250), (Sat.Literal.pos 2259)] [(Sat.Literal.neg 2250), (Sat.Literal.pos 2259)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_5 s)

theorem clause_8010 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2249), (Sat.Literal.pos 2259)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2249), (Sat.Literal.pos 2259)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2249), (Sat.Literal.pos 2259)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_5 s)

theorem clause_8011 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249))
    [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_5 s)

theorem clause_8012 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 2249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2259) (Sat.Literal.pos 2250) (Sat.Literal.pos 226) (Sat.Literal.pos 2249))
    [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 2249)] [(Sat.Literal.neg 2259), (Sat.Literal.pos 2250), (Sat.Literal.pos 2249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_5 s)

theorem counter_227_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250)) := by
  exact counter_gate s 226 5 (assignment s)
    (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250)
    rfl (rfl) rfl (rfl)

theorem clause_8013 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2251), (Sat.Literal.pos 2260)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250))
    [(Sat.Literal.neg 2251), (Sat.Literal.pos 2260)] [(Sat.Literal.neg 2251), (Sat.Literal.pos 2260)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_6 s)

theorem clause_8014 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2250), (Sat.Literal.pos 2260)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2250), (Sat.Literal.pos 2260)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2250), (Sat.Literal.pos 2260)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_6 s)

theorem clause_8015 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250))
    [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_6 s)

theorem clause_8016 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 2250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2260) (Sat.Literal.pos 2251) (Sat.Literal.pos 226) (Sat.Literal.pos 2250))
    [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 2250)] [(Sat.Literal.neg 2260), (Sat.Literal.pos 2251), (Sat.Literal.pos 2250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_6 s)

theorem counter_227_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251)) := by
  exact counter_gate s 226 6 (assignment s)
    (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251)
    rfl (rfl) rfl (rfl)

theorem clause_8017 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2252), (Sat.Literal.pos 2261)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251))
    [(Sat.Literal.neg 2252), (Sat.Literal.pos 2261)] [(Sat.Literal.neg 2252), (Sat.Literal.pos 2261)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_7 s)

theorem clause_8018 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2251), (Sat.Literal.pos 2261)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2251), (Sat.Literal.pos 2261)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2251), (Sat.Literal.pos 2261)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_7 s)

theorem clause_8019 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251))
    [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_7 s)

theorem clause_8020 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 2251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2261) (Sat.Literal.pos 2252) (Sat.Literal.pos 226) (Sat.Literal.pos 2251))
    [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 2251)] [(Sat.Literal.neg 2261), (Sat.Literal.pos 2252), (Sat.Literal.pos 2251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_7 s)

theorem counter_227_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252)) := by
  exact counter_gate s 226 7 (assignment s)
    (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252)
    rfl (rfl) rfl (rfl)

theorem clause_8021 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2253), (Sat.Literal.pos 2262)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252))
    [(Sat.Literal.neg 2253), (Sat.Literal.pos 2262)] [(Sat.Literal.neg 2253), (Sat.Literal.pos 2262)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_8 s)

theorem clause_8022 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2252), (Sat.Literal.pos 2262)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2252), (Sat.Literal.pos 2262)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2252), (Sat.Literal.pos 2262)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_8 s)

theorem clause_8023 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252))
    [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_8 s)

theorem clause_8024 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 2252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2262) (Sat.Literal.pos 2253) (Sat.Literal.pos 226) (Sat.Literal.pos 2252))
    [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 2252)] [(Sat.Literal.neg 2262), (Sat.Literal.pos 2253), (Sat.Literal.pos 2252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_8 s)

theorem counter_227_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253)) := by
  exact counter_gate s 226 8 (assignment s)
    (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253)
    rfl (rfl) rfl (rfl)

theorem clause_8025 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2254), (Sat.Literal.pos 2263)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253))
    [(Sat.Literal.neg 2254), (Sat.Literal.pos 2263)] [(Sat.Literal.neg 2254), (Sat.Literal.pos 2263)] (List.Mem.head _) (by intro l hl; exact hl) (counter_227_9 s)

theorem clause_8026 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 226), (Sat.Literal.neg 2253), (Sat.Literal.pos 2263)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253))
    [(Sat.Literal.neg 226), (Sat.Literal.neg 2253), (Sat.Literal.pos 2263)] [(Sat.Literal.neg 226), (Sat.Literal.neg 2253), (Sat.Literal.pos 2263)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_227_9 s)

theorem clause_8027 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 226)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253))
    [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 226)] [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 226)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_227_9 s)

theorem clause_8028 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 2253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2263) (Sat.Literal.pos 2254) (Sat.Literal.pos 226) (Sat.Literal.pos 2253))
    [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 2253)] [(Sat.Literal.neg 2263), (Sat.Literal.pos 2254), (Sat.Literal.pos 2253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_227_9 s)

theorem counter_228_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256)) := by
  exact counter_gate s 227 0 (assignment s)
    (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 227).symm)

theorem clause_8029 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2255), (Sat.Literal.pos 2264)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2255), (Sat.Literal.pos 2264)] [(Sat.Literal.neg 2255), (Sat.Literal.pos 2264)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_1 s)

theorem clause_8030 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.pos 256), (Sat.Literal.pos 2264)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 227), (Sat.Literal.pos 256), (Sat.Literal.pos 2264)] [(Sat.Literal.neg 227), (Sat.Literal.pos 256), (Sat.Literal.pos 2264)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_1 s)

theorem clause_8031 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_1 s)

theorem clause_8032 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2264) (Sat.Literal.pos 2255) (Sat.Literal.pos 227) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2264), (Sat.Literal.pos 2255), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_1 s)

theorem counter_228_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255)) := by
  exact counter_gate s 227 1 (assignment s)
    (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255)
    rfl (rfl) rfl (rfl)

theorem clause_8033 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2256), (Sat.Literal.pos 2265)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255))
    [(Sat.Literal.neg 2256), (Sat.Literal.pos 2265)] [(Sat.Literal.neg 2256), (Sat.Literal.pos 2265)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_2 s)

theorem clause_8034 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2255), (Sat.Literal.pos 2265)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2255), (Sat.Literal.pos 2265)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2255), (Sat.Literal.pos 2265)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_2 s)

theorem clause_8035 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255))
    [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_2 s)

theorem clause_8036 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 2255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2265) (Sat.Literal.pos 2256) (Sat.Literal.pos 227) (Sat.Literal.pos 2255))
    [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 2255)] [(Sat.Literal.neg 2265), (Sat.Literal.pos 2256), (Sat.Literal.pos 2255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_2 s)

theorem counter_228_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256)) := by
  exact counter_gate s 227 2 (assignment s)
    (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256)
    rfl (rfl) rfl (rfl)

theorem clause_8037 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2257), (Sat.Literal.pos 2266)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256))
    [(Sat.Literal.neg 2257), (Sat.Literal.pos 2266)] [(Sat.Literal.neg 2257), (Sat.Literal.pos 2266)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_3 s)

theorem clause_8038 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2256), (Sat.Literal.pos 2266)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2256), (Sat.Literal.pos 2266)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2256), (Sat.Literal.pos 2266)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_3 s)

theorem clause_8039 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256))
    [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_3 s)

theorem clause_8040 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 2256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2266) (Sat.Literal.pos 2257) (Sat.Literal.pos 227) (Sat.Literal.pos 2256))
    [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 2256)] [(Sat.Literal.neg 2266), (Sat.Literal.pos 2257), (Sat.Literal.pos 2256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_3 s)

theorem counter_228_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257)) := by
  exact counter_gate s 227 3 (assignment s)
    (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257)
    rfl (rfl) rfl (rfl)

theorem clause_8041 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2258), (Sat.Literal.pos 2267)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257))
    [(Sat.Literal.neg 2258), (Sat.Literal.pos 2267)] [(Sat.Literal.neg 2258), (Sat.Literal.pos 2267)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_4 s)

theorem clause_8042 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2257), (Sat.Literal.pos 2267)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2257), (Sat.Literal.pos 2267)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2257), (Sat.Literal.pos 2267)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_4 s)

theorem clause_8043 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257))
    [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_4 s)

theorem clause_8044 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 2257)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2267) (Sat.Literal.pos 2258) (Sat.Literal.pos 227) (Sat.Literal.pos 2257))
    [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 2257)] [(Sat.Literal.neg 2267), (Sat.Literal.pos 2258), (Sat.Literal.pos 2257)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_4 s)

theorem counter_228_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258)) := by
  exact counter_gate s 227 4 (assignment s)
    (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258)
    rfl (rfl) rfl (rfl)

theorem clause_8045 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2259), (Sat.Literal.pos 2268)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258))
    [(Sat.Literal.neg 2259), (Sat.Literal.pos 2268)] [(Sat.Literal.neg 2259), (Sat.Literal.pos 2268)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_5 s)

theorem clause_8046 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2258), (Sat.Literal.pos 2268)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2258), (Sat.Literal.pos 2268)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2258), (Sat.Literal.pos 2268)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_5 s)

theorem clause_8047 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258))
    [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_5 s)

theorem clause_8048 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 2258)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2268) (Sat.Literal.pos 2259) (Sat.Literal.pos 227) (Sat.Literal.pos 2258))
    [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 2258)] [(Sat.Literal.neg 2268), (Sat.Literal.pos 2259), (Sat.Literal.pos 2258)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_5 s)

theorem counter_228_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259)) := by
  exact counter_gate s 227 5 (assignment s)
    (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259)
    rfl (rfl) rfl (rfl)

theorem clause_8049 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2260), (Sat.Literal.pos 2269)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259))
    [(Sat.Literal.neg 2260), (Sat.Literal.pos 2269)] [(Sat.Literal.neg 2260), (Sat.Literal.pos 2269)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_6 s)

theorem clause_8050 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2259), (Sat.Literal.pos 2269)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2259), (Sat.Literal.pos 2269)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2259), (Sat.Literal.pos 2269)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_6 s)

theorem clause_8051 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259))
    [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_6 s)

theorem clause_8052 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 2259)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2269) (Sat.Literal.pos 2260) (Sat.Literal.pos 227) (Sat.Literal.pos 2259))
    [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 2259)] [(Sat.Literal.neg 2269), (Sat.Literal.pos 2260), (Sat.Literal.pos 2259)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_6 s)

theorem counter_228_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260)) := by
  exact counter_gate s 227 6 (assignment s)
    (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260)
    rfl (rfl) rfl (rfl)

theorem clause_8053 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2261), (Sat.Literal.pos 2270)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260))
    [(Sat.Literal.neg 2261), (Sat.Literal.pos 2270)] [(Sat.Literal.neg 2261), (Sat.Literal.pos 2270)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_7 s)

theorem clause_8054 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2260), (Sat.Literal.pos 2270)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2260), (Sat.Literal.pos 2270)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2260), (Sat.Literal.pos 2270)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_7 s)

theorem clause_8055 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260))
    [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_7 s)

theorem clause_8056 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 2260)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2270) (Sat.Literal.pos 2261) (Sat.Literal.pos 227) (Sat.Literal.pos 2260))
    [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 2260)] [(Sat.Literal.neg 2270), (Sat.Literal.pos 2261), (Sat.Literal.pos 2260)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_7 s)

theorem counter_228_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261)) := by
  exact counter_gate s 227 7 (assignment s)
    (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261)
    rfl (rfl) rfl (rfl)

theorem clause_8057 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2262), (Sat.Literal.pos 2271)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261))
    [(Sat.Literal.neg 2262), (Sat.Literal.pos 2271)] [(Sat.Literal.neg 2262), (Sat.Literal.pos 2271)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_8 s)

theorem clause_8058 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2261), (Sat.Literal.pos 2271)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2261), (Sat.Literal.pos 2271)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2261), (Sat.Literal.pos 2271)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_8 s)

theorem clause_8059 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261))
    [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_8 s)

theorem clause_8060 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 2261)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2271) (Sat.Literal.pos 2262) (Sat.Literal.pos 227) (Sat.Literal.pos 2261))
    [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 2261)] [(Sat.Literal.neg 2271), (Sat.Literal.pos 2262), (Sat.Literal.pos 2261)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_8 s)

theorem counter_228_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262)) := by
  exact counter_gate s 227 8 (assignment s)
    (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262)
    rfl (rfl) rfl (rfl)

theorem clause_8061 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2263), (Sat.Literal.pos 2272)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262))
    [(Sat.Literal.neg 2263), (Sat.Literal.pos 2272)] [(Sat.Literal.neg 2263), (Sat.Literal.pos 2272)] (List.Mem.head _) (by intro l hl; exact hl) (counter_228_9 s)

theorem clause_8062 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 227), (Sat.Literal.neg 2262), (Sat.Literal.pos 2272)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262))
    [(Sat.Literal.neg 227), (Sat.Literal.neg 2262), (Sat.Literal.pos 2272)] [(Sat.Literal.neg 227), (Sat.Literal.neg 2262), (Sat.Literal.pos 2272)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_228_9 s)

theorem clause_8063 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 227)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262))
    [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 227)] [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 227)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_228_9 s)

theorem clause_8064 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 2262)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2272) (Sat.Literal.pos 2263) (Sat.Literal.pos 227) (Sat.Literal.pos 2262))
    [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 2262)] [(Sat.Literal.neg 2272), (Sat.Literal.pos 2263), (Sat.Literal.pos 2262)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_228_9 s)

theorem counter_229_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256)) := by
  exact counter_gate s 228 0 (assignment s)
    (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 228).symm)

theorem clause_8065 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2264), (Sat.Literal.pos 2273)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2264), (Sat.Literal.pos 2273)] [(Sat.Literal.neg 2264), (Sat.Literal.pos 2273)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_1 s)

theorem clause_8066 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.pos 256), (Sat.Literal.pos 2273)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 228), (Sat.Literal.pos 256), (Sat.Literal.pos 2273)] [(Sat.Literal.neg 228), (Sat.Literal.pos 256), (Sat.Literal.pos 2273)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_1 s)

theorem clause_8067 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_1 s)

theorem clause_8068 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2273) (Sat.Literal.pos 2264) (Sat.Literal.pos 228) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2273), (Sat.Literal.pos 2264), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_1 s)

theorem counter_229_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264)) := by
  exact counter_gate s 228 1 (assignment s)
    (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264)
    rfl (rfl) rfl (rfl)

theorem clause_8069 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2265), (Sat.Literal.pos 2274)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264))
    [(Sat.Literal.neg 2265), (Sat.Literal.pos 2274)] [(Sat.Literal.neg 2265), (Sat.Literal.pos 2274)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_2 s)

theorem clause_8070 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2264), (Sat.Literal.pos 2274)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2264), (Sat.Literal.pos 2274)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2264), (Sat.Literal.pos 2274)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_2 s)

theorem clause_8071 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264))
    [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_2 s)

theorem clause_8072 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 2264)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2274) (Sat.Literal.pos 2265) (Sat.Literal.pos 228) (Sat.Literal.pos 2264))
    [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 2264)] [(Sat.Literal.neg 2274), (Sat.Literal.pos 2265), (Sat.Literal.pos 2264)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_2 s)

theorem counter_229_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265)) := by
  exact counter_gate s 228 2 (assignment s)
    (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265)
    rfl (rfl) rfl (rfl)

theorem clause_8073 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2266), (Sat.Literal.pos 2275)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265))
    [(Sat.Literal.neg 2266), (Sat.Literal.pos 2275)] [(Sat.Literal.neg 2266), (Sat.Literal.pos 2275)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_3 s)

theorem clause_8074 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2265), (Sat.Literal.pos 2275)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2265), (Sat.Literal.pos 2275)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2265), (Sat.Literal.pos 2275)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_3 s)

theorem clause_8075 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265))
    [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_3 s)

theorem clause_8076 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 2265)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2275) (Sat.Literal.pos 2266) (Sat.Literal.pos 228) (Sat.Literal.pos 2265))
    [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 2265)] [(Sat.Literal.neg 2275), (Sat.Literal.pos 2266), (Sat.Literal.pos 2265)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_3 s)

theorem counter_229_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266)) := by
  exact counter_gate s 228 3 (assignment s)
    (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266)
    rfl (rfl) rfl (rfl)

theorem clause_8077 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2267), (Sat.Literal.pos 2276)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266))
    [(Sat.Literal.neg 2267), (Sat.Literal.pos 2276)] [(Sat.Literal.neg 2267), (Sat.Literal.pos 2276)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_4 s)

theorem clause_8078 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2266), (Sat.Literal.pos 2276)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2266), (Sat.Literal.pos 2276)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2266), (Sat.Literal.pos 2276)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_4 s)

theorem clause_8079 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266))
    [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_4 s)

theorem clause_8080 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 2266)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2276) (Sat.Literal.pos 2267) (Sat.Literal.pos 228) (Sat.Literal.pos 2266))
    [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 2266)] [(Sat.Literal.neg 2276), (Sat.Literal.pos 2267), (Sat.Literal.pos 2266)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_4 s)

theorem counter_229_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267)) := by
  exact counter_gate s 228 4 (assignment s)
    (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267)
    rfl (rfl) rfl (rfl)

theorem clause_8081 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2268), (Sat.Literal.pos 2277)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267))
    [(Sat.Literal.neg 2268), (Sat.Literal.pos 2277)] [(Sat.Literal.neg 2268), (Sat.Literal.pos 2277)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_5 s)

theorem clause_8082 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2267), (Sat.Literal.pos 2277)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2267), (Sat.Literal.pos 2277)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2267), (Sat.Literal.pos 2277)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_5 s)

theorem clause_8083 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267))
    [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_5 s)

theorem clause_8084 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 2267)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2277) (Sat.Literal.pos 2268) (Sat.Literal.pos 228) (Sat.Literal.pos 2267))
    [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 2267)] [(Sat.Literal.neg 2277), (Sat.Literal.pos 2268), (Sat.Literal.pos 2267)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_5 s)

theorem counter_229_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268)) := by
  exact counter_gate s 228 5 (assignment s)
    (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268)
    rfl (rfl) rfl (rfl)

theorem clause_8085 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2269), (Sat.Literal.pos 2278)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268))
    [(Sat.Literal.neg 2269), (Sat.Literal.pos 2278)] [(Sat.Literal.neg 2269), (Sat.Literal.pos 2278)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_6 s)

theorem clause_8086 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2268), (Sat.Literal.pos 2278)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2268), (Sat.Literal.pos 2278)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2268), (Sat.Literal.pos 2278)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_6 s)

theorem clause_8087 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268))
    [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_6 s)

theorem clause_8088 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 2268)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2278) (Sat.Literal.pos 2269) (Sat.Literal.pos 228) (Sat.Literal.pos 2268))
    [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 2268)] [(Sat.Literal.neg 2278), (Sat.Literal.pos 2269), (Sat.Literal.pos 2268)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_6 s)

theorem counter_229_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269)) := by
  exact counter_gate s 228 6 (assignment s)
    (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269)
    rfl (rfl) rfl (rfl)

theorem clause_8089 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2270), (Sat.Literal.pos 2279)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269))
    [(Sat.Literal.neg 2270), (Sat.Literal.pos 2279)] [(Sat.Literal.neg 2270), (Sat.Literal.pos 2279)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_7 s)

theorem clause_8090 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2269), (Sat.Literal.pos 2279)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2269), (Sat.Literal.pos 2279)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2269), (Sat.Literal.pos 2279)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_7 s)

theorem clause_8091 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269))
    [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_7 s)

theorem clause_8092 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 2269)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2279) (Sat.Literal.pos 2270) (Sat.Literal.pos 228) (Sat.Literal.pos 2269))
    [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 2269)] [(Sat.Literal.neg 2279), (Sat.Literal.pos 2270), (Sat.Literal.pos 2269)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_7 s)

theorem counter_229_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270)) := by
  exact counter_gate s 228 7 (assignment s)
    (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270)
    rfl (rfl) rfl (rfl)

theorem clause_8093 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2271), (Sat.Literal.pos 2280)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270))
    [(Sat.Literal.neg 2271), (Sat.Literal.pos 2280)] [(Sat.Literal.neg 2271), (Sat.Literal.pos 2280)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_8 s)

theorem clause_8094 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2270), (Sat.Literal.pos 2280)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2270), (Sat.Literal.pos 2280)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2270), (Sat.Literal.pos 2280)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_8 s)

theorem clause_8095 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270))
    [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_8 s)

theorem clause_8096 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 2270)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2280) (Sat.Literal.pos 2271) (Sat.Literal.pos 228) (Sat.Literal.pos 2270))
    [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 2270)] [(Sat.Literal.neg 2280), (Sat.Literal.pos 2271), (Sat.Literal.pos 2270)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_8 s)

theorem counter_229_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271)) := by
  exact counter_gate s 228 8 (assignment s)
    (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271)
    rfl (rfl) rfl (rfl)

theorem clause_8097 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2272), (Sat.Literal.pos 2281)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271))
    [(Sat.Literal.neg 2272), (Sat.Literal.pos 2281)] [(Sat.Literal.neg 2272), (Sat.Literal.pos 2281)] (List.Mem.head _) (by intro l hl; exact hl) (counter_229_9 s)

theorem clause_8098 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 228), (Sat.Literal.neg 2271), (Sat.Literal.pos 2281)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271))
    [(Sat.Literal.neg 228), (Sat.Literal.neg 2271), (Sat.Literal.pos 2281)] [(Sat.Literal.neg 228), (Sat.Literal.neg 2271), (Sat.Literal.pos 2281)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_229_9 s)

theorem clause_8099 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 228)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271))
    [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 228)] [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 228)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_229_9 s)

theorem clause_8100 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 2271)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2281) (Sat.Literal.pos 2272) (Sat.Literal.pos 228) (Sat.Literal.pos 2271))
    [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 2271)] [(Sat.Literal.neg 2281), (Sat.Literal.pos 2272), (Sat.Literal.pos 2271)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_229_9 s)

theorem counter_230_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256)) := by
  exact counter_gate s 229 0 (assignment s)
    (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 229).symm)

theorem clause_8101 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2273), (Sat.Literal.pos 2282)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2273), (Sat.Literal.pos 2282)] [(Sat.Literal.neg 2273), (Sat.Literal.pos 2282)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_1 s)

theorem clause_8102 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.pos 256), (Sat.Literal.pos 2282)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 229), (Sat.Literal.pos 256), (Sat.Literal.pos 2282)] [(Sat.Literal.neg 229), (Sat.Literal.pos 256), (Sat.Literal.pos 2282)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_1 s)

theorem clause_8103 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_1 s)

theorem clause_8104 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2282) (Sat.Literal.pos 2273) (Sat.Literal.pos 229) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2282), (Sat.Literal.pos 2273), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_1 s)

theorem counter_230_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273)) := by
  exact counter_gate s 229 1 (assignment s)
    (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273)
    rfl (rfl) rfl (rfl)

theorem clause_8105 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2274), (Sat.Literal.pos 2283)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273))
    [(Sat.Literal.neg 2274), (Sat.Literal.pos 2283)] [(Sat.Literal.neg 2274), (Sat.Literal.pos 2283)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_2 s)

theorem clause_8106 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2273), (Sat.Literal.pos 2283)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2273), (Sat.Literal.pos 2283)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2273), (Sat.Literal.pos 2283)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_2 s)

theorem clause_8107 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273))
    [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_2 s)

theorem clause_8108 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 2273)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2283) (Sat.Literal.pos 2274) (Sat.Literal.pos 229) (Sat.Literal.pos 2273))
    [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 2273)] [(Sat.Literal.neg 2283), (Sat.Literal.pos 2274), (Sat.Literal.pos 2273)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_2 s)

theorem counter_230_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274)) := by
  exact counter_gate s 229 2 (assignment s)
    (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274)
    rfl (rfl) rfl (rfl)

theorem clause_8109 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2275), (Sat.Literal.pos 2284)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274))
    [(Sat.Literal.neg 2275), (Sat.Literal.pos 2284)] [(Sat.Literal.neg 2275), (Sat.Literal.pos 2284)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_3 s)

theorem clause_8110 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2274), (Sat.Literal.pos 2284)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2274), (Sat.Literal.pos 2284)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2274), (Sat.Literal.pos 2284)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_3 s)

theorem clause_8111 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274))
    [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_3 s)

theorem clause_8112 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 2274)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2284) (Sat.Literal.pos 2275) (Sat.Literal.pos 229) (Sat.Literal.pos 2274))
    [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 2274)] [(Sat.Literal.neg 2284), (Sat.Literal.pos 2275), (Sat.Literal.pos 2274)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_3 s)

theorem counter_230_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275)) := by
  exact counter_gate s 229 3 (assignment s)
    (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275)
    rfl (rfl) rfl (rfl)

theorem clause_8113 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2276), (Sat.Literal.pos 2285)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275))
    [(Sat.Literal.neg 2276), (Sat.Literal.pos 2285)] [(Sat.Literal.neg 2276), (Sat.Literal.pos 2285)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_4 s)

theorem clause_8114 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2275), (Sat.Literal.pos 2285)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2275), (Sat.Literal.pos 2285)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2275), (Sat.Literal.pos 2285)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_4 s)

theorem clause_8115 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275))
    [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_4 s)

theorem clause_8116 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 2275)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2285) (Sat.Literal.pos 2276) (Sat.Literal.pos 229) (Sat.Literal.pos 2275))
    [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 2275)] [(Sat.Literal.neg 2285), (Sat.Literal.pos 2276), (Sat.Literal.pos 2275)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_4 s)

theorem counter_230_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276)) := by
  exact counter_gate s 229 4 (assignment s)
    (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276)
    rfl (rfl) rfl (rfl)

theorem clause_8117 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2277), (Sat.Literal.pos 2286)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276))
    [(Sat.Literal.neg 2277), (Sat.Literal.pos 2286)] [(Sat.Literal.neg 2277), (Sat.Literal.pos 2286)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_5 s)

theorem clause_8118 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2276), (Sat.Literal.pos 2286)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2276), (Sat.Literal.pos 2286)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2276), (Sat.Literal.pos 2286)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_5 s)

theorem clause_8119 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276))
    [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_5 s)

theorem clause_8120 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 2276)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2286) (Sat.Literal.pos 2277) (Sat.Literal.pos 229) (Sat.Literal.pos 2276))
    [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 2276)] [(Sat.Literal.neg 2286), (Sat.Literal.pos 2277), (Sat.Literal.pos 2276)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_5 s)

theorem counter_230_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277)) := by
  exact counter_gate s 229 5 (assignment s)
    (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277)
    rfl (rfl) rfl (rfl)

theorem clause_8121 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2278), (Sat.Literal.pos 2287)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277))
    [(Sat.Literal.neg 2278), (Sat.Literal.pos 2287)] [(Sat.Literal.neg 2278), (Sat.Literal.pos 2287)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_6 s)

theorem clause_8122 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2277), (Sat.Literal.pos 2287)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2277), (Sat.Literal.pos 2287)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2277), (Sat.Literal.pos 2287)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_6 s)

theorem clause_8123 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277))
    [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_6 s)

theorem clause_8124 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 2277)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2287) (Sat.Literal.pos 2278) (Sat.Literal.pos 229) (Sat.Literal.pos 2277))
    [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 2277)] [(Sat.Literal.neg 2287), (Sat.Literal.pos 2278), (Sat.Literal.pos 2277)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_6 s)

theorem counter_230_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278)) := by
  exact counter_gate s 229 6 (assignment s)
    (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278)
    rfl (rfl) rfl (rfl)

theorem clause_8125 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2279), (Sat.Literal.pos 2288)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278))
    [(Sat.Literal.neg 2279), (Sat.Literal.pos 2288)] [(Sat.Literal.neg 2279), (Sat.Literal.pos 2288)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_7 s)

theorem clause_8126 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2278), (Sat.Literal.pos 2288)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2278), (Sat.Literal.pos 2288)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2278), (Sat.Literal.pos 2288)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_7 s)

theorem clause_8127 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278))
    [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_7 s)

theorem clause_8128 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 2278)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2288) (Sat.Literal.pos 2279) (Sat.Literal.pos 229) (Sat.Literal.pos 2278))
    [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 2278)] [(Sat.Literal.neg 2288), (Sat.Literal.pos 2279), (Sat.Literal.pos 2278)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_7 s)

theorem counter_230_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279)) := by
  exact counter_gate s 229 7 (assignment s)
    (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279)
    rfl (rfl) rfl (rfl)

theorem clause_8129 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2280), (Sat.Literal.pos 2289)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279))
    [(Sat.Literal.neg 2280), (Sat.Literal.pos 2289)] [(Sat.Literal.neg 2280), (Sat.Literal.pos 2289)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_8 s)

theorem clause_8130 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2279), (Sat.Literal.pos 2289)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2279), (Sat.Literal.pos 2289)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2279), (Sat.Literal.pos 2289)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_8 s)

theorem clause_8131 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279))
    [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_8 s)

theorem clause_8132 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 2279)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2289) (Sat.Literal.pos 2280) (Sat.Literal.pos 229) (Sat.Literal.pos 2279))
    [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 2279)] [(Sat.Literal.neg 2289), (Sat.Literal.pos 2280), (Sat.Literal.pos 2279)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_8 s)

theorem counter_230_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280)) := by
  exact counter_gate s 229 8 (assignment s)
    (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280)
    rfl (rfl) rfl (rfl)

theorem clause_8133 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2281), (Sat.Literal.pos 2290)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280))
    [(Sat.Literal.neg 2281), (Sat.Literal.pos 2290)] [(Sat.Literal.neg 2281), (Sat.Literal.pos 2290)] (List.Mem.head _) (by intro l hl; exact hl) (counter_230_9 s)

theorem clause_8134 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 229), (Sat.Literal.neg 2280), (Sat.Literal.pos 2290)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280))
    [(Sat.Literal.neg 229), (Sat.Literal.neg 2280), (Sat.Literal.pos 2290)] [(Sat.Literal.neg 229), (Sat.Literal.neg 2280), (Sat.Literal.pos 2290)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_230_9 s)

theorem clause_8135 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 229)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280))
    [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 229)] [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 229)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_230_9 s)

theorem clause_8136 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 2280)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2290) (Sat.Literal.pos 2281) (Sat.Literal.pos 229) (Sat.Literal.pos 2280))
    [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 2280)] [(Sat.Literal.neg 2290), (Sat.Literal.pos 2281), (Sat.Literal.pos 2280)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_230_9 s)

theorem counter_231_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256)) := by
  exact counter_gate s 230 0 (assignment s)
    (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 230).symm)

theorem clause_8137 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2282), (Sat.Literal.pos 2291)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2282), (Sat.Literal.pos 2291)] [(Sat.Literal.neg 2282), (Sat.Literal.pos 2291)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_1 s)

theorem clause_8138 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.pos 256), (Sat.Literal.pos 2291)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 230), (Sat.Literal.pos 256), (Sat.Literal.pos 2291)] [(Sat.Literal.neg 230), (Sat.Literal.pos 256), (Sat.Literal.pos 2291)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_1 s)

theorem clause_8139 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_1 s)

theorem clause_8140 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2291) (Sat.Literal.pos 2282) (Sat.Literal.pos 230) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2291), (Sat.Literal.pos 2282), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_1 s)

theorem counter_231_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282)) := by
  exact counter_gate s 230 1 (assignment s)
    (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282)
    rfl (rfl) rfl (rfl)

theorem clause_8141 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2283), (Sat.Literal.pos 2292)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282))
    [(Sat.Literal.neg 2283), (Sat.Literal.pos 2292)] [(Sat.Literal.neg 2283), (Sat.Literal.pos 2292)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_2 s)

theorem clause_8142 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2282), (Sat.Literal.pos 2292)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2282), (Sat.Literal.pos 2292)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2282), (Sat.Literal.pos 2292)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_2 s)

theorem clause_8143 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282))
    [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_2 s)

theorem clause_8144 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 2282)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2292) (Sat.Literal.pos 2283) (Sat.Literal.pos 230) (Sat.Literal.pos 2282))
    [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 2282)] [(Sat.Literal.neg 2292), (Sat.Literal.pos 2283), (Sat.Literal.pos 2282)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_2 s)

theorem counter_231_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283)) := by
  exact counter_gate s 230 2 (assignment s)
    (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283)
    rfl (rfl) rfl (rfl)

theorem clause_8145 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2284), (Sat.Literal.pos 2293)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283))
    [(Sat.Literal.neg 2284), (Sat.Literal.pos 2293)] [(Sat.Literal.neg 2284), (Sat.Literal.pos 2293)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_3 s)

theorem clause_8146 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2283), (Sat.Literal.pos 2293)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2283), (Sat.Literal.pos 2293)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2283), (Sat.Literal.pos 2293)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_3 s)

theorem clause_8147 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283))
    [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_3 s)

theorem clause_8148 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 2283)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2293) (Sat.Literal.pos 2284) (Sat.Literal.pos 230) (Sat.Literal.pos 2283))
    [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 2283)] [(Sat.Literal.neg 2293), (Sat.Literal.pos 2284), (Sat.Literal.pos 2283)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_3 s)

theorem counter_231_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284)) := by
  exact counter_gate s 230 3 (assignment s)
    (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284)
    rfl (rfl) rfl (rfl)

theorem clause_8149 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2285), (Sat.Literal.pos 2294)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284))
    [(Sat.Literal.neg 2285), (Sat.Literal.pos 2294)] [(Sat.Literal.neg 2285), (Sat.Literal.pos 2294)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_4 s)

theorem clause_8150 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2284), (Sat.Literal.pos 2294)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2284), (Sat.Literal.pos 2294)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2284), (Sat.Literal.pos 2294)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_4 s)

theorem clause_8151 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284))
    [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_4 s)

theorem clause_8152 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 2284)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2294) (Sat.Literal.pos 2285) (Sat.Literal.pos 230) (Sat.Literal.pos 2284))
    [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 2284)] [(Sat.Literal.neg 2294), (Sat.Literal.pos 2285), (Sat.Literal.pos 2284)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_4 s)

theorem counter_231_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285)) := by
  exact counter_gate s 230 4 (assignment s)
    (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285)
    rfl (rfl) rfl (rfl)

theorem clause_8153 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2286), (Sat.Literal.pos 2295)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285))
    [(Sat.Literal.neg 2286), (Sat.Literal.pos 2295)] [(Sat.Literal.neg 2286), (Sat.Literal.pos 2295)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_5 s)

theorem clause_8154 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2285), (Sat.Literal.pos 2295)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2285), (Sat.Literal.pos 2295)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2285), (Sat.Literal.pos 2295)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_5 s)

theorem clause_8155 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285))
    [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_5 s)

theorem clause_8156 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 2285)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2295) (Sat.Literal.pos 2286) (Sat.Literal.pos 230) (Sat.Literal.pos 2285))
    [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 2285)] [(Sat.Literal.neg 2295), (Sat.Literal.pos 2286), (Sat.Literal.pos 2285)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_5 s)

theorem counter_231_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286)) := by
  exact counter_gate s 230 5 (assignment s)
    (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286)
    rfl (rfl) rfl (rfl)

theorem clause_8157 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2287), (Sat.Literal.pos 2296)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286))
    [(Sat.Literal.neg 2287), (Sat.Literal.pos 2296)] [(Sat.Literal.neg 2287), (Sat.Literal.pos 2296)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_6 s)

theorem clause_8158 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2286), (Sat.Literal.pos 2296)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2286), (Sat.Literal.pos 2296)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2286), (Sat.Literal.pos 2296)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_6 s)

theorem clause_8159 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286))
    [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_6 s)

theorem clause_8160 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 2286)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2296) (Sat.Literal.pos 2287) (Sat.Literal.pos 230) (Sat.Literal.pos 2286))
    [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 2286)] [(Sat.Literal.neg 2296), (Sat.Literal.pos 2287), (Sat.Literal.pos 2286)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_6 s)

theorem counter_231_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287)) := by
  exact counter_gate s 230 6 (assignment s)
    (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287)
    rfl (rfl) rfl (rfl)

theorem clause_8161 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2288), (Sat.Literal.pos 2297)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287))
    [(Sat.Literal.neg 2288), (Sat.Literal.pos 2297)] [(Sat.Literal.neg 2288), (Sat.Literal.pos 2297)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_7 s)

theorem clause_8162 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2287), (Sat.Literal.pos 2297)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2287), (Sat.Literal.pos 2297)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2287), (Sat.Literal.pos 2297)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_7 s)

theorem clause_8163 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287))
    [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_7 s)

theorem clause_8164 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 2287)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2297) (Sat.Literal.pos 2288) (Sat.Literal.pos 230) (Sat.Literal.pos 2287))
    [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 2287)] [(Sat.Literal.neg 2297), (Sat.Literal.pos 2288), (Sat.Literal.pos 2287)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_7 s)

theorem counter_231_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288)) := by
  exact counter_gate s 230 7 (assignment s)
    (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288)
    rfl (rfl) rfl (rfl)

theorem clause_8165 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2289), (Sat.Literal.pos 2298)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288))
    [(Sat.Literal.neg 2289), (Sat.Literal.pos 2298)] [(Sat.Literal.neg 2289), (Sat.Literal.pos 2298)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_8 s)

theorem clause_8166 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2288), (Sat.Literal.pos 2298)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2288), (Sat.Literal.pos 2298)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2288), (Sat.Literal.pos 2298)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_8 s)

theorem clause_8167 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288))
    [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_8 s)

theorem clause_8168 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 2288)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2298) (Sat.Literal.pos 2289) (Sat.Literal.pos 230) (Sat.Literal.pos 2288))
    [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 2288)] [(Sat.Literal.neg 2298), (Sat.Literal.pos 2289), (Sat.Literal.pos 2288)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_8 s)

theorem counter_231_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289)) := by
  exact counter_gate s 230 8 (assignment s)
    (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289)
    rfl (rfl) rfl (rfl)

theorem clause_8169 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2290), (Sat.Literal.pos 2299)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289))
    [(Sat.Literal.neg 2290), (Sat.Literal.pos 2299)] [(Sat.Literal.neg 2290), (Sat.Literal.pos 2299)] (List.Mem.head _) (by intro l hl; exact hl) (counter_231_9 s)

theorem clause_8170 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 230), (Sat.Literal.neg 2289), (Sat.Literal.pos 2299)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289))
    [(Sat.Literal.neg 230), (Sat.Literal.neg 2289), (Sat.Literal.pos 2299)] [(Sat.Literal.neg 230), (Sat.Literal.neg 2289), (Sat.Literal.pos 2299)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_231_9 s)

theorem clause_8171 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 230)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289))
    [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 230)] [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 230)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_231_9 s)

theorem clause_8172 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 2289)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2299) (Sat.Literal.pos 2290) (Sat.Literal.pos 230) (Sat.Literal.pos 2289))
    [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 2289)] [(Sat.Literal.neg 2299), (Sat.Literal.pos 2290), (Sat.Literal.pos 2289)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_231_9 s)

theorem counter_232_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256)) := by
  exact counter_gate s 231 0 (assignment s)
    (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 231).symm)

theorem clause_8173 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2291), (Sat.Literal.pos 2300)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2291), (Sat.Literal.pos 2300)] [(Sat.Literal.neg 2291), (Sat.Literal.pos 2300)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_1 s)

theorem clause_8174 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.pos 256), (Sat.Literal.pos 2300)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 231), (Sat.Literal.pos 256), (Sat.Literal.pos 2300)] [(Sat.Literal.neg 231), (Sat.Literal.pos 256), (Sat.Literal.pos 2300)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_1 s)

theorem clause_8175 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_1 s)

theorem clause_8176 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2300) (Sat.Literal.pos 2291) (Sat.Literal.pos 231) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2300), (Sat.Literal.pos 2291), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_1 s)

theorem counter_232_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291)) := by
  exact counter_gate s 231 1 (assignment s)
    (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291)
    rfl (rfl) rfl (rfl)

theorem clause_8177 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2292), (Sat.Literal.pos 2301)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291))
    [(Sat.Literal.neg 2292), (Sat.Literal.pos 2301)] [(Sat.Literal.neg 2292), (Sat.Literal.pos 2301)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_2 s)

theorem clause_8178 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2291), (Sat.Literal.pos 2301)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2291), (Sat.Literal.pos 2301)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2291), (Sat.Literal.pos 2301)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_2 s)

theorem clause_8179 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291))
    [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_2 s)

theorem clause_8180 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 2291)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2301) (Sat.Literal.pos 2292) (Sat.Literal.pos 231) (Sat.Literal.pos 2291))
    [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 2291)] [(Sat.Literal.neg 2301), (Sat.Literal.pos 2292), (Sat.Literal.pos 2291)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_2 s)

theorem counter_232_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292)) := by
  exact counter_gate s 231 2 (assignment s)
    (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292)
    rfl (rfl) rfl (rfl)

theorem clause_8181 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2293), (Sat.Literal.pos 2302)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292))
    [(Sat.Literal.neg 2293), (Sat.Literal.pos 2302)] [(Sat.Literal.neg 2293), (Sat.Literal.pos 2302)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_3 s)

theorem clause_8182 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2292), (Sat.Literal.pos 2302)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2292), (Sat.Literal.pos 2302)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2292), (Sat.Literal.pos 2302)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_3 s)

theorem clause_8183 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292))
    [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_3 s)

theorem clause_8184 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 2292)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2302) (Sat.Literal.pos 2293) (Sat.Literal.pos 231) (Sat.Literal.pos 2292))
    [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 2292)] [(Sat.Literal.neg 2302), (Sat.Literal.pos 2293), (Sat.Literal.pos 2292)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_3 s)

theorem counter_232_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293)) := by
  exact counter_gate s 231 3 (assignment s)
    (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293)
    rfl (rfl) rfl (rfl)

theorem clause_8185 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2294), (Sat.Literal.pos 2303)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293))
    [(Sat.Literal.neg 2294), (Sat.Literal.pos 2303)] [(Sat.Literal.neg 2294), (Sat.Literal.pos 2303)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_4 s)

theorem clause_8186 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2293), (Sat.Literal.pos 2303)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2293), (Sat.Literal.pos 2303)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2293), (Sat.Literal.pos 2303)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_4 s)

theorem clause_8187 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293))
    [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_4 s)

theorem clause_8188 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 2293)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2303) (Sat.Literal.pos 2294) (Sat.Literal.pos 231) (Sat.Literal.pos 2293))
    [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 2293)] [(Sat.Literal.neg 2303), (Sat.Literal.pos 2294), (Sat.Literal.pos 2293)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_4 s)

theorem counter_232_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294)) := by
  exact counter_gate s 231 4 (assignment s)
    (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294)
    rfl (rfl) rfl (rfl)

theorem clause_8189 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2295), (Sat.Literal.pos 2304)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294))
    [(Sat.Literal.neg 2295), (Sat.Literal.pos 2304)] [(Sat.Literal.neg 2295), (Sat.Literal.pos 2304)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_5 s)

theorem clause_8190 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2294), (Sat.Literal.pos 2304)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2294), (Sat.Literal.pos 2304)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2294), (Sat.Literal.pos 2304)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_5 s)

theorem clause_8191 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294))
    [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_5 s)

theorem clause_8192 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 2294)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2304) (Sat.Literal.pos 2295) (Sat.Literal.pos 231) (Sat.Literal.pos 2294))
    [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 2294)] [(Sat.Literal.neg 2304), (Sat.Literal.pos 2295), (Sat.Literal.pos 2294)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_5 s)

theorem counter_232_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295)) := by
  exact counter_gate s 231 5 (assignment s)
    (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295)
    rfl (rfl) rfl (rfl)

theorem clause_8193 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2296), (Sat.Literal.pos 2305)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295))
    [(Sat.Literal.neg 2296), (Sat.Literal.pos 2305)] [(Sat.Literal.neg 2296), (Sat.Literal.pos 2305)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_6 s)

theorem clause_8194 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2295), (Sat.Literal.pos 2305)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2295), (Sat.Literal.pos 2305)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2295), (Sat.Literal.pos 2305)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_6 s)

theorem clause_8195 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295))
    [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_6 s)

theorem clause_8196 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 2295)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2305) (Sat.Literal.pos 2296) (Sat.Literal.pos 231) (Sat.Literal.pos 2295))
    [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 2295)] [(Sat.Literal.neg 2305), (Sat.Literal.pos 2296), (Sat.Literal.pos 2295)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_6 s)

theorem counter_232_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296)) := by
  exact counter_gate s 231 6 (assignment s)
    (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296)
    rfl (rfl) rfl (rfl)

theorem clause_8197 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2297), (Sat.Literal.pos 2306)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296))
    [(Sat.Literal.neg 2297), (Sat.Literal.pos 2306)] [(Sat.Literal.neg 2297), (Sat.Literal.pos 2306)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_7 s)

theorem clause_8198 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2296), (Sat.Literal.pos 2306)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2296), (Sat.Literal.pos 2306)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2296), (Sat.Literal.pos 2306)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_7 s)

theorem clause_8199 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296))
    [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_7 s)

theorem clause_8200 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 2296)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2306) (Sat.Literal.pos 2297) (Sat.Literal.pos 231) (Sat.Literal.pos 2296))
    [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 2296)] [(Sat.Literal.neg 2306), (Sat.Literal.pos 2297), (Sat.Literal.pos 2296)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_7 s)

theorem counter_232_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297)) := by
  exact counter_gate s 231 7 (assignment s)
    (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297)
    rfl (rfl) rfl (rfl)

theorem clause_8201 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2298), (Sat.Literal.pos 2307)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297))
    [(Sat.Literal.neg 2298), (Sat.Literal.pos 2307)] [(Sat.Literal.neg 2298), (Sat.Literal.pos 2307)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_8 s)

theorem clause_8202 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2297), (Sat.Literal.pos 2307)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2297), (Sat.Literal.pos 2307)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2297), (Sat.Literal.pos 2307)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_8 s)

theorem clause_8203 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297))
    [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_8 s)

theorem clause_8204 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 2297)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2307) (Sat.Literal.pos 2298) (Sat.Literal.pos 231) (Sat.Literal.pos 2297))
    [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 2297)] [(Sat.Literal.neg 2307), (Sat.Literal.pos 2298), (Sat.Literal.pos 2297)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_8 s)

theorem counter_232_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298)) := by
  exact counter_gate s 231 8 (assignment s)
    (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298)
    rfl (rfl) rfl (rfl)

theorem clause_8205 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2299), (Sat.Literal.pos 2308)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298))
    [(Sat.Literal.neg 2299), (Sat.Literal.pos 2308)] [(Sat.Literal.neg 2299), (Sat.Literal.pos 2308)] (List.Mem.head _) (by intro l hl; exact hl) (counter_232_9 s)

theorem clause_8206 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 231), (Sat.Literal.neg 2298), (Sat.Literal.pos 2308)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298))
    [(Sat.Literal.neg 231), (Sat.Literal.neg 2298), (Sat.Literal.pos 2308)] [(Sat.Literal.neg 231), (Sat.Literal.neg 2298), (Sat.Literal.pos 2308)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_232_9 s)

theorem clause_8207 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 231)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298))
    [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 231)] [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 231)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_232_9 s)

theorem clause_8208 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 2298)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2308) (Sat.Literal.pos 2299) (Sat.Literal.pos 231) (Sat.Literal.pos 2298))
    [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 2298)] [(Sat.Literal.neg 2308), (Sat.Literal.pos 2299), (Sat.Literal.pos 2298)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_232_9 s)

theorem counter_233_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256)) := by
  exact counter_gate s 232 0 (assignment s)
    (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 232).symm)

theorem clause_8209 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2300), (Sat.Literal.pos 2309)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2300), (Sat.Literal.pos 2309)] [(Sat.Literal.neg 2300), (Sat.Literal.pos 2309)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_1 s)

theorem clause_8210 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.pos 256), (Sat.Literal.pos 2309)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 232), (Sat.Literal.pos 256), (Sat.Literal.pos 2309)] [(Sat.Literal.neg 232), (Sat.Literal.pos 256), (Sat.Literal.pos 2309)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_1 s)

theorem clause_8211 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_1 s)

theorem clause_8212 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2309) (Sat.Literal.pos 2300) (Sat.Literal.pos 232) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2309), (Sat.Literal.pos 2300), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_1 s)

theorem counter_233_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300)) := by
  exact counter_gate s 232 1 (assignment s)
    (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300)
    rfl (rfl) rfl (rfl)

theorem clause_8213 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2301), (Sat.Literal.pos 2310)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300))
    [(Sat.Literal.neg 2301), (Sat.Literal.pos 2310)] [(Sat.Literal.neg 2301), (Sat.Literal.pos 2310)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_2 s)

theorem clause_8214 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2300), (Sat.Literal.pos 2310)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2300), (Sat.Literal.pos 2310)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2300), (Sat.Literal.pos 2310)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_2 s)

theorem clause_8215 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300))
    [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_2 s)

theorem clause_8216 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 2300)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2310) (Sat.Literal.pos 2301) (Sat.Literal.pos 232) (Sat.Literal.pos 2300))
    [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 2300)] [(Sat.Literal.neg 2310), (Sat.Literal.pos 2301), (Sat.Literal.pos 2300)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_2 s)

theorem counter_233_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301)) := by
  exact counter_gate s 232 2 (assignment s)
    (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301)
    rfl (rfl) rfl (rfl)

theorem clause_8217 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2302), (Sat.Literal.pos 2311)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301))
    [(Sat.Literal.neg 2302), (Sat.Literal.pos 2311)] [(Sat.Literal.neg 2302), (Sat.Literal.pos 2311)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_3 s)

theorem clause_8218 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2301), (Sat.Literal.pos 2311)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2301), (Sat.Literal.pos 2311)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2301), (Sat.Literal.pos 2311)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_3 s)

theorem clause_8219 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301))
    [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_3 s)

theorem clause_8220 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 2301)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2311) (Sat.Literal.pos 2302) (Sat.Literal.pos 232) (Sat.Literal.pos 2301))
    [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 2301)] [(Sat.Literal.neg 2311), (Sat.Literal.pos 2302), (Sat.Literal.pos 2301)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_3 s)

theorem counter_233_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302)) := by
  exact counter_gate s 232 3 (assignment s)
    (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302)
    rfl (rfl) rfl (rfl)

theorem clause_8221 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2303), (Sat.Literal.pos 2312)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302))
    [(Sat.Literal.neg 2303), (Sat.Literal.pos 2312)] [(Sat.Literal.neg 2303), (Sat.Literal.pos 2312)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_4 s)

theorem clause_8222 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2302), (Sat.Literal.pos 2312)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2302), (Sat.Literal.pos 2312)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2302), (Sat.Literal.pos 2312)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_4 s)

theorem clause_8223 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302))
    [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_4 s)

theorem clause_8224 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 2302)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2312) (Sat.Literal.pos 2303) (Sat.Literal.pos 232) (Sat.Literal.pos 2302))
    [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 2302)] [(Sat.Literal.neg 2312), (Sat.Literal.pos 2303), (Sat.Literal.pos 2302)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_4 s)

theorem counter_233_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303)) := by
  exact counter_gate s 232 4 (assignment s)
    (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303)
    rfl (rfl) rfl (rfl)

theorem clause_8225 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2304), (Sat.Literal.pos 2313)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303))
    [(Sat.Literal.neg 2304), (Sat.Literal.pos 2313)] [(Sat.Literal.neg 2304), (Sat.Literal.pos 2313)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_5 s)

theorem clause_8226 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2303), (Sat.Literal.pos 2313)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2303), (Sat.Literal.pos 2313)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2303), (Sat.Literal.pos 2313)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_5 s)

theorem clause_8227 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303))
    [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_5 s)

theorem clause_8228 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 2303)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2313) (Sat.Literal.pos 2304) (Sat.Literal.pos 232) (Sat.Literal.pos 2303))
    [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 2303)] [(Sat.Literal.neg 2313), (Sat.Literal.pos 2304), (Sat.Literal.pos 2303)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_5 s)

theorem counter_233_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304)) := by
  exact counter_gate s 232 5 (assignment s)
    (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304)
    rfl (rfl) rfl (rfl)

theorem clause_8229 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2305), (Sat.Literal.pos 2314)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304))
    [(Sat.Literal.neg 2305), (Sat.Literal.pos 2314)] [(Sat.Literal.neg 2305), (Sat.Literal.pos 2314)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_6 s)

theorem clause_8230 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2304), (Sat.Literal.pos 2314)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2304), (Sat.Literal.pos 2314)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2304), (Sat.Literal.pos 2314)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_6 s)

theorem clause_8231 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304))
    [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_6 s)

theorem clause_8232 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 2304)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2314) (Sat.Literal.pos 2305) (Sat.Literal.pos 232) (Sat.Literal.pos 2304))
    [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 2304)] [(Sat.Literal.neg 2314), (Sat.Literal.pos 2305), (Sat.Literal.pos 2304)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_6 s)

theorem counter_233_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305)) := by
  exact counter_gate s 232 6 (assignment s)
    (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305)
    rfl (rfl) rfl (rfl)

theorem clause_8233 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2306), (Sat.Literal.pos 2315)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305))
    [(Sat.Literal.neg 2306), (Sat.Literal.pos 2315)] [(Sat.Literal.neg 2306), (Sat.Literal.pos 2315)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_7 s)

theorem clause_8234 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2305), (Sat.Literal.pos 2315)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2305), (Sat.Literal.pos 2315)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2305), (Sat.Literal.pos 2315)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_7 s)

theorem clause_8235 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305))
    [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_7 s)

theorem clause_8236 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 2305)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2315) (Sat.Literal.pos 2306) (Sat.Literal.pos 232) (Sat.Literal.pos 2305))
    [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 2305)] [(Sat.Literal.neg 2315), (Sat.Literal.pos 2306), (Sat.Literal.pos 2305)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_7 s)

theorem counter_233_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306)) := by
  exact counter_gate s 232 7 (assignment s)
    (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306)
    rfl (rfl) rfl (rfl)

theorem clause_8237 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2307), (Sat.Literal.pos 2316)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306))
    [(Sat.Literal.neg 2307), (Sat.Literal.pos 2316)] [(Sat.Literal.neg 2307), (Sat.Literal.pos 2316)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_8 s)

theorem clause_8238 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2306), (Sat.Literal.pos 2316)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2306), (Sat.Literal.pos 2316)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2306), (Sat.Literal.pos 2316)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_8 s)

theorem clause_8239 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306))
    [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_8 s)

theorem clause_8240 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 2306)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2316) (Sat.Literal.pos 2307) (Sat.Literal.pos 232) (Sat.Literal.pos 2306))
    [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 2306)] [(Sat.Literal.neg 2316), (Sat.Literal.pos 2307), (Sat.Literal.pos 2306)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_8 s)

theorem counter_233_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307)) := by
  exact counter_gate s 232 8 (assignment s)
    (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307)
    rfl (rfl) rfl (rfl)

theorem clause_8241 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2308), (Sat.Literal.pos 2317)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307))
    [(Sat.Literal.neg 2308), (Sat.Literal.pos 2317)] [(Sat.Literal.neg 2308), (Sat.Literal.pos 2317)] (List.Mem.head _) (by intro l hl; exact hl) (counter_233_9 s)

theorem clause_8242 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 232), (Sat.Literal.neg 2307), (Sat.Literal.pos 2317)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307))
    [(Sat.Literal.neg 232), (Sat.Literal.neg 2307), (Sat.Literal.pos 2317)] [(Sat.Literal.neg 232), (Sat.Literal.neg 2307), (Sat.Literal.pos 2317)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_233_9 s)

theorem clause_8243 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 232)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307))
    [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 232)] [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 232)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_233_9 s)

theorem clause_8244 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 2307)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2317) (Sat.Literal.pos 2308) (Sat.Literal.pos 232) (Sat.Literal.pos 2307))
    [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 2307)] [(Sat.Literal.neg 2317), (Sat.Literal.pos 2308), (Sat.Literal.pos 2307)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_233_9 s)

theorem counter_234_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256)) := by
  exact counter_gate s 233 0 (assignment s)
    (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 233).symm)

theorem clause_8245 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2309), (Sat.Literal.pos 2318)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2309), (Sat.Literal.pos 2318)] [(Sat.Literal.neg 2309), (Sat.Literal.pos 2318)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_1 s)

theorem clause_8246 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.pos 256), (Sat.Literal.pos 2318)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 233), (Sat.Literal.pos 256), (Sat.Literal.pos 2318)] [(Sat.Literal.neg 233), (Sat.Literal.pos 256), (Sat.Literal.pos 2318)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_1 s)

theorem clause_8247 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_1 s)

theorem clause_8248 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2318) (Sat.Literal.pos 2309) (Sat.Literal.pos 233) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2318), (Sat.Literal.pos 2309), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_1 s)

theorem counter_234_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309)) := by
  exact counter_gate s 233 1 (assignment s)
    (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309)
    rfl (rfl) rfl (rfl)

theorem clause_8249 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2310), (Sat.Literal.pos 2319)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309))
    [(Sat.Literal.neg 2310), (Sat.Literal.pos 2319)] [(Sat.Literal.neg 2310), (Sat.Literal.pos 2319)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_2 s)

theorem clause_8250 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2309), (Sat.Literal.pos 2319)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2309), (Sat.Literal.pos 2319)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2309), (Sat.Literal.pos 2319)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_2 s)

theorem clause_8251 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309))
    [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_2 s)

theorem clause_8252 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 2309)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2319) (Sat.Literal.pos 2310) (Sat.Literal.pos 233) (Sat.Literal.pos 2309))
    [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 2309)] [(Sat.Literal.neg 2319), (Sat.Literal.pos 2310), (Sat.Literal.pos 2309)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_2 s)

theorem counter_234_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310)) := by
  exact counter_gate s 233 2 (assignment s)
    (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310)
    rfl (rfl) rfl (rfl)

theorem clause_8253 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2311), (Sat.Literal.pos 2320)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310))
    [(Sat.Literal.neg 2311), (Sat.Literal.pos 2320)] [(Sat.Literal.neg 2311), (Sat.Literal.pos 2320)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_3 s)

theorem clause_8254 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2310), (Sat.Literal.pos 2320)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2310), (Sat.Literal.pos 2320)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2310), (Sat.Literal.pos 2320)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_3 s)

theorem clause_8255 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310))
    [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_3 s)

theorem clause_8256 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 2310)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2320) (Sat.Literal.pos 2311) (Sat.Literal.pos 233) (Sat.Literal.pos 2310))
    [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 2310)] [(Sat.Literal.neg 2320), (Sat.Literal.pos 2311), (Sat.Literal.pos 2310)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_3 s)

theorem counter_234_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311)) := by
  exact counter_gate s 233 3 (assignment s)
    (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311)
    rfl (rfl) rfl (rfl)

theorem clause_8257 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2312), (Sat.Literal.pos 2321)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311))
    [(Sat.Literal.neg 2312), (Sat.Literal.pos 2321)] [(Sat.Literal.neg 2312), (Sat.Literal.pos 2321)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_4 s)

theorem clause_8258 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2311), (Sat.Literal.pos 2321)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2311), (Sat.Literal.pos 2321)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2311), (Sat.Literal.pos 2321)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_4 s)

theorem clause_8259 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311))
    [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_4 s)

theorem clause_8260 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 2311)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2321) (Sat.Literal.pos 2312) (Sat.Literal.pos 233) (Sat.Literal.pos 2311))
    [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 2311)] [(Sat.Literal.neg 2321), (Sat.Literal.pos 2312), (Sat.Literal.pos 2311)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_4 s)

theorem counter_234_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312)) := by
  exact counter_gate s 233 4 (assignment s)
    (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312)
    rfl (rfl) rfl (rfl)

theorem clause_8261 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2313), (Sat.Literal.pos 2322)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312))
    [(Sat.Literal.neg 2313), (Sat.Literal.pos 2322)] [(Sat.Literal.neg 2313), (Sat.Literal.pos 2322)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_5 s)

theorem clause_8262 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2312), (Sat.Literal.pos 2322)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2312), (Sat.Literal.pos 2322)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2312), (Sat.Literal.pos 2322)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_5 s)

theorem clause_8263 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312))
    [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_5 s)

theorem clause_8264 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 2312)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2322) (Sat.Literal.pos 2313) (Sat.Literal.pos 233) (Sat.Literal.pos 2312))
    [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 2312)] [(Sat.Literal.neg 2322), (Sat.Literal.pos 2313), (Sat.Literal.pos 2312)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_5 s)

theorem counter_234_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313)) := by
  exact counter_gate s 233 5 (assignment s)
    (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313)
    rfl (rfl) rfl (rfl)

theorem clause_8265 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2314), (Sat.Literal.pos 2323)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313))
    [(Sat.Literal.neg 2314), (Sat.Literal.pos 2323)] [(Sat.Literal.neg 2314), (Sat.Literal.pos 2323)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_6 s)

theorem clause_8266 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2313), (Sat.Literal.pos 2323)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2313), (Sat.Literal.pos 2323)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2313), (Sat.Literal.pos 2323)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_6 s)

theorem clause_8267 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313))
    [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_6 s)

theorem clause_8268 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 2313)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2323) (Sat.Literal.pos 2314) (Sat.Literal.pos 233) (Sat.Literal.pos 2313))
    [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 2313)] [(Sat.Literal.neg 2323), (Sat.Literal.pos 2314), (Sat.Literal.pos 2313)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_6 s)

theorem counter_234_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314)) := by
  exact counter_gate s 233 6 (assignment s)
    (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314)
    rfl (rfl) rfl (rfl)

theorem clause_8269 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2315), (Sat.Literal.pos 2324)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314))
    [(Sat.Literal.neg 2315), (Sat.Literal.pos 2324)] [(Sat.Literal.neg 2315), (Sat.Literal.pos 2324)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_7 s)

theorem clause_8270 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2314), (Sat.Literal.pos 2324)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2314), (Sat.Literal.pos 2324)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2314), (Sat.Literal.pos 2324)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_7 s)

theorem clause_8271 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314))
    [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_7 s)

theorem clause_8272 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 2314)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2324) (Sat.Literal.pos 2315) (Sat.Literal.pos 233) (Sat.Literal.pos 2314))
    [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 2314)] [(Sat.Literal.neg 2324), (Sat.Literal.pos 2315), (Sat.Literal.pos 2314)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_7 s)

theorem counter_234_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315)) := by
  exact counter_gate s 233 7 (assignment s)
    (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315)
    rfl (rfl) rfl (rfl)

theorem clause_8273 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2316), (Sat.Literal.pos 2325)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315))
    [(Sat.Literal.neg 2316), (Sat.Literal.pos 2325)] [(Sat.Literal.neg 2316), (Sat.Literal.pos 2325)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_8 s)

theorem clause_8274 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2315), (Sat.Literal.pos 2325)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2315), (Sat.Literal.pos 2325)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2315), (Sat.Literal.pos 2325)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_8 s)

theorem clause_8275 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315))
    [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_8 s)

theorem clause_8276 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 2315)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2325) (Sat.Literal.pos 2316) (Sat.Literal.pos 233) (Sat.Literal.pos 2315))
    [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 2315)] [(Sat.Literal.neg 2325), (Sat.Literal.pos 2316), (Sat.Literal.pos 2315)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_8 s)

theorem counter_234_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316)) := by
  exact counter_gate s 233 8 (assignment s)
    (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316)
    rfl (rfl) rfl (rfl)

theorem clause_8277 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2317), (Sat.Literal.pos 2326)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316))
    [(Sat.Literal.neg 2317), (Sat.Literal.pos 2326)] [(Sat.Literal.neg 2317), (Sat.Literal.pos 2326)] (List.Mem.head _) (by intro l hl; exact hl) (counter_234_9 s)

theorem clause_8278 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 233), (Sat.Literal.neg 2316), (Sat.Literal.pos 2326)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316))
    [(Sat.Literal.neg 233), (Sat.Literal.neg 2316), (Sat.Literal.pos 2326)] [(Sat.Literal.neg 233), (Sat.Literal.neg 2316), (Sat.Literal.pos 2326)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_234_9 s)

theorem clause_8279 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 233)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316))
    [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 233)] [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 233)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_234_9 s)

theorem clause_8280 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 2316)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2326) (Sat.Literal.pos 2317) (Sat.Literal.pos 233) (Sat.Literal.pos 2316))
    [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 2316)] [(Sat.Literal.neg 2326), (Sat.Literal.pos 2317), (Sat.Literal.pos 2316)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_234_9 s)

theorem counter_235_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256)) := by
  exact counter_gate s 234 0 (assignment s)
    (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 234).symm)

theorem clause_8281 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2318), (Sat.Literal.pos 2327)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2318), (Sat.Literal.pos 2327)] [(Sat.Literal.neg 2318), (Sat.Literal.pos 2327)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_1 s)

theorem clause_8282 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.pos 256), (Sat.Literal.pos 2327)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 234), (Sat.Literal.pos 256), (Sat.Literal.pos 2327)] [(Sat.Literal.neg 234), (Sat.Literal.pos 256), (Sat.Literal.pos 2327)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_1 s)

theorem clause_8283 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_1 s)

theorem clause_8284 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2327) (Sat.Literal.pos 2318) (Sat.Literal.pos 234) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2327), (Sat.Literal.pos 2318), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_1 s)

theorem counter_235_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318)) := by
  exact counter_gate s 234 1 (assignment s)
    (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318)
    rfl (rfl) rfl (rfl)

theorem clause_8285 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2319), (Sat.Literal.pos 2328)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318))
    [(Sat.Literal.neg 2319), (Sat.Literal.pos 2328)] [(Sat.Literal.neg 2319), (Sat.Literal.pos 2328)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_2 s)

theorem clause_8286 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2318), (Sat.Literal.pos 2328)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2318), (Sat.Literal.pos 2328)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2318), (Sat.Literal.pos 2328)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_2 s)

theorem clause_8287 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318))
    [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_2 s)

theorem clause_8288 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 2318)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2328) (Sat.Literal.pos 2319) (Sat.Literal.pos 234) (Sat.Literal.pos 2318))
    [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 2318)] [(Sat.Literal.neg 2328), (Sat.Literal.pos 2319), (Sat.Literal.pos 2318)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_2 s)

theorem counter_235_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319)) := by
  exact counter_gate s 234 2 (assignment s)
    (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319)
    rfl (rfl) rfl (rfl)

theorem clause_8289 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2320), (Sat.Literal.pos 2329)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319))
    [(Sat.Literal.neg 2320), (Sat.Literal.pos 2329)] [(Sat.Literal.neg 2320), (Sat.Literal.pos 2329)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_3 s)

theorem clause_8290 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2319), (Sat.Literal.pos 2329)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2319), (Sat.Literal.pos 2329)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2319), (Sat.Literal.pos 2329)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_3 s)

theorem clause_8291 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319))
    [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_3 s)

theorem clause_8292 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 2319)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2329) (Sat.Literal.pos 2320) (Sat.Literal.pos 234) (Sat.Literal.pos 2319))
    [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 2319)] [(Sat.Literal.neg 2329), (Sat.Literal.pos 2320), (Sat.Literal.pos 2319)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_3 s)

theorem counter_235_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320)) := by
  exact counter_gate s 234 3 (assignment s)
    (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320)
    rfl (rfl) rfl (rfl)

theorem clause_8293 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2321), (Sat.Literal.pos 2330)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320))
    [(Sat.Literal.neg 2321), (Sat.Literal.pos 2330)] [(Sat.Literal.neg 2321), (Sat.Literal.pos 2330)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_4 s)

theorem clause_8294 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2320), (Sat.Literal.pos 2330)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2320), (Sat.Literal.pos 2330)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2320), (Sat.Literal.pos 2330)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_4 s)

theorem clause_8295 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320))
    [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_4 s)

theorem clause_8296 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 2320)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2330) (Sat.Literal.pos 2321) (Sat.Literal.pos 234) (Sat.Literal.pos 2320))
    [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 2320)] [(Sat.Literal.neg 2330), (Sat.Literal.pos 2321), (Sat.Literal.pos 2320)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_4 s)

theorem counter_235_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321)) := by
  exact counter_gate s 234 4 (assignment s)
    (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321)
    rfl (rfl) rfl (rfl)

theorem clause_8297 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2322), (Sat.Literal.pos 2331)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321))
    [(Sat.Literal.neg 2322), (Sat.Literal.pos 2331)] [(Sat.Literal.neg 2322), (Sat.Literal.pos 2331)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_5 s)

theorem clause_8298 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2321), (Sat.Literal.pos 2331)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2321), (Sat.Literal.pos 2331)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2321), (Sat.Literal.pos 2331)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_5 s)

theorem clause_8299 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321))
    [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_5 s)

theorem clause_8300 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 2321)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2331) (Sat.Literal.pos 2322) (Sat.Literal.pos 234) (Sat.Literal.pos 2321))
    [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 2321)] [(Sat.Literal.neg 2331), (Sat.Literal.pos 2322), (Sat.Literal.pos 2321)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_5 s)

theorem counter_235_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322)) := by
  exact counter_gate s 234 5 (assignment s)
    (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322)
    rfl (rfl) rfl (rfl)

theorem clause_8301 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2323), (Sat.Literal.pos 2332)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322))
    [(Sat.Literal.neg 2323), (Sat.Literal.pos 2332)] [(Sat.Literal.neg 2323), (Sat.Literal.pos 2332)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_6 s)

theorem clause_8302 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2322), (Sat.Literal.pos 2332)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2322), (Sat.Literal.pos 2332)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2322), (Sat.Literal.pos 2332)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_6 s)

theorem clause_8303 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322))
    [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_6 s)

theorem clause_8304 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 2322)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2332) (Sat.Literal.pos 2323) (Sat.Literal.pos 234) (Sat.Literal.pos 2322))
    [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 2322)] [(Sat.Literal.neg 2332), (Sat.Literal.pos 2323), (Sat.Literal.pos 2322)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_6 s)

theorem counter_235_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323)) := by
  exact counter_gate s 234 6 (assignment s)
    (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323)
    rfl (rfl) rfl (rfl)

theorem clause_8305 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2324), (Sat.Literal.pos 2333)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323))
    [(Sat.Literal.neg 2324), (Sat.Literal.pos 2333)] [(Sat.Literal.neg 2324), (Sat.Literal.pos 2333)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_7 s)

theorem clause_8306 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2323), (Sat.Literal.pos 2333)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2323), (Sat.Literal.pos 2333)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2323), (Sat.Literal.pos 2333)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_7 s)

theorem clause_8307 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323))
    [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_7 s)

theorem clause_8308 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 2323)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2333) (Sat.Literal.pos 2324) (Sat.Literal.pos 234) (Sat.Literal.pos 2323))
    [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 2323)] [(Sat.Literal.neg 2333), (Sat.Literal.pos 2324), (Sat.Literal.pos 2323)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_7 s)

theorem counter_235_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324)) := by
  exact counter_gate s 234 7 (assignment s)
    (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324)
    rfl (rfl) rfl (rfl)

theorem clause_8309 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2325), (Sat.Literal.pos 2334)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324))
    [(Sat.Literal.neg 2325), (Sat.Literal.pos 2334)] [(Sat.Literal.neg 2325), (Sat.Literal.pos 2334)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_8 s)

theorem clause_8310 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2324), (Sat.Literal.pos 2334)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2324), (Sat.Literal.pos 2334)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2324), (Sat.Literal.pos 2334)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_8 s)

theorem clause_8311 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324))
    [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_8 s)

theorem clause_8312 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 2324)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2334) (Sat.Literal.pos 2325) (Sat.Literal.pos 234) (Sat.Literal.pos 2324))
    [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 2324)] [(Sat.Literal.neg 2334), (Sat.Literal.pos 2325), (Sat.Literal.pos 2324)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_8 s)

theorem counter_235_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325)) := by
  exact counter_gate s 234 8 (assignment s)
    (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325)
    rfl (rfl) rfl (rfl)

theorem clause_8313 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2326), (Sat.Literal.pos 2335)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325))
    [(Sat.Literal.neg 2326), (Sat.Literal.pos 2335)] [(Sat.Literal.neg 2326), (Sat.Literal.pos 2335)] (List.Mem.head _) (by intro l hl; exact hl) (counter_235_9 s)

theorem clause_8314 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 234), (Sat.Literal.neg 2325), (Sat.Literal.pos 2335)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325))
    [(Sat.Literal.neg 234), (Sat.Literal.neg 2325), (Sat.Literal.pos 2335)] [(Sat.Literal.neg 234), (Sat.Literal.neg 2325), (Sat.Literal.pos 2335)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_235_9 s)

theorem clause_8315 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 234)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325))
    [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 234)] [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 234)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_235_9 s)

theorem clause_8316 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 2325)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2335) (Sat.Literal.pos 2326) (Sat.Literal.pos 234) (Sat.Literal.pos 2325))
    [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 2325)] [(Sat.Literal.neg 2335), (Sat.Literal.pos 2326), (Sat.Literal.pos 2325)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_235_9 s)

theorem counter_236_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256)) := by
  exact counter_gate s 235 0 (assignment s)
    (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 235).symm)

theorem clause_8317 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2327), (Sat.Literal.pos 2336)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2327), (Sat.Literal.pos 2336)] [(Sat.Literal.neg 2327), (Sat.Literal.pos 2336)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_1 s)

theorem clause_8318 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.pos 256), (Sat.Literal.pos 2336)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 235), (Sat.Literal.pos 256), (Sat.Literal.pos 2336)] [(Sat.Literal.neg 235), (Sat.Literal.pos 256), (Sat.Literal.pos 2336)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_1 s)

theorem clause_8319 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_1 s)

theorem clause_8320 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2336) (Sat.Literal.pos 2327) (Sat.Literal.pos 235) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2336), (Sat.Literal.pos 2327), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_1 s)

theorem counter_236_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327)) := by
  exact counter_gate s 235 1 (assignment s)
    (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327)
    rfl (rfl) rfl (rfl)

theorem clause_8321 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2328), (Sat.Literal.pos 2337)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327))
    [(Sat.Literal.neg 2328), (Sat.Literal.pos 2337)] [(Sat.Literal.neg 2328), (Sat.Literal.pos 2337)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_2 s)

theorem clause_8322 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2327), (Sat.Literal.pos 2337)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2327), (Sat.Literal.pos 2337)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2327), (Sat.Literal.pos 2337)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_2 s)

theorem clause_8323 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327))
    [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_2 s)

theorem clause_8324 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 2327)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2337) (Sat.Literal.pos 2328) (Sat.Literal.pos 235) (Sat.Literal.pos 2327))
    [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 2327)] [(Sat.Literal.neg 2337), (Sat.Literal.pos 2328), (Sat.Literal.pos 2327)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_2 s)

theorem counter_236_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328)) := by
  exact counter_gate s 235 2 (assignment s)
    (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328)
    rfl (rfl) rfl (rfl)

theorem clause_8325 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2329), (Sat.Literal.pos 2338)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328))
    [(Sat.Literal.neg 2329), (Sat.Literal.pos 2338)] [(Sat.Literal.neg 2329), (Sat.Literal.pos 2338)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_3 s)

theorem clause_8326 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2328), (Sat.Literal.pos 2338)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2328), (Sat.Literal.pos 2338)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2328), (Sat.Literal.pos 2338)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_3 s)

theorem clause_8327 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328))
    [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_3 s)

theorem clause_8328 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 2328)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2338) (Sat.Literal.pos 2329) (Sat.Literal.pos 235) (Sat.Literal.pos 2328))
    [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 2328)] [(Sat.Literal.neg 2338), (Sat.Literal.pos 2329), (Sat.Literal.pos 2328)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_3 s)

theorem counter_236_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329)) := by
  exact counter_gate s 235 3 (assignment s)
    (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329)
    rfl (rfl) rfl (rfl)

theorem clause_8329 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2330), (Sat.Literal.pos 2339)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329))
    [(Sat.Literal.neg 2330), (Sat.Literal.pos 2339)] [(Sat.Literal.neg 2330), (Sat.Literal.pos 2339)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_4 s)

theorem clause_8330 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2329), (Sat.Literal.pos 2339)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2329), (Sat.Literal.pos 2339)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2329), (Sat.Literal.pos 2339)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_4 s)

theorem clause_8331 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329))
    [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_4 s)

theorem clause_8332 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 2329)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2339) (Sat.Literal.pos 2330) (Sat.Literal.pos 235) (Sat.Literal.pos 2329))
    [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 2329)] [(Sat.Literal.neg 2339), (Sat.Literal.pos 2330), (Sat.Literal.pos 2329)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_4 s)

theorem counter_236_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330)) := by
  exact counter_gate s 235 4 (assignment s)
    (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330)
    rfl (rfl) rfl (rfl)

theorem clause_8333 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2331), (Sat.Literal.pos 2340)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330))
    [(Sat.Literal.neg 2331), (Sat.Literal.pos 2340)] [(Sat.Literal.neg 2331), (Sat.Literal.pos 2340)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_5 s)

theorem clause_8334 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2330), (Sat.Literal.pos 2340)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2330), (Sat.Literal.pos 2340)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2330), (Sat.Literal.pos 2340)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_5 s)

theorem clause_8335 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330))
    [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_5 s)

theorem clause_8336 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 2330)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2340) (Sat.Literal.pos 2331) (Sat.Literal.pos 235) (Sat.Literal.pos 2330))
    [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 2330)] [(Sat.Literal.neg 2340), (Sat.Literal.pos 2331), (Sat.Literal.pos 2330)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_5 s)

theorem counter_236_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331)) := by
  exact counter_gate s 235 5 (assignment s)
    (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331)
    rfl (rfl) rfl (rfl)

theorem clause_8337 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2332), (Sat.Literal.pos 2341)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331))
    [(Sat.Literal.neg 2332), (Sat.Literal.pos 2341)] [(Sat.Literal.neg 2332), (Sat.Literal.pos 2341)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_6 s)

theorem clause_8338 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2331), (Sat.Literal.pos 2341)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2331), (Sat.Literal.pos 2341)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2331), (Sat.Literal.pos 2341)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_6 s)

theorem clause_8339 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331))
    [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_6 s)

theorem clause_8340 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 2331)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2341) (Sat.Literal.pos 2332) (Sat.Literal.pos 235) (Sat.Literal.pos 2331))
    [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 2331)] [(Sat.Literal.neg 2341), (Sat.Literal.pos 2332), (Sat.Literal.pos 2331)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_6 s)

theorem counter_236_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332)) := by
  exact counter_gate s 235 6 (assignment s)
    (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332)
    rfl (rfl) rfl (rfl)

theorem clause_8341 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2333), (Sat.Literal.pos 2342)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332))
    [(Sat.Literal.neg 2333), (Sat.Literal.pos 2342)] [(Sat.Literal.neg 2333), (Sat.Literal.pos 2342)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_7 s)

theorem clause_8342 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2332), (Sat.Literal.pos 2342)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2332), (Sat.Literal.pos 2342)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2332), (Sat.Literal.pos 2342)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_7 s)

theorem clause_8343 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332))
    [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_7 s)

theorem clause_8344 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 2332)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2342) (Sat.Literal.pos 2333) (Sat.Literal.pos 235) (Sat.Literal.pos 2332))
    [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 2332)] [(Sat.Literal.neg 2342), (Sat.Literal.pos 2333), (Sat.Literal.pos 2332)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_7 s)

theorem counter_236_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333)) := by
  exact counter_gate s 235 7 (assignment s)
    (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333)
    rfl (rfl) rfl (rfl)

theorem clause_8345 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2334), (Sat.Literal.pos 2343)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333))
    [(Sat.Literal.neg 2334), (Sat.Literal.pos 2343)] [(Sat.Literal.neg 2334), (Sat.Literal.pos 2343)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_8 s)

theorem clause_8346 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2333), (Sat.Literal.pos 2343)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2333), (Sat.Literal.pos 2343)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2333), (Sat.Literal.pos 2343)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_8 s)

theorem clause_8347 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333))
    [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_8 s)

theorem clause_8348 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 2333)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2343) (Sat.Literal.pos 2334) (Sat.Literal.pos 235) (Sat.Literal.pos 2333))
    [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 2333)] [(Sat.Literal.neg 2343), (Sat.Literal.pos 2334), (Sat.Literal.pos 2333)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_8 s)

theorem counter_236_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334)) := by
  exact counter_gate s 235 8 (assignment s)
    (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334)
    rfl (rfl) rfl (rfl)

theorem clause_8349 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2335), (Sat.Literal.pos 2344)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334))
    [(Sat.Literal.neg 2335), (Sat.Literal.pos 2344)] [(Sat.Literal.neg 2335), (Sat.Literal.pos 2344)] (List.Mem.head _) (by intro l hl; exact hl) (counter_236_9 s)

theorem clause_8350 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 235), (Sat.Literal.neg 2334), (Sat.Literal.pos 2344)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334))
    [(Sat.Literal.neg 235), (Sat.Literal.neg 2334), (Sat.Literal.pos 2344)] [(Sat.Literal.neg 235), (Sat.Literal.neg 2334), (Sat.Literal.pos 2344)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_236_9 s)

theorem clause_8351 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 235)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334))
    [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 235)] [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 235)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_236_9 s)

theorem clause_8352 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 2334)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2344) (Sat.Literal.pos 2335) (Sat.Literal.pos 235) (Sat.Literal.pos 2334))
    [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 2334)] [(Sat.Literal.neg 2344), (Sat.Literal.pos 2335), (Sat.Literal.pos 2334)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_236_9 s)

theorem counter_237_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256)) := by
  exact counter_gate s 236 0 (assignment s)
    (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 236).symm)

theorem clause_8353 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2336), (Sat.Literal.pos 2345)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2336), (Sat.Literal.pos 2345)] [(Sat.Literal.neg 2336), (Sat.Literal.pos 2345)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_1 s)

theorem clause_8354 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.pos 256), (Sat.Literal.pos 2345)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 236), (Sat.Literal.pos 256), (Sat.Literal.pos 2345)] [(Sat.Literal.neg 236), (Sat.Literal.pos 256), (Sat.Literal.pos 2345)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_1 s)

theorem clause_8355 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_1 s)

theorem clause_8356 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2345) (Sat.Literal.pos 2336) (Sat.Literal.pos 236) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2345), (Sat.Literal.pos 2336), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_1 s)

theorem counter_237_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336)) := by
  exact counter_gate s 236 1 (assignment s)
    (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336)
    rfl (rfl) rfl (rfl)

theorem clause_8357 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2337), (Sat.Literal.pos 2346)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336))
    [(Sat.Literal.neg 2337), (Sat.Literal.pos 2346)] [(Sat.Literal.neg 2337), (Sat.Literal.pos 2346)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_2 s)

theorem clause_8358 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2336), (Sat.Literal.pos 2346)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2336), (Sat.Literal.pos 2346)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2336), (Sat.Literal.pos 2346)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_2 s)

theorem clause_8359 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336))
    [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_2 s)

theorem clause_8360 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 2336)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2346) (Sat.Literal.pos 2337) (Sat.Literal.pos 236) (Sat.Literal.pos 2336))
    [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 2336)] [(Sat.Literal.neg 2346), (Sat.Literal.pos 2337), (Sat.Literal.pos 2336)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_2 s)

theorem counter_237_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337)) := by
  exact counter_gate s 236 2 (assignment s)
    (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337)
    rfl (rfl) rfl (rfl)

theorem clause_8361 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2338), (Sat.Literal.pos 2347)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337))
    [(Sat.Literal.neg 2338), (Sat.Literal.pos 2347)] [(Sat.Literal.neg 2338), (Sat.Literal.pos 2347)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_3 s)

theorem clause_8362 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2337), (Sat.Literal.pos 2347)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2337), (Sat.Literal.pos 2347)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2337), (Sat.Literal.pos 2347)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_3 s)

theorem clause_8363 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337))
    [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_3 s)

theorem clause_8364 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 2337)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2347) (Sat.Literal.pos 2338) (Sat.Literal.pos 236) (Sat.Literal.pos 2337))
    [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 2337)] [(Sat.Literal.neg 2347), (Sat.Literal.pos 2338), (Sat.Literal.pos 2337)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_3 s)

theorem counter_237_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338)) := by
  exact counter_gate s 236 3 (assignment s)
    (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338)
    rfl (rfl) rfl (rfl)

theorem clause_8365 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2339), (Sat.Literal.pos 2348)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338))
    [(Sat.Literal.neg 2339), (Sat.Literal.pos 2348)] [(Sat.Literal.neg 2339), (Sat.Literal.pos 2348)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_4 s)

theorem clause_8366 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2338), (Sat.Literal.pos 2348)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2338), (Sat.Literal.pos 2348)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2338), (Sat.Literal.pos 2348)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_4 s)

theorem clause_8367 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338))
    [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_4 s)

theorem clause_8368 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 2338)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2348) (Sat.Literal.pos 2339) (Sat.Literal.pos 236) (Sat.Literal.pos 2338))
    [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 2338)] [(Sat.Literal.neg 2348), (Sat.Literal.pos 2339), (Sat.Literal.pos 2338)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_4 s)

theorem counter_237_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339)) := by
  exact counter_gate s 236 4 (assignment s)
    (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339)
    rfl (rfl) rfl (rfl)

theorem clause_8369 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2340), (Sat.Literal.pos 2349)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339))
    [(Sat.Literal.neg 2340), (Sat.Literal.pos 2349)] [(Sat.Literal.neg 2340), (Sat.Literal.pos 2349)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_5 s)

theorem clause_8370 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2339), (Sat.Literal.pos 2349)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2339), (Sat.Literal.pos 2349)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2339), (Sat.Literal.pos 2349)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_5 s)

theorem clause_8371 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339))
    [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_5 s)

theorem clause_8372 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 2339)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2349) (Sat.Literal.pos 2340) (Sat.Literal.pos 236) (Sat.Literal.pos 2339))
    [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 2339)] [(Sat.Literal.neg 2349), (Sat.Literal.pos 2340), (Sat.Literal.pos 2339)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_5 s)

theorem counter_237_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340)) := by
  exact counter_gate s 236 5 (assignment s)
    (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340)
    rfl (rfl) rfl (rfl)

theorem clause_8373 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2341), (Sat.Literal.pos 2350)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340))
    [(Sat.Literal.neg 2341), (Sat.Literal.pos 2350)] [(Sat.Literal.neg 2341), (Sat.Literal.pos 2350)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_6 s)

theorem clause_8374 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2340), (Sat.Literal.pos 2350)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2340), (Sat.Literal.pos 2350)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2340), (Sat.Literal.pos 2350)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_6 s)

theorem clause_8375 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340))
    [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_6 s)

theorem clause_8376 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 2340)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2350) (Sat.Literal.pos 2341) (Sat.Literal.pos 236) (Sat.Literal.pos 2340))
    [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 2340)] [(Sat.Literal.neg 2350), (Sat.Literal.pos 2341), (Sat.Literal.pos 2340)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_6 s)

theorem counter_237_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341)) := by
  exact counter_gate s 236 6 (assignment s)
    (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341)
    rfl (rfl) rfl (rfl)

theorem clause_8377 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2342), (Sat.Literal.pos 2351)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341))
    [(Sat.Literal.neg 2342), (Sat.Literal.pos 2351)] [(Sat.Literal.neg 2342), (Sat.Literal.pos 2351)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_7 s)

theorem clause_8378 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2341), (Sat.Literal.pos 2351)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2341), (Sat.Literal.pos 2351)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2341), (Sat.Literal.pos 2351)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_7 s)

theorem clause_8379 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341))
    [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_7 s)

theorem clause_8380 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 2341)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2351) (Sat.Literal.pos 2342) (Sat.Literal.pos 236) (Sat.Literal.pos 2341))
    [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 2341)] [(Sat.Literal.neg 2351), (Sat.Literal.pos 2342), (Sat.Literal.pos 2341)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_7 s)

theorem counter_237_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342)) := by
  exact counter_gate s 236 7 (assignment s)
    (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342)
    rfl (rfl) rfl (rfl)

theorem clause_8381 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2343), (Sat.Literal.pos 2352)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342))
    [(Sat.Literal.neg 2343), (Sat.Literal.pos 2352)] [(Sat.Literal.neg 2343), (Sat.Literal.pos 2352)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_8 s)

theorem clause_8382 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2342), (Sat.Literal.pos 2352)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2342), (Sat.Literal.pos 2352)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2342), (Sat.Literal.pos 2352)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_8 s)

theorem clause_8383 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342))
    [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_8 s)

theorem clause_8384 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 2342)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2352) (Sat.Literal.pos 2343) (Sat.Literal.pos 236) (Sat.Literal.pos 2342))
    [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 2342)] [(Sat.Literal.neg 2352), (Sat.Literal.pos 2343), (Sat.Literal.pos 2342)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_8 s)

theorem counter_237_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343)) := by
  exact counter_gate s 236 8 (assignment s)
    (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343)
    rfl (rfl) rfl (rfl)

theorem clause_8385 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2344), (Sat.Literal.pos 2353)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343))
    [(Sat.Literal.neg 2344), (Sat.Literal.pos 2353)] [(Sat.Literal.neg 2344), (Sat.Literal.pos 2353)] (List.Mem.head _) (by intro l hl; exact hl) (counter_237_9 s)

theorem clause_8386 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 236), (Sat.Literal.neg 2343), (Sat.Literal.pos 2353)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343))
    [(Sat.Literal.neg 236), (Sat.Literal.neg 2343), (Sat.Literal.pos 2353)] [(Sat.Literal.neg 236), (Sat.Literal.neg 2343), (Sat.Literal.pos 2353)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_237_9 s)

theorem clause_8387 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 236)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343))
    [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 236)] [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 236)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_237_9 s)

theorem clause_8388 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 2343)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2353) (Sat.Literal.pos 2344) (Sat.Literal.pos 236) (Sat.Literal.pos 2343))
    [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 2343)] [(Sat.Literal.neg 2353), (Sat.Literal.pos 2344), (Sat.Literal.pos 2343)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_237_9 s)

theorem counter_238_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256)) := by
  exact counter_gate s 237 0 (assignment s)
    (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 237).symm)

theorem clause_8389 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2345), (Sat.Literal.pos 2354)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2345), (Sat.Literal.pos 2354)] [(Sat.Literal.neg 2345), (Sat.Literal.pos 2354)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_1 s)

theorem clause_8390 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.pos 256), (Sat.Literal.pos 2354)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 237), (Sat.Literal.pos 256), (Sat.Literal.pos 2354)] [(Sat.Literal.neg 237), (Sat.Literal.pos 256), (Sat.Literal.pos 2354)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_1 s)

theorem clause_8391 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_1 s)

theorem clause_8392 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2354) (Sat.Literal.pos 2345) (Sat.Literal.pos 237) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2354), (Sat.Literal.pos 2345), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_1 s)

theorem counter_238_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345)) := by
  exact counter_gate s 237 1 (assignment s)
    (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345)
    rfl (rfl) rfl (rfl)

theorem clause_8393 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2346), (Sat.Literal.pos 2355)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345))
    [(Sat.Literal.neg 2346), (Sat.Literal.pos 2355)] [(Sat.Literal.neg 2346), (Sat.Literal.pos 2355)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_2 s)

theorem clause_8394 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2345), (Sat.Literal.pos 2355)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2345), (Sat.Literal.pos 2355)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2345), (Sat.Literal.pos 2355)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_2 s)

theorem clause_8395 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345))
    [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_2 s)

theorem clause_8396 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 2345)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2355) (Sat.Literal.pos 2346) (Sat.Literal.pos 237) (Sat.Literal.pos 2345))
    [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 2345)] [(Sat.Literal.neg 2355), (Sat.Literal.pos 2346), (Sat.Literal.pos 2345)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_2 s)

theorem counter_238_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346)) := by
  exact counter_gate s 237 2 (assignment s)
    (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346)
    rfl (rfl) rfl (rfl)

theorem clause_8397 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2347), (Sat.Literal.pos 2356)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346))
    [(Sat.Literal.neg 2347), (Sat.Literal.pos 2356)] [(Sat.Literal.neg 2347), (Sat.Literal.pos 2356)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_3 s)

theorem clause_8398 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2346), (Sat.Literal.pos 2356)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2346), (Sat.Literal.pos 2356)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2346), (Sat.Literal.pos 2356)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_3 s)

theorem clause_8399 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346))
    [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_3 s)

theorem clause_8400 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 2346)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2356) (Sat.Literal.pos 2347) (Sat.Literal.pos 237) (Sat.Literal.pos 2346))
    [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 2346)] [(Sat.Literal.neg 2356), (Sat.Literal.pos 2347), (Sat.Literal.pos 2346)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_3 s)

theorem counter_238_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347)) := by
  exact counter_gate s 237 3 (assignment s)
    (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347)
    rfl (rfl) rfl (rfl)

theorem clause_8401 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2348), (Sat.Literal.pos 2357)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347))
    [(Sat.Literal.neg 2348), (Sat.Literal.pos 2357)] [(Sat.Literal.neg 2348), (Sat.Literal.pos 2357)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_4 s)

theorem clause_8402 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2347), (Sat.Literal.pos 2357)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2347), (Sat.Literal.pos 2357)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2347), (Sat.Literal.pos 2357)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_4 s)

theorem clause_8403 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347))
    [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_4 s)

theorem clause_8404 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 2347)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2357) (Sat.Literal.pos 2348) (Sat.Literal.pos 237) (Sat.Literal.pos 2347))
    [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 2347)] [(Sat.Literal.neg 2357), (Sat.Literal.pos 2348), (Sat.Literal.pos 2347)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_4 s)

theorem counter_238_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348)) := by
  exact counter_gate s 237 4 (assignment s)
    (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348)
    rfl (rfl) rfl (rfl)

theorem clause_8405 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2349), (Sat.Literal.pos 2358)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348))
    [(Sat.Literal.neg 2349), (Sat.Literal.pos 2358)] [(Sat.Literal.neg 2349), (Sat.Literal.pos 2358)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_5 s)

theorem clause_8406 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2348), (Sat.Literal.pos 2358)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2348), (Sat.Literal.pos 2358)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2348), (Sat.Literal.pos 2358)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_5 s)

theorem clause_8407 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348))
    [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_5 s)

theorem clause_8408 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 2348)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2358) (Sat.Literal.pos 2349) (Sat.Literal.pos 237) (Sat.Literal.pos 2348))
    [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 2348)] [(Sat.Literal.neg 2358), (Sat.Literal.pos 2349), (Sat.Literal.pos 2348)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_5 s)

theorem counter_238_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349)) := by
  exact counter_gate s 237 5 (assignment s)
    (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349)
    rfl (rfl) rfl (rfl)

theorem clause_8409 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2350), (Sat.Literal.pos 2359)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349))
    [(Sat.Literal.neg 2350), (Sat.Literal.pos 2359)] [(Sat.Literal.neg 2350), (Sat.Literal.pos 2359)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_6 s)

theorem clause_8410 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2349), (Sat.Literal.pos 2359)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2349), (Sat.Literal.pos 2359)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2349), (Sat.Literal.pos 2359)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_6 s)

theorem clause_8411 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349))
    [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_6 s)

theorem clause_8412 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 2349)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2359) (Sat.Literal.pos 2350) (Sat.Literal.pos 237) (Sat.Literal.pos 2349))
    [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 2349)] [(Sat.Literal.neg 2359), (Sat.Literal.pos 2350), (Sat.Literal.pos 2349)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_6 s)

theorem counter_238_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350)) := by
  exact counter_gate s 237 6 (assignment s)
    (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350)
    rfl (rfl) rfl (rfl)

theorem clause_8413 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2351), (Sat.Literal.pos 2360)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350))
    [(Sat.Literal.neg 2351), (Sat.Literal.pos 2360)] [(Sat.Literal.neg 2351), (Sat.Literal.pos 2360)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_7 s)

theorem clause_8414 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2350), (Sat.Literal.pos 2360)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2350), (Sat.Literal.pos 2360)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2350), (Sat.Literal.pos 2360)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_7 s)

theorem clause_8415 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350))
    [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_7 s)

theorem clause_8416 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 2350)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2360) (Sat.Literal.pos 2351) (Sat.Literal.pos 237) (Sat.Literal.pos 2350))
    [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 2350)] [(Sat.Literal.neg 2360), (Sat.Literal.pos 2351), (Sat.Literal.pos 2350)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_7 s)

theorem counter_238_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351)) := by
  exact counter_gate s 237 7 (assignment s)
    (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351)
    rfl (rfl) rfl (rfl)

theorem clause_8417 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2352), (Sat.Literal.pos 2361)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351))
    [(Sat.Literal.neg 2352), (Sat.Literal.pos 2361)] [(Sat.Literal.neg 2352), (Sat.Literal.pos 2361)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_8 s)

theorem clause_8418 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2351), (Sat.Literal.pos 2361)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2351), (Sat.Literal.pos 2361)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2351), (Sat.Literal.pos 2361)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_8 s)

theorem clause_8419 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351))
    [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_8 s)

theorem clause_8420 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 2351)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2361) (Sat.Literal.pos 2352) (Sat.Literal.pos 237) (Sat.Literal.pos 2351))
    [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 2351)] [(Sat.Literal.neg 2361), (Sat.Literal.pos 2352), (Sat.Literal.pos 2351)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_8 s)

theorem counter_238_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352)) := by
  exact counter_gate s 237 8 (assignment s)
    (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352)
    rfl (rfl) rfl (rfl)

theorem clause_8421 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2353), (Sat.Literal.pos 2362)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352))
    [(Sat.Literal.neg 2353), (Sat.Literal.pos 2362)] [(Sat.Literal.neg 2353), (Sat.Literal.pos 2362)] (List.Mem.head _) (by intro l hl; exact hl) (counter_238_9 s)

theorem clause_8422 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 237), (Sat.Literal.neg 2352), (Sat.Literal.pos 2362)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352))
    [(Sat.Literal.neg 237), (Sat.Literal.neg 2352), (Sat.Literal.pos 2362)] [(Sat.Literal.neg 237), (Sat.Literal.neg 2352), (Sat.Literal.pos 2362)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_238_9 s)

theorem clause_8423 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 237)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352))
    [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 237)] [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 237)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_238_9 s)

theorem clause_8424 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 2352)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2362) (Sat.Literal.pos 2353) (Sat.Literal.pos 237) (Sat.Literal.pos 2352))
    [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 2352)] [(Sat.Literal.neg 2362), (Sat.Literal.pos 2353), (Sat.Literal.pos 2352)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_238_9 s)

theorem counter_239_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256)) := by
  exact counter_gate s 238 0 (assignment s)
    (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 238).symm)

theorem clause_8425 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2354), (Sat.Literal.pos 2363)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2354), (Sat.Literal.pos 2363)] [(Sat.Literal.neg 2354), (Sat.Literal.pos 2363)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_1 s)

theorem clause_8426 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.pos 256), (Sat.Literal.pos 2363)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 238), (Sat.Literal.pos 256), (Sat.Literal.pos 2363)] [(Sat.Literal.neg 238), (Sat.Literal.pos 256), (Sat.Literal.pos 2363)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_1 s)

theorem clause_8427 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_1 s)

theorem clause_8428 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2363) (Sat.Literal.pos 2354) (Sat.Literal.pos 238) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2363), (Sat.Literal.pos 2354), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_1 s)

theorem counter_239_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354)) := by
  exact counter_gate s 238 1 (assignment s)
    (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354)
    rfl (rfl) rfl (rfl)

theorem clause_8429 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2355), (Sat.Literal.pos 2364)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354))
    [(Sat.Literal.neg 2355), (Sat.Literal.pos 2364)] [(Sat.Literal.neg 2355), (Sat.Literal.pos 2364)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_2 s)

theorem clause_8430 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2354), (Sat.Literal.pos 2364)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2354), (Sat.Literal.pos 2364)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2354), (Sat.Literal.pos 2364)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_2 s)

theorem clause_8431 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354))
    [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_2 s)

theorem clause_8432 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 2354)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2364) (Sat.Literal.pos 2355) (Sat.Literal.pos 238) (Sat.Literal.pos 2354))
    [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 2354)] [(Sat.Literal.neg 2364), (Sat.Literal.pos 2355), (Sat.Literal.pos 2354)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_2 s)

theorem counter_239_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355)) := by
  exact counter_gate s 238 2 (assignment s)
    (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355)
    rfl (rfl) rfl (rfl)

theorem clause_8433 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2356), (Sat.Literal.pos 2365)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355))
    [(Sat.Literal.neg 2356), (Sat.Literal.pos 2365)] [(Sat.Literal.neg 2356), (Sat.Literal.pos 2365)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_3 s)

theorem clause_8434 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2355), (Sat.Literal.pos 2365)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2355), (Sat.Literal.pos 2365)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2355), (Sat.Literal.pos 2365)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_3 s)

theorem clause_8435 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355))
    [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_3 s)

theorem clause_8436 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 2355)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2365) (Sat.Literal.pos 2356) (Sat.Literal.pos 238) (Sat.Literal.pos 2355))
    [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 2355)] [(Sat.Literal.neg 2365), (Sat.Literal.pos 2356), (Sat.Literal.pos 2355)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_3 s)

theorem counter_239_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356)) := by
  exact counter_gate s 238 3 (assignment s)
    (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356)
    rfl (rfl) rfl (rfl)

theorem clause_8437 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2357), (Sat.Literal.pos 2366)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356))
    [(Sat.Literal.neg 2357), (Sat.Literal.pos 2366)] [(Sat.Literal.neg 2357), (Sat.Literal.pos 2366)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_4 s)

theorem clause_8438 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2356), (Sat.Literal.pos 2366)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2356), (Sat.Literal.pos 2366)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2356), (Sat.Literal.pos 2366)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_4 s)

theorem clause_8439 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356))
    [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_4 s)

theorem clause_8440 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 2356)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2366) (Sat.Literal.pos 2357) (Sat.Literal.pos 238) (Sat.Literal.pos 2356))
    [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 2356)] [(Sat.Literal.neg 2366), (Sat.Literal.pos 2357), (Sat.Literal.pos 2356)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_4 s)

theorem counter_239_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357)) := by
  exact counter_gate s 238 4 (assignment s)
    (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357)
    rfl (rfl) rfl (rfl)

theorem clause_8441 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2358), (Sat.Literal.pos 2367)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357))
    [(Sat.Literal.neg 2358), (Sat.Literal.pos 2367)] [(Sat.Literal.neg 2358), (Sat.Literal.pos 2367)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_5 s)

theorem clause_8442 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2357), (Sat.Literal.pos 2367)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2357), (Sat.Literal.pos 2367)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2357), (Sat.Literal.pos 2367)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_5 s)

theorem clause_8443 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357))
    [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_5 s)

theorem clause_8444 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 2357)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2367) (Sat.Literal.pos 2358) (Sat.Literal.pos 238) (Sat.Literal.pos 2357))
    [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 2357)] [(Sat.Literal.neg 2367), (Sat.Literal.pos 2358), (Sat.Literal.pos 2357)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_5 s)

theorem counter_239_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358)) := by
  exact counter_gate s 238 5 (assignment s)
    (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358)
    rfl (rfl) rfl (rfl)

theorem clause_8445 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2359), (Sat.Literal.pos 2368)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358))
    [(Sat.Literal.neg 2359), (Sat.Literal.pos 2368)] [(Sat.Literal.neg 2359), (Sat.Literal.pos 2368)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_6 s)

theorem clause_8446 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2358), (Sat.Literal.pos 2368)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2358), (Sat.Literal.pos 2368)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2358), (Sat.Literal.pos 2368)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_6 s)

theorem clause_8447 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358))
    [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_6 s)

theorem clause_8448 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 2358)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2368) (Sat.Literal.pos 2359) (Sat.Literal.pos 238) (Sat.Literal.pos 2358))
    [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 2358)] [(Sat.Literal.neg 2368), (Sat.Literal.pos 2359), (Sat.Literal.pos 2358)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_6 s)

theorem counter_239_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359)) := by
  exact counter_gate s 238 6 (assignment s)
    (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359)
    rfl (rfl) rfl (rfl)

theorem clause_8449 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2360), (Sat.Literal.pos 2369)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359))
    [(Sat.Literal.neg 2360), (Sat.Literal.pos 2369)] [(Sat.Literal.neg 2360), (Sat.Literal.pos 2369)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_7 s)

theorem clause_8450 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2359), (Sat.Literal.pos 2369)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2359), (Sat.Literal.pos 2369)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2359), (Sat.Literal.pos 2369)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_7 s)

theorem clause_8451 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359))
    [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_7 s)

theorem clause_8452 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 2359)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2369) (Sat.Literal.pos 2360) (Sat.Literal.pos 238) (Sat.Literal.pos 2359))
    [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 2359)] [(Sat.Literal.neg 2369), (Sat.Literal.pos 2360), (Sat.Literal.pos 2359)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_7 s)

theorem counter_239_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360)) := by
  exact counter_gate s 238 7 (assignment s)
    (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360)
    rfl (rfl) rfl (rfl)

theorem clause_8453 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2361), (Sat.Literal.pos 2370)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360))
    [(Sat.Literal.neg 2361), (Sat.Literal.pos 2370)] [(Sat.Literal.neg 2361), (Sat.Literal.pos 2370)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_8 s)

theorem clause_8454 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2360), (Sat.Literal.pos 2370)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2360), (Sat.Literal.pos 2370)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2360), (Sat.Literal.pos 2370)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_8 s)

theorem clause_8455 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360))
    [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_8 s)

theorem clause_8456 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 2360)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2370) (Sat.Literal.pos 2361) (Sat.Literal.pos 238) (Sat.Literal.pos 2360))
    [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 2360)] [(Sat.Literal.neg 2370), (Sat.Literal.pos 2361), (Sat.Literal.pos 2360)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_8 s)

theorem counter_239_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361)) := by
  exact counter_gate s 238 8 (assignment s)
    (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361)
    rfl (rfl) rfl (rfl)

theorem clause_8457 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2362), (Sat.Literal.pos 2371)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361))
    [(Sat.Literal.neg 2362), (Sat.Literal.pos 2371)] [(Sat.Literal.neg 2362), (Sat.Literal.pos 2371)] (List.Mem.head _) (by intro l hl; exact hl) (counter_239_9 s)

theorem clause_8458 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 238), (Sat.Literal.neg 2361), (Sat.Literal.pos 2371)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361))
    [(Sat.Literal.neg 238), (Sat.Literal.neg 2361), (Sat.Literal.pos 2371)] [(Sat.Literal.neg 238), (Sat.Literal.neg 2361), (Sat.Literal.pos 2371)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_239_9 s)

theorem clause_8459 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 238)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361))
    [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 238)] [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 238)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_239_9 s)

theorem clause_8460 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 2361)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2371) (Sat.Literal.pos 2362) (Sat.Literal.pos 238) (Sat.Literal.pos 2361))
    [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 2361)] [(Sat.Literal.neg 2371), (Sat.Literal.pos 2362), (Sat.Literal.pos 2361)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_239_9 s)

theorem counter_240_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256)) := by
  exact counter_gate s 239 0 (assignment s)
    (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 239).symm)

theorem clause_8461 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2363), (Sat.Literal.pos 2372)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2363), (Sat.Literal.pos 2372)] [(Sat.Literal.neg 2363), (Sat.Literal.pos 2372)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_1 s)

theorem clause_8462 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.pos 256), (Sat.Literal.pos 2372)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 239), (Sat.Literal.pos 256), (Sat.Literal.pos 2372)] [(Sat.Literal.neg 239), (Sat.Literal.pos 256), (Sat.Literal.pos 2372)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_1 s)

theorem clause_8463 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_1 s)

theorem clause_8464 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2372) (Sat.Literal.pos 2363) (Sat.Literal.pos 239) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2372), (Sat.Literal.pos 2363), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_1 s)

theorem counter_240_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363)) := by
  exact counter_gate s 239 1 (assignment s)
    (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363)
    rfl (rfl) rfl (rfl)

theorem clause_8465 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2364), (Sat.Literal.pos 2373)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363))
    [(Sat.Literal.neg 2364), (Sat.Literal.pos 2373)] [(Sat.Literal.neg 2364), (Sat.Literal.pos 2373)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_2 s)

theorem clause_8466 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2363), (Sat.Literal.pos 2373)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2363), (Sat.Literal.pos 2373)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2363), (Sat.Literal.pos 2373)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_2 s)

theorem clause_8467 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363))
    [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_2 s)

theorem clause_8468 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 2363)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2373) (Sat.Literal.pos 2364) (Sat.Literal.pos 239) (Sat.Literal.pos 2363))
    [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 2363)] [(Sat.Literal.neg 2373), (Sat.Literal.pos 2364), (Sat.Literal.pos 2363)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_2 s)

theorem counter_240_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364)) := by
  exact counter_gate s 239 2 (assignment s)
    (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364)
    rfl (rfl) rfl (rfl)

theorem clause_8469 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2365), (Sat.Literal.pos 2374)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364))
    [(Sat.Literal.neg 2365), (Sat.Literal.pos 2374)] [(Sat.Literal.neg 2365), (Sat.Literal.pos 2374)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_3 s)

theorem clause_8470 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2364), (Sat.Literal.pos 2374)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2364), (Sat.Literal.pos 2374)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2364), (Sat.Literal.pos 2374)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_3 s)

theorem clause_8471 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364))
    [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_3 s)

theorem clause_8472 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 2364)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2374) (Sat.Literal.pos 2365) (Sat.Literal.pos 239) (Sat.Literal.pos 2364))
    [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 2364)] [(Sat.Literal.neg 2374), (Sat.Literal.pos 2365), (Sat.Literal.pos 2364)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_3 s)

theorem counter_240_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365)) := by
  exact counter_gate s 239 3 (assignment s)
    (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365)
    rfl (rfl) rfl (rfl)

theorem clause_8473 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2366), (Sat.Literal.pos 2375)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365))
    [(Sat.Literal.neg 2366), (Sat.Literal.pos 2375)] [(Sat.Literal.neg 2366), (Sat.Literal.pos 2375)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_4 s)

theorem clause_8474 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2365), (Sat.Literal.pos 2375)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2365), (Sat.Literal.pos 2375)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2365), (Sat.Literal.pos 2375)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_4 s)

theorem clause_8475 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365))
    [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_4 s)

theorem clause_8476 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 2365)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2375) (Sat.Literal.pos 2366) (Sat.Literal.pos 239) (Sat.Literal.pos 2365))
    [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 2365)] [(Sat.Literal.neg 2375), (Sat.Literal.pos 2366), (Sat.Literal.pos 2365)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_4 s)

theorem counter_240_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366)) := by
  exact counter_gate s 239 4 (assignment s)
    (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366)
    rfl (rfl) rfl (rfl)

theorem clause_8477 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2367), (Sat.Literal.pos 2376)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366))
    [(Sat.Literal.neg 2367), (Sat.Literal.pos 2376)] [(Sat.Literal.neg 2367), (Sat.Literal.pos 2376)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_5 s)

theorem clause_8478 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2366), (Sat.Literal.pos 2376)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2366), (Sat.Literal.pos 2376)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2366), (Sat.Literal.pos 2376)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_5 s)

theorem clause_8479 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366))
    [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_5 s)

theorem clause_8480 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 2366)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2376) (Sat.Literal.pos 2367) (Sat.Literal.pos 239) (Sat.Literal.pos 2366))
    [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 2366)] [(Sat.Literal.neg 2376), (Sat.Literal.pos 2367), (Sat.Literal.pos 2366)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_5 s)

theorem counter_240_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367)) := by
  exact counter_gate s 239 5 (assignment s)
    (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367)
    rfl (rfl) rfl (rfl)

theorem clause_8481 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2368), (Sat.Literal.pos 2377)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367))
    [(Sat.Literal.neg 2368), (Sat.Literal.pos 2377)] [(Sat.Literal.neg 2368), (Sat.Literal.pos 2377)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_6 s)

theorem clause_8482 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2367), (Sat.Literal.pos 2377)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2367), (Sat.Literal.pos 2377)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2367), (Sat.Literal.pos 2377)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_6 s)

theorem clause_8483 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367))
    [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_6 s)

theorem clause_8484 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 2367)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2377) (Sat.Literal.pos 2368) (Sat.Literal.pos 239) (Sat.Literal.pos 2367))
    [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 2367)] [(Sat.Literal.neg 2377), (Sat.Literal.pos 2368), (Sat.Literal.pos 2367)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_6 s)

theorem counter_240_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368)) := by
  exact counter_gate s 239 6 (assignment s)
    (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368)
    rfl (rfl) rfl (rfl)

theorem clause_8485 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2369), (Sat.Literal.pos 2378)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368))
    [(Sat.Literal.neg 2369), (Sat.Literal.pos 2378)] [(Sat.Literal.neg 2369), (Sat.Literal.pos 2378)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_7 s)

theorem clause_8486 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2368), (Sat.Literal.pos 2378)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2368), (Sat.Literal.pos 2378)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2368), (Sat.Literal.pos 2378)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_7 s)

theorem clause_8487 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368))
    [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_7 s)

theorem clause_8488 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 2368)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2378) (Sat.Literal.pos 2369) (Sat.Literal.pos 239) (Sat.Literal.pos 2368))
    [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 2368)] [(Sat.Literal.neg 2378), (Sat.Literal.pos 2369), (Sat.Literal.pos 2368)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_7 s)

theorem counter_240_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369)) := by
  exact counter_gate s 239 7 (assignment s)
    (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369)
    rfl (rfl) rfl (rfl)

theorem clause_8489 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2370), (Sat.Literal.pos 2379)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369))
    [(Sat.Literal.neg 2370), (Sat.Literal.pos 2379)] [(Sat.Literal.neg 2370), (Sat.Literal.pos 2379)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_8 s)

theorem clause_8490 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2369), (Sat.Literal.pos 2379)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2369), (Sat.Literal.pos 2379)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2369), (Sat.Literal.pos 2379)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_8 s)

theorem clause_8491 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369))
    [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_8 s)

theorem clause_8492 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 2369)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2379) (Sat.Literal.pos 2370) (Sat.Literal.pos 239) (Sat.Literal.pos 2369))
    [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 2369)] [(Sat.Literal.neg 2379), (Sat.Literal.pos 2370), (Sat.Literal.pos 2369)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_8 s)

theorem counter_240_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370)) := by
  exact counter_gate s 239 8 (assignment s)
    (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370)
    rfl (rfl) rfl (rfl)

theorem clause_8493 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2371), (Sat.Literal.pos 2380)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370))
    [(Sat.Literal.neg 2371), (Sat.Literal.pos 2380)] [(Sat.Literal.neg 2371), (Sat.Literal.pos 2380)] (List.Mem.head _) (by intro l hl; exact hl) (counter_240_9 s)

theorem clause_8494 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 239), (Sat.Literal.neg 2370), (Sat.Literal.pos 2380)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370))
    [(Sat.Literal.neg 239), (Sat.Literal.neg 2370), (Sat.Literal.pos 2380)] [(Sat.Literal.neg 239), (Sat.Literal.neg 2370), (Sat.Literal.pos 2380)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_240_9 s)

theorem clause_8495 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 239)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370))
    [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 239)] [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 239)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_240_9 s)

theorem clause_8496 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 2370)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2380) (Sat.Literal.pos 2371) (Sat.Literal.pos 239) (Sat.Literal.pos 2370))
    [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 2370)] [(Sat.Literal.neg 2380), (Sat.Literal.pos 2371), (Sat.Literal.pos 2370)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_240_9 s)

theorem counter_241_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256)) := by
  exact counter_gate s 240 0 (assignment s)
    (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 240).symm)

theorem clause_8497 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2372), (Sat.Literal.pos 2381)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2372), (Sat.Literal.pos 2381)] [(Sat.Literal.neg 2372), (Sat.Literal.pos 2381)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_1 s)

theorem clause_8498 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.pos 256), (Sat.Literal.pos 2381)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 240), (Sat.Literal.pos 256), (Sat.Literal.pos 2381)] [(Sat.Literal.neg 240), (Sat.Literal.pos 256), (Sat.Literal.pos 2381)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_1 s)

theorem clause_8499 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_1 s)

theorem clause_8500 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2381) (Sat.Literal.pos 2372) (Sat.Literal.pos 240) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2381), (Sat.Literal.pos 2372), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_1 s)

theorem counter_241_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372)) := by
  exact counter_gate s 240 1 (assignment s)
    (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372)
    rfl (rfl) rfl (rfl)

theorem clause_8501 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2373), (Sat.Literal.pos 2382)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372))
    [(Sat.Literal.neg 2373), (Sat.Literal.pos 2382)] [(Sat.Literal.neg 2373), (Sat.Literal.pos 2382)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_2 s)

theorem clause_8502 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2372), (Sat.Literal.pos 2382)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2372), (Sat.Literal.pos 2382)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2372), (Sat.Literal.pos 2382)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_2 s)

theorem clause_8503 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372))
    [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_2 s)

theorem clause_8504 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 2372)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2382) (Sat.Literal.pos 2373) (Sat.Literal.pos 240) (Sat.Literal.pos 2372))
    [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 2372)] [(Sat.Literal.neg 2382), (Sat.Literal.pos 2373), (Sat.Literal.pos 2372)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_2 s)

theorem counter_241_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373)) := by
  exact counter_gate s 240 2 (assignment s)
    (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373)
    rfl (rfl) rfl (rfl)

theorem clause_8505 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2374), (Sat.Literal.pos 2383)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373))
    [(Sat.Literal.neg 2374), (Sat.Literal.pos 2383)] [(Sat.Literal.neg 2374), (Sat.Literal.pos 2383)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_3 s)

theorem clause_8506 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2373), (Sat.Literal.pos 2383)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2373), (Sat.Literal.pos 2383)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2373), (Sat.Literal.pos 2383)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_3 s)

theorem clause_8507 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373))
    [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_3 s)

theorem clause_8508 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 2373)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2383) (Sat.Literal.pos 2374) (Sat.Literal.pos 240) (Sat.Literal.pos 2373))
    [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 2373)] [(Sat.Literal.neg 2383), (Sat.Literal.pos 2374), (Sat.Literal.pos 2373)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_3 s)

theorem counter_241_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374)) := by
  exact counter_gate s 240 3 (assignment s)
    (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374)
    rfl (rfl) rfl (rfl)

theorem clause_8509 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2375), (Sat.Literal.pos 2384)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374))
    [(Sat.Literal.neg 2375), (Sat.Literal.pos 2384)] [(Sat.Literal.neg 2375), (Sat.Literal.pos 2384)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_4 s)

theorem clause_8510 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2374), (Sat.Literal.pos 2384)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2374), (Sat.Literal.pos 2384)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2374), (Sat.Literal.pos 2384)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_4 s)

theorem clause_8511 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374))
    [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_4 s)

theorem clause_8512 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 2374)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2384) (Sat.Literal.pos 2375) (Sat.Literal.pos 240) (Sat.Literal.pos 2374))
    [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 2374)] [(Sat.Literal.neg 2384), (Sat.Literal.pos 2375), (Sat.Literal.pos 2374)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_4 s)

theorem counter_241_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375)) := by
  exact counter_gate s 240 4 (assignment s)
    (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375)
    rfl (rfl) rfl (rfl)

theorem clause_8513 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2376), (Sat.Literal.pos 2385)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375))
    [(Sat.Literal.neg 2376), (Sat.Literal.pos 2385)] [(Sat.Literal.neg 2376), (Sat.Literal.pos 2385)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_5 s)

theorem clause_8514 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2375), (Sat.Literal.pos 2385)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2375), (Sat.Literal.pos 2385)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2375), (Sat.Literal.pos 2385)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_5 s)

theorem clause_8515 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375))
    [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_5 s)

theorem clause_8516 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 2375)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2385) (Sat.Literal.pos 2376) (Sat.Literal.pos 240) (Sat.Literal.pos 2375))
    [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 2375)] [(Sat.Literal.neg 2385), (Sat.Literal.pos 2376), (Sat.Literal.pos 2375)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_5 s)

theorem counter_241_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376)) := by
  exact counter_gate s 240 5 (assignment s)
    (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376)
    rfl (rfl) rfl (rfl)

theorem clause_8517 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2377), (Sat.Literal.pos 2386)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376))
    [(Sat.Literal.neg 2377), (Sat.Literal.pos 2386)] [(Sat.Literal.neg 2377), (Sat.Literal.pos 2386)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_6 s)

theorem clause_8518 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2376), (Sat.Literal.pos 2386)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2376), (Sat.Literal.pos 2386)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2376), (Sat.Literal.pos 2386)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_6 s)

theorem clause_8519 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376))
    [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_6 s)

theorem clause_8520 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 2376)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2386) (Sat.Literal.pos 2377) (Sat.Literal.pos 240) (Sat.Literal.pos 2376))
    [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 2376)] [(Sat.Literal.neg 2386), (Sat.Literal.pos 2377), (Sat.Literal.pos 2376)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_6 s)

theorem counter_241_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377)) := by
  exact counter_gate s 240 6 (assignment s)
    (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377)
    rfl (rfl) rfl (rfl)

theorem clause_8521 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2378), (Sat.Literal.pos 2387)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377))
    [(Sat.Literal.neg 2378), (Sat.Literal.pos 2387)] [(Sat.Literal.neg 2378), (Sat.Literal.pos 2387)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_7 s)

theorem clause_8522 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2377), (Sat.Literal.pos 2387)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2377), (Sat.Literal.pos 2387)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2377), (Sat.Literal.pos 2387)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_7 s)

theorem clause_8523 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377))
    [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_7 s)

theorem clause_8524 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 2377)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2387) (Sat.Literal.pos 2378) (Sat.Literal.pos 240) (Sat.Literal.pos 2377))
    [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 2377)] [(Sat.Literal.neg 2387), (Sat.Literal.pos 2378), (Sat.Literal.pos 2377)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_7 s)

theorem counter_241_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378)) := by
  exact counter_gate s 240 7 (assignment s)
    (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378)
    rfl (rfl) rfl (rfl)

theorem clause_8525 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2379), (Sat.Literal.pos 2388)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378))
    [(Sat.Literal.neg 2379), (Sat.Literal.pos 2388)] [(Sat.Literal.neg 2379), (Sat.Literal.pos 2388)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_8 s)

theorem clause_8526 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2378), (Sat.Literal.pos 2388)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2378), (Sat.Literal.pos 2388)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2378), (Sat.Literal.pos 2388)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_8 s)

theorem clause_8527 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378))
    [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_8 s)

theorem clause_8528 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 2378)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2388) (Sat.Literal.pos 2379) (Sat.Literal.pos 240) (Sat.Literal.pos 2378))
    [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 2378)] [(Sat.Literal.neg 2388), (Sat.Literal.pos 2379), (Sat.Literal.pos 2378)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_8 s)

theorem counter_241_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379)) := by
  exact counter_gate s 240 8 (assignment s)
    (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379)
    rfl (rfl) rfl (rfl)

theorem clause_8529 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2380), (Sat.Literal.pos 2389)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379))
    [(Sat.Literal.neg 2380), (Sat.Literal.pos 2389)] [(Sat.Literal.neg 2380), (Sat.Literal.pos 2389)] (List.Mem.head _) (by intro l hl; exact hl) (counter_241_9 s)

theorem clause_8530 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 240), (Sat.Literal.neg 2379), (Sat.Literal.pos 2389)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379))
    [(Sat.Literal.neg 240), (Sat.Literal.neg 2379), (Sat.Literal.pos 2389)] [(Sat.Literal.neg 240), (Sat.Literal.neg 2379), (Sat.Literal.pos 2389)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_241_9 s)

theorem clause_8531 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 240)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379))
    [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 240)] [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 240)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_241_9 s)

theorem clause_8532 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 2379)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2389) (Sat.Literal.pos 2380) (Sat.Literal.pos 240) (Sat.Literal.pos 2379))
    [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 2379)] [(Sat.Literal.neg 2389), (Sat.Literal.pos 2380), (Sat.Literal.pos 2379)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_241_9 s)

theorem counter_242_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256)) := by
  exact counter_gate s 241 0 (assignment s)
    (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 241).symm)

theorem clause_8533 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2381), (Sat.Literal.pos 2390)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2381), (Sat.Literal.pos 2390)] [(Sat.Literal.neg 2381), (Sat.Literal.pos 2390)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_1 s)

theorem clause_8534 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.pos 256), (Sat.Literal.pos 2390)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 241), (Sat.Literal.pos 256), (Sat.Literal.pos 2390)] [(Sat.Literal.neg 241), (Sat.Literal.pos 256), (Sat.Literal.pos 2390)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_1 s)

theorem clause_8535 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_1 s)

theorem clause_8536 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2390) (Sat.Literal.pos 2381) (Sat.Literal.pos 241) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2390), (Sat.Literal.pos 2381), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_1 s)

theorem counter_242_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381)) := by
  exact counter_gate s 241 1 (assignment s)
    (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381)
    rfl (rfl) rfl (rfl)

theorem clause_8537 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2382), (Sat.Literal.pos 2391)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381))
    [(Sat.Literal.neg 2382), (Sat.Literal.pos 2391)] [(Sat.Literal.neg 2382), (Sat.Literal.pos 2391)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_2 s)

theorem clause_8538 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2381), (Sat.Literal.pos 2391)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2381), (Sat.Literal.pos 2391)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2381), (Sat.Literal.pos 2391)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_2 s)

theorem clause_8539 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381))
    [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_2 s)

theorem clause_8540 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 2381)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2391) (Sat.Literal.pos 2382) (Sat.Literal.pos 241) (Sat.Literal.pos 2381))
    [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 2381)] [(Sat.Literal.neg 2391), (Sat.Literal.pos 2382), (Sat.Literal.pos 2381)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_2 s)

theorem counter_242_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382)) := by
  exact counter_gate s 241 2 (assignment s)
    (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382)
    rfl (rfl) rfl (rfl)

theorem clause_8541 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2383), (Sat.Literal.pos 2392)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382))
    [(Sat.Literal.neg 2383), (Sat.Literal.pos 2392)] [(Sat.Literal.neg 2383), (Sat.Literal.pos 2392)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_3 s)

theorem clause_8542 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2382), (Sat.Literal.pos 2392)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2382), (Sat.Literal.pos 2392)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2382), (Sat.Literal.pos 2392)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_3 s)

theorem clause_8543 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382))
    [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_3 s)

theorem clause_8544 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 2382)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2392) (Sat.Literal.pos 2383) (Sat.Literal.pos 241) (Sat.Literal.pos 2382))
    [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 2382)] [(Sat.Literal.neg 2392), (Sat.Literal.pos 2383), (Sat.Literal.pos 2382)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_3 s)

theorem counter_242_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383)) := by
  exact counter_gate s 241 3 (assignment s)
    (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383)
    rfl (rfl) rfl (rfl)

theorem clause_8545 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2384), (Sat.Literal.pos 2393)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383))
    [(Sat.Literal.neg 2384), (Sat.Literal.pos 2393)] [(Sat.Literal.neg 2384), (Sat.Literal.pos 2393)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_4 s)

theorem clause_8546 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2383), (Sat.Literal.pos 2393)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2383), (Sat.Literal.pos 2393)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2383), (Sat.Literal.pos 2393)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_4 s)

theorem clause_8547 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383))
    [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_4 s)

theorem clause_8548 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 2383)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2393) (Sat.Literal.pos 2384) (Sat.Literal.pos 241) (Sat.Literal.pos 2383))
    [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 2383)] [(Sat.Literal.neg 2393), (Sat.Literal.pos 2384), (Sat.Literal.pos 2383)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_4 s)

theorem counter_242_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384)) := by
  exact counter_gate s 241 4 (assignment s)
    (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384)
    rfl (rfl) rfl (rfl)

theorem clause_8549 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2385), (Sat.Literal.pos 2394)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384))
    [(Sat.Literal.neg 2385), (Sat.Literal.pos 2394)] [(Sat.Literal.neg 2385), (Sat.Literal.pos 2394)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_5 s)

theorem clause_8550 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2384), (Sat.Literal.pos 2394)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2384), (Sat.Literal.pos 2394)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2384), (Sat.Literal.pos 2394)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_5 s)

theorem clause_8551 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384))
    [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_5 s)

theorem clause_8552 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 2384)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2394) (Sat.Literal.pos 2385) (Sat.Literal.pos 241) (Sat.Literal.pos 2384))
    [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 2384)] [(Sat.Literal.neg 2394), (Sat.Literal.pos 2385), (Sat.Literal.pos 2384)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_5 s)

theorem counter_242_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385)) := by
  exact counter_gate s 241 5 (assignment s)
    (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385)
    rfl (rfl) rfl (rfl)

theorem clause_8553 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2386), (Sat.Literal.pos 2395)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385))
    [(Sat.Literal.neg 2386), (Sat.Literal.pos 2395)] [(Sat.Literal.neg 2386), (Sat.Literal.pos 2395)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_6 s)

theorem clause_8554 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2385), (Sat.Literal.pos 2395)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2385), (Sat.Literal.pos 2395)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2385), (Sat.Literal.pos 2395)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_6 s)

theorem clause_8555 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385))
    [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_6 s)

theorem clause_8556 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 2385)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2395) (Sat.Literal.pos 2386) (Sat.Literal.pos 241) (Sat.Literal.pos 2385))
    [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 2385)] [(Sat.Literal.neg 2395), (Sat.Literal.pos 2386), (Sat.Literal.pos 2385)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_6 s)

theorem counter_242_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386)) := by
  exact counter_gate s 241 6 (assignment s)
    (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386)
    rfl (rfl) rfl (rfl)

theorem clause_8557 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2387), (Sat.Literal.pos 2396)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386))
    [(Sat.Literal.neg 2387), (Sat.Literal.pos 2396)] [(Sat.Literal.neg 2387), (Sat.Literal.pos 2396)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_7 s)

theorem clause_8558 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2386), (Sat.Literal.pos 2396)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2386), (Sat.Literal.pos 2396)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2386), (Sat.Literal.pos 2396)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_7 s)

theorem clause_8559 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386))
    [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_7 s)

theorem clause_8560 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 2386)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2396) (Sat.Literal.pos 2387) (Sat.Literal.pos 241) (Sat.Literal.pos 2386))
    [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 2386)] [(Sat.Literal.neg 2396), (Sat.Literal.pos 2387), (Sat.Literal.pos 2386)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_7 s)

theorem counter_242_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387)) := by
  exact counter_gate s 241 7 (assignment s)
    (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387)
    rfl (rfl) rfl (rfl)

theorem clause_8561 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2388), (Sat.Literal.pos 2397)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387))
    [(Sat.Literal.neg 2388), (Sat.Literal.pos 2397)] [(Sat.Literal.neg 2388), (Sat.Literal.pos 2397)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_8 s)

theorem clause_8562 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2387), (Sat.Literal.pos 2397)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2387), (Sat.Literal.pos 2397)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2387), (Sat.Literal.pos 2397)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_8 s)

theorem clause_8563 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387))
    [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_8 s)

theorem clause_8564 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 2387)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2397) (Sat.Literal.pos 2388) (Sat.Literal.pos 241) (Sat.Literal.pos 2387))
    [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 2387)] [(Sat.Literal.neg 2397), (Sat.Literal.pos 2388), (Sat.Literal.pos 2387)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_8 s)

theorem counter_242_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388)) := by
  exact counter_gate s 241 8 (assignment s)
    (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388)
    rfl (rfl) rfl (rfl)

theorem clause_8565 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2389), (Sat.Literal.pos 2398)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388))
    [(Sat.Literal.neg 2389), (Sat.Literal.pos 2398)] [(Sat.Literal.neg 2389), (Sat.Literal.pos 2398)] (List.Mem.head _) (by intro l hl; exact hl) (counter_242_9 s)

theorem clause_8566 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 241), (Sat.Literal.neg 2388), (Sat.Literal.pos 2398)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388))
    [(Sat.Literal.neg 241), (Sat.Literal.neg 2388), (Sat.Literal.pos 2398)] [(Sat.Literal.neg 241), (Sat.Literal.neg 2388), (Sat.Literal.pos 2398)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_242_9 s)

theorem clause_8567 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 241)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388))
    [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 241)] [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 241)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_242_9 s)

theorem clause_8568 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 2388)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2398) (Sat.Literal.pos 2389) (Sat.Literal.pos 241) (Sat.Literal.pos 2388))
    [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 2388)] [(Sat.Literal.neg 2398), (Sat.Literal.pos 2389), (Sat.Literal.pos 2388)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_242_9 s)

theorem counter_243_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256)) := by
  exact counter_gate s 242 0 (assignment s)
    (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 242).symm)

theorem clause_8569 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2390), (Sat.Literal.pos 2399)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2390), (Sat.Literal.pos 2399)] [(Sat.Literal.neg 2390), (Sat.Literal.pos 2399)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_1 s)

theorem clause_8570 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.pos 256), (Sat.Literal.pos 2399)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 242), (Sat.Literal.pos 256), (Sat.Literal.pos 2399)] [(Sat.Literal.neg 242), (Sat.Literal.pos 256), (Sat.Literal.pos 2399)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_1 s)

theorem clause_8571 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_1 s)

theorem clause_8572 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2399) (Sat.Literal.pos 2390) (Sat.Literal.pos 242) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2399), (Sat.Literal.pos 2390), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_1 s)

theorem counter_243_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390)) := by
  exact counter_gate s 242 1 (assignment s)
    (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390)
    rfl (rfl) rfl (rfl)

theorem clause_8573 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2391), (Sat.Literal.pos 2400)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390))
    [(Sat.Literal.neg 2391), (Sat.Literal.pos 2400)] [(Sat.Literal.neg 2391), (Sat.Literal.pos 2400)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_2 s)

theorem clause_8574 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2390), (Sat.Literal.pos 2400)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2390), (Sat.Literal.pos 2400)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2390), (Sat.Literal.pos 2400)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_2 s)

theorem clause_8575 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390))
    [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_2 s)

theorem clause_8576 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 2390)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2400) (Sat.Literal.pos 2391) (Sat.Literal.pos 242) (Sat.Literal.pos 2390))
    [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 2390)] [(Sat.Literal.neg 2400), (Sat.Literal.pos 2391), (Sat.Literal.pos 2390)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_2 s)

theorem counter_243_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391)) := by
  exact counter_gate s 242 2 (assignment s)
    (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391)
    rfl (rfl) rfl (rfl)

theorem clause_8577 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2392), (Sat.Literal.pos 2401)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391))
    [(Sat.Literal.neg 2392), (Sat.Literal.pos 2401)] [(Sat.Literal.neg 2392), (Sat.Literal.pos 2401)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_3 s)

theorem clause_8578 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2391), (Sat.Literal.pos 2401)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2391), (Sat.Literal.pos 2401)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2391), (Sat.Literal.pos 2401)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_3 s)

theorem clause_8579 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391))
    [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_3 s)

theorem clause_8580 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 2391)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2401) (Sat.Literal.pos 2392) (Sat.Literal.pos 242) (Sat.Literal.pos 2391))
    [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 2391)] [(Sat.Literal.neg 2401), (Sat.Literal.pos 2392), (Sat.Literal.pos 2391)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_3 s)

theorem counter_243_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392)) := by
  exact counter_gate s 242 3 (assignment s)
    (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392)
    rfl (rfl) rfl (rfl)

theorem clause_8581 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2393), (Sat.Literal.pos 2402)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392))
    [(Sat.Literal.neg 2393), (Sat.Literal.pos 2402)] [(Sat.Literal.neg 2393), (Sat.Literal.pos 2402)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_4 s)

theorem clause_8582 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2392), (Sat.Literal.pos 2402)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2392), (Sat.Literal.pos 2402)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2392), (Sat.Literal.pos 2402)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_4 s)

theorem clause_8583 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392))
    [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_4 s)

theorem clause_8584 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 2392)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2402) (Sat.Literal.pos 2393) (Sat.Literal.pos 242) (Sat.Literal.pos 2392))
    [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 2392)] [(Sat.Literal.neg 2402), (Sat.Literal.pos 2393), (Sat.Literal.pos 2392)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_4 s)

theorem counter_243_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393)) := by
  exact counter_gate s 242 4 (assignment s)
    (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393)
    rfl (rfl) rfl (rfl)

theorem clause_8585 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2394), (Sat.Literal.pos 2403)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393))
    [(Sat.Literal.neg 2394), (Sat.Literal.pos 2403)] [(Sat.Literal.neg 2394), (Sat.Literal.pos 2403)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_5 s)

theorem clause_8586 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2393), (Sat.Literal.pos 2403)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2393), (Sat.Literal.pos 2403)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2393), (Sat.Literal.pos 2403)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_5 s)

theorem clause_8587 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393))
    [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_5 s)

theorem clause_8588 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 2393)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2403) (Sat.Literal.pos 2394) (Sat.Literal.pos 242) (Sat.Literal.pos 2393))
    [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 2393)] [(Sat.Literal.neg 2403), (Sat.Literal.pos 2394), (Sat.Literal.pos 2393)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_5 s)

theorem counter_243_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394)) := by
  exact counter_gate s 242 5 (assignment s)
    (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394)
    rfl (rfl) rfl (rfl)

theorem clause_8589 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2395), (Sat.Literal.pos 2404)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394))
    [(Sat.Literal.neg 2395), (Sat.Literal.pos 2404)] [(Sat.Literal.neg 2395), (Sat.Literal.pos 2404)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_6 s)

theorem clause_8590 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2394), (Sat.Literal.pos 2404)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2394), (Sat.Literal.pos 2404)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2394), (Sat.Literal.pos 2404)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_6 s)

theorem clause_8591 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394))
    [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_6 s)

theorem clause_8592 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 2394)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2404) (Sat.Literal.pos 2395) (Sat.Literal.pos 242) (Sat.Literal.pos 2394))
    [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 2394)] [(Sat.Literal.neg 2404), (Sat.Literal.pos 2395), (Sat.Literal.pos 2394)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_6 s)

theorem counter_243_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395)) := by
  exact counter_gate s 242 6 (assignment s)
    (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395)
    rfl (rfl) rfl (rfl)

theorem clause_8593 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2396), (Sat.Literal.pos 2405)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395))
    [(Sat.Literal.neg 2396), (Sat.Literal.pos 2405)] [(Sat.Literal.neg 2396), (Sat.Literal.pos 2405)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_7 s)

theorem clause_8594 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2395), (Sat.Literal.pos 2405)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2395), (Sat.Literal.pos 2405)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2395), (Sat.Literal.pos 2405)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_7 s)

theorem clause_8595 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395))
    [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_7 s)

theorem clause_8596 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 2395)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2405) (Sat.Literal.pos 2396) (Sat.Literal.pos 242) (Sat.Literal.pos 2395))
    [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 2395)] [(Sat.Literal.neg 2405), (Sat.Literal.pos 2396), (Sat.Literal.pos 2395)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_7 s)

theorem counter_243_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396)) := by
  exact counter_gate s 242 7 (assignment s)
    (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396)
    rfl (rfl) rfl (rfl)

theorem clause_8597 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2397), (Sat.Literal.pos 2406)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396))
    [(Sat.Literal.neg 2397), (Sat.Literal.pos 2406)] [(Sat.Literal.neg 2397), (Sat.Literal.pos 2406)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_8 s)

theorem clause_8598 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2396), (Sat.Literal.pos 2406)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2396), (Sat.Literal.pos 2406)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2396), (Sat.Literal.pos 2406)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_8 s)

theorem clause_8599 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396))
    [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_8 s)

theorem clause_8600 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 2396)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2406) (Sat.Literal.pos 2397) (Sat.Literal.pos 242) (Sat.Literal.pos 2396))
    [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 2396)] [(Sat.Literal.neg 2406), (Sat.Literal.pos 2397), (Sat.Literal.pos 2396)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_8 s)

theorem counter_243_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397)) := by
  exact counter_gate s 242 8 (assignment s)
    (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397)
    rfl (rfl) rfl (rfl)

theorem clause_8601 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2398), (Sat.Literal.pos 2407)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397))
    [(Sat.Literal.neg 2398), (Sat.Literal.pos 2407)] [(Sat.Literal.neg 2398), (Sat.Literal.pos 2407)] (List.Mem.head _) (by intro l hl; exact hl) (counter_243_9 s)

theorem clause_8602 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 242), (Sat.Literal.neg 2397), (Sat.Literal.pos 2407)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397))
    [(Sat.Literal.neg 242), (Sat.Literal.neg 2397), (Sat.Literal.pos 2407)] [(Sat.Literal.neg 242), (Sat.Literal.neg 2397), (Sat.Literal.pos 2407)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_243_9 s)

theorem clause_8603 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 242)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397))
    [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 242)] [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 242)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_243_9 s)

theorem clause_8604 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 2397)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2407) (Sat.Literal.pos 2398) (Sat.Literal.pos 242) (Sat.Literal.pos 2397))
    [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 2397)] [(Sat.Literal.neg 2407), (Sat.Literal.pos 2398), (Sat.Literal.pos 2397)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_243_9 s)

theorem counter_244_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256)) := by
  exact counter_gate s 243 0 (assignment s)
    (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 243).symm)

theorem clause_8605 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2399), (Sat.Literal.pos 2408)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2399), (Sat.Literal.pos 2408)] [(Sat.Literal.neg 2399), (Sat.Literal.pos 2408)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_1 s)

theorem clause_8606 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.pos 256), (Sat.Literal.pos 2408)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 243), (Sat.Literal.pos 256), (Sat.Literal.pos 2408)] [(Sat.Literal.neg 243), (Sat.Literal.pos 256), (Sat.Literal.pos 2408)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_1 s)

theorem clause_8607 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_1 s)

theorem clause_8608 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2408) (Sat.Literal.pos 2399) (Sat.Literal.pos 243) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2408), (Sat.Literal.pos 2399), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_1 s)

theorem counter_244_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399)) := by
  exact counter_gate s 243 1 (assignment s)
    (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399)
    rfl (rfl) rfl (rfl)

theorem clause_8609 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2400), (Sat.Literal.pos 2409)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399))
    [(Sat.Literal.neg 2400), (Sat.Literal.pos 2409)] [(Sat.Literal.neg 2400), (Sat.Literal.pos 2409)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_2 s)

theorem clause_8610 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2399), (Sat.Literal.pos 2409)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2399), (Sat.Literal.pos 2409)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2399), (Sat.Literal.pos 2409)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_2 s)

theorem clause_8611 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399))
    [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_2 s)

theorem clause_8612 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 2399)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2409) (Sat.Literal.pos 2400) (Sat.Literal.pos 243) (Sat.Literal.pos 2399))
    [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 2399)] [(Sat.Literal.neg 2409), (Sat.Literal.pos 2400), (Sat.Literal.pos 2399)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_2 s)

theorem counter_244_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400)) := by
  exact counter_gate s 243 2 (assignment s)
    (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400)
    rfl (rfl) rfl (rfl)

theorem clause_8613 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2401), (Sat.Literal.pos 2410)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400))
    [(Sat.Literal.neg 2401), (Sat.Literal.pos 2410)] [(Sat.Literal.neg 2401), (Sat.Literal.pos 2410)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_3 s)

theorem clause_8614 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2400), (Sat.Literal.pos 2410)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2400), (Sat.Literal.pos 2410)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2400), (Sat.Literal.pos 2410)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_3 s)

theorem clause_8615 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400))
    [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_3 s)

theorem clause_8616 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 2400)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2410) (Sat.Literal.pos 2401) (Sat.Literal.pos 243) (Sat.Literal.pos 2400))
    [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 2400)] [(Sat.Literal.neg 2410), (Sat.Literal.pos 2401), (Sat.Literal.pos 2400)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_3 s)

theorem counter_244_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401)) := by
  exact counter_gate s 243 3 (assignment s)
    (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401)
    rfl (rfl) rfl (rfl)

theorem clause_8617 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2402), (Sat.Literal.pos 2411)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401))
    [(Sat.Literal.neg 2402), (Sat.Literal.pos 2411)] [(Sat.Literal.neg 2402), (Sat.Literal.pos 2411)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_4 s)

theorem clause_8618 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2401), (Sat.Literal.pos 2411)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2401), (Sat.Literal.pos 2411)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2401), (Sat.Literal.pos 2411)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_4 s)

theorem clause_8619 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401))
    [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_4 s)

theorem clause_8620 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 2401)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2411) (Sat.Literal.pos 2402) (Sat.Literal.pos 243) (Sat.Literal.pos 2401))
    [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 2401)] [(Sat.Literal.neg 2411), (Sat.Literal.pos 2402), (Sat.Literal.pos 2401)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_4 s)

theorem counter_244_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402)) := by
  exact counter_gate s 243 4 (assignment s)
    (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402)
    rfl (rfl) rfl (rfl)

theorem clause_8621 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2403), (Sat.Literal.pos 2412)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402))
    [(Sat.Literal.neg 2403), (Sat.Literal.pos 2412)] [(Sat.Literal.neg 2403), (Sat.Literal.pos 2412)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_5 s)

theorem clause_8622 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2402), (Sat.Literal.pos 2412)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2402), (Sat.Literal.pos 2412)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2402), (Sat.Literal.pos 2412)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_5 s)

theorem clause_8623 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402))
    [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_5 s)

theorem clause_8624 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 2402)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2412) (Sat.Literal.pos 2403) (Sat.Literal.pos 243) (Sat.Literal.pos 2402))
    [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 2402)] [(Sat.Literal.neg 2412), (Sat.Literal.pos 2403), (Sat.Literal.pos 2402)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_5 s)

theorem counter_244_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403)) := by
  exact counter_gate s 243 5 (assignment s)
    (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403)
    rfl (rfl) rfl (rfl)

theorem clause_8625 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2404), (Sat.Literal.pos 2413)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403))
    [(Sat.Literal.neg 2404), (Sat.Literal.pos 2413)] [(Sat.Literal.neg 2404), (Sat.Literal.pos 2413)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_6 s)

theorem clause_8626 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2403), (Sat.Literal.pos 2413)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2403), (Sat.Literal.pos 2413)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2403), (Sat.Literal.pos 2413)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_6 s)

theorem clause_8627 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403))
    [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_6 s)

theorem clause_8628 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 2403)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2413) (Sat.Literal.pos 2404) (Sat.Literal.pos 243) (Sat.Literal.pos 2403))
    [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 2403)] [(Sat.Literal.neg 2413), (Sat.Literal.pos 2404), (Sat.Literal.pos 2403)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_6 s)

theorem counter_244_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404)) := by
  exact counter_gate s 243 6 (assignment s)
    (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404)
    rfl (rfl) rfl (rfl)

theorem clause_8629 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2405), (Sat.Literal.pos 2414)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404))
    [(Sat.Literal.neg 2405), (Sat.Literal.pos 2414)] [(Sat.Literal.neg 2405), (Sat.Literal.pos 2414)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_7 s)

theorem clause_8630 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2404), (Sat.Literal.pos 2414)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2404), (Sat.Literal.pos 2414)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2404), (Sat.Literal.pos 2414)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_7 s)

theorem clause_8631 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404))
    [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_7 s)

theorem clause_8632 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 2404)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2414) (Sat.Literal.pos 2405) (Sat.Literal.pos 243) (Sat.Literal.pos 2404))
    [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 2404)] [(Sat.Literal.neg 2414), (Sat.Literal.pos 2405), (Sat.Literal.pos 2404)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_7 s)

theorem counter_244_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405)) := by
  exact counter_gate s 243 7 (assignment s)
    (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405)
    rfl (rfl) rfl (rfl)

theorem clause_8633 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2406), (Sat.Literal.pos 2415)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405))
    [(Sat.Literal.neg 2406), (Sat.Literal.pos 2415)] [(Sat.Literal.neg 2406), (Sat.Literal.pos 2415)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_8 s)

theorem clause_8634 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2405), (Sat.Literal.pos 2415)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2405), (Sat.Literal.pos 2415)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2405), (Sat.Literal.pos 2415)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_8 s)

theorem clause_8635 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405))
    [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_8 s)

theorem clause_8636 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 2405)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2415) (Sat.Literal.pos 2406) (Sat.Literal.pos 243) (Sat.Literal.pos 2405))
    [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 2405)] [(Sat.Literal.neg 2415), (Sat.Literal.pos 2406), (Sat.Literal.pos 2405)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_8 s)

theorem counter_244_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406)) := by
  exact counter_gate s 243 8 (assignment s)
    (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406)
    rfl (rfl) rfl (rfl)

theorem clause_8637 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2407), (Sat.Literal.pos 2416)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406))
    [(Sat.Literal.neg 2407), (Sat.Literal.pos 2416)] [(Sat.Literal.neg 2407), (Sat.Literal.pos 2416)] (List.Mem.head _) (by intro l hl; exact hl) (counter_244_9 s)

theorem clause_8638 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 243), (Sat.Literal.neg 2406), (Sat.Literal.pos 2416)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406))
    [(Sat.Literal.neg 243), (Sat.Literal.neg 2406), (Sat.Literal.pos 2416)] [(Sat.Literal.neg 243), (Sat.Literal.neg 2406), (Sat.Literal.pos 2416)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_244_9 s)

theorem clause_8639 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 243)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406))
    [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 243)] [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 243)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_244_9 s)

theorem clause_8640 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 2406)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2416) (Sat.Literal.pos 2407) (Sat.Literal.pos 243) (Sat.Literal.pos 2406))
    [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 2406)] [(Sat.Literal.neg 2416), (Sat.Literal.pos 2407), (Sat.Literal.pos 2406)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_244_9 s)

theorem counter_245_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256)) := by
  exact counter_gate s 244 0 (assignment s)
    (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 244).symm)

theorem clause_8641 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2408), (Sat.Literal.pos 2417)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2408), (Sat.Literal.pos 2417)] [(Sat.Literal.neg 2408), (Sat.Literal.pos 2417)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_1 s)

theorem clause_8642 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.pos 256), (Sat.Literal.pos 2417)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 244), (Sat.Literal.pos 256), (Sat.Literal.pos 2417)] [(Sat.Literal.neg 244), (Sat.Literal.pos 256), (Sat.Literal.pos 2417)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_1 s)

theorem clause_8643 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_1 s)

theorem clause_8644 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2417) (Sat.Literal.pos 2408) (Sat.Literal.pos 244) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2417), (Sat.Literal.pos 2408), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_1 s)

theorem counter_245_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408)) := by
  exact counter_gate s 244 1 (assignment s)
    (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408)
    rfl (rfl) rfl (rfl)

theorem clause_8645 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2409), (Sat.Literal.pos 2418)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408))
    [(Sat.Literal.neg 2409), (Sat.Literal.pos 2418)] [(Sat.Literal.neg 2409), (Sat.Literal.pos 2418)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_2 s)

theorem clause_8646 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2408), (Sat.Literal.pos 2418)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2408), (Sat.Literal.pos 2418)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2408), (Sat.Literal.pos 2418)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_2 s)

theorem clause_8647 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408))
    [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_2 s)

theorem clause_8648 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 2408)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2418) (Sat.Literal.pos 2409) (Sat.Literal.pos 244) (Sat.Literal.pos 2408))
    [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 2408)] [(Sat.Literal.neg 2418), (Sat.Literal.pos 2409), (Sat.Literal.pos 2408)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_2 s)

theorem counter_245_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409)) := by
  exact counter_gate s 244 2 (assignment s)
    (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409)
    rfl (rfl) rfl (rfl)

theorem clause_8649 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2410), (Sat.Literal.pos 2419)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409))
    [(Sat.Literal.neg 2410), (Sat.Literal.pos 2419)] [(Sat.Literal.neg 2410), (Sat.Literal.pos 2419)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_3 s)

theorem clause_8650 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2409), (Sat.Literal.pos 2419)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2409), (Sat.Literal.pos 2419)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2409), (Sat.Literal.pos 2419)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_3 s)

theorem clause_8651 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409))
    [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_3 s)

theorem clause_8652 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 2409)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2419) (Sat.Literal.pos 2410) (Sat.Literal.pos 244) (Sat.Literal.pos 2409))
    [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 2409)] [(Sat.Literal.neg 2419), (Sat.Literal.pos 2410), (Sat.Literal.pos 2409)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_3 s)

theorem counter_245_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410)) := by
  exact counter_gate s 244 3 (assignment s)
    (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410)
    rfl (rfl) rfl (rfl)

theorem clause_8653 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2411), (Sat.Literal.pos 2420)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410))
    [(Sat.Literal.neg 2411), (Sat.Literal.pos 2420)] [(Sat.Literal.neg 2411), (Sat.Literal.pos 2420)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_4 s)

theorem clause_8654 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2410), (Sat.Literal.pos 2420)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2410), (Sat.Literal.pos 2420)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2410), (Sat.Literal.pos 2420)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_4 s)

theorem clause_8655 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410))
    [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_4 s)

theorem clause_8656 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 2410)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2420) (Sat.Literal.pos 2411) (Sat.Literal.pos 244) (Sat.Literal.pos 2410))
    [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 2410)] [(Sat.Literal.neg 2420), (Sat.Literal.pos 2411), (Sat.Literal.pos 2410)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_4 s)

theorem counter_245_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411)) := by
  exact counter_gate s 244 4 (assignment s)
    (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411)
    rfl (rfl) rfl (rfl)

theorem clause_8657 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2412), (Sat.Literal.pos 2421)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411))
    [(Sat.Literal.neg 2412), (Sat.Literal.pos 2421)] [(Sat.Literal.neg 2412), (Sat.Literal.pos 2421)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_5 s)

theorem clause_8658 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2411), (Sat.Literal.pos 2421)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2411), (Sat.Literal.pos 2421)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2411), (Sat.Literal.pos 2421)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_5 s)

theorem clause_8659 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411))
    [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_5 s)

theorem clause_8660 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 2411)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2421) (Sat.Literal.pos 2412) (Sat.Literal.pos 244) (Sat.Literal.pos 2411))
    [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 2411)] [(Sat.Literal.neg 2421), (Sat.Literal.pos 2412), (Sat.Literal.pos 2411)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_5 s)

theorem counter_245_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412)) := by
  exact counter_gate s 244 5 (assignment s)
    (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412)
    rfl (rfl) rfl (rfl)

theorem clause_8661 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2413), (Sat.Literal.pos 2422)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412))
    [(Sat.Literal.neg 2413), (Sat.Literal.pos 2422)] [(Sat.Literal.neg 2413), (Sat.Literal.pos 2422)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_6 s)

theorem clause_8662 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2412), (Sat.Literal.pos 2422)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2412), (Sat.Literal.pos 2422)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2412), (Sat.Literal.pos 2422)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_6 s)

theorem clause_8663 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412))
    [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_6 s)

theorem clause_8664 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 2412)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2422) (Sat.Literal.pos 2413) (Sat.Literal.pos 244) (Sat.Literal.pos 2412))
    [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 2412)] [(Sat.Literal.neg 2422), (Sat.Literal.pos 2413), (Sat.Literal.pos 2412)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_6 s)

theorem counter_245_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413)) := by
  exact counter_gate s 244 6 (assignment s)
    (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413)
    rfl (rfl) rfl (rfl)

theorem clause_8665 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2414), (Sat.Literal.pos 2423)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413))
    [(Sat.Literal.neg 2414), (Sat.Literal.pos 2423)] [(Sat.Literal.neg 2414), (Sat.Literal.pos 2423)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_7 s)

theorem clause_8666 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2413), (Sat.Literal.pos 2423)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2413), (Sat.Literal.pos 2423)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2413), (Sat.Literal.pos 2423)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_7 s)

theorem clause_8667 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413))
    [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_7 s)

theorem clause_8668 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 2413)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2423) (Sat.Literal.pos 2414) (Sat.Literal.pos 244) (Sat.Literal.pos 2413))
    [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 2413)] [(Sat.Literal.neg 2423), (Sat.Literal.pos 2414), (Sat.Literal.pos 2413)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_7 s)

theorem counter_245_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414)) := by
  exact counter_gate s 244 7 (assignment s)
    (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414)
    rfl (rfl) rfl (rfl)

theorem clause_8669 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2415), (Sat.Literal.pos 2424)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414))
    [(Sat.Literal.neg 2415), (Sat.Literal.pos 2424)] [(Sat.Literal.neg 2415), (Sat.Literal.pos 2424)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_8 s)

theorem clause_8670 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2414), (Sat.Literal.pos 2424)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2414), (Sat.Literal.pos 2424)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2414), (Sat.Literal.pos 2424)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_8 s)

theorem clause_8671 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414))
    [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_8 s)

theorem clause_8672 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 2414)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2424) (Sat.Literal.pos 2415) (Sat.Literal.pos 244) (Sat.Literal.pos 2414))
    [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 2414)] [(Sat.Literal.neg 2424), (Sat.Literal.pos 2415), (Sat.Literal.pos 2414)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_8 s)

theorem counter_245_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415)) := by
  exact counter_gate s 244 8 (assignment s)
    (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415)
    rfl (rfl) rfl (rfl)

theorem clause_8673 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2416), (Sat.Literal.pos 2425)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415))
    [(Sat.Literal.neg 2416), (Sat.Literal.pos 2425)] [(Sat.Literal.neg 2416), (Sat.Literal.pos 2425)] (List.Mem.head _) (by intro l hl; exact hl) (counter_245_9 s)

theorem clause_8674 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 244), (Sat.Literal.neg 2415), (Sat.Literal.pos 2425)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415))
    [(Sat.Literal.neg 244), (Sat.Literal.neg 2415), (Sat.Literal.pos 2425)] [(Sat.Literal.neg 244), (Sat.Literal.neg 2415), (Sat.Literal.pos 2425)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_245_9 s)

theorem clause_8675 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 244)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415))
    [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 244)] [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 244)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_245_9 s)

theorem clause_8676 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 2415)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2425) (Sat.Literal.pos 2416) (Sat.Literal.pos 244) (Sat.Literal.pos 2415))
    [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 2415)] [(Sat.Literal.neg 2425), (Sat.Literal.pos 2416), (Sat.Literal.pos 2415)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_245_9 s)

theorem counter_246_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256)) := by
  exact counter_gate s 245 0 (assignment s)
    (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 245).symm)

theorem clause_8677 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2417), (Sat.Literal.pos 2426)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2417), (Sat.Literal.pos 2426)] [(Sat.Literal.neg 2417), (Sat.Literal.pos 2426)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_1 s)

theorem clause_8678 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.pos 256), (Sat.Literal.pos 2426)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 245), (Sat.Literal.pos 256), (Sat.Literal.pos 2426)] [(Sat.Literal.neg 245), (Sat.Literal.pos 256), (Sat.Literal.pos 2426)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_1 s)

theorem clause_8679 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_1 s)

theorem clause_8680 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2426) (Sat.Literal.pos 2417) (Sat.Literal.pos 245) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2426), (Sat.Literal.pos 2417), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_1 s)

theorem counter_246_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417)) := by
  exact counter_gate s 245 1 (assignment s)
    (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417)
    rfl (rfl) rfl (rfl)

theorem clause_8681 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2418), (Sat.Literal.pos 2427)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417))
    [(Sat.Literal.neg 2418), (Sat.Literal.pos 2427)] [(Sat.Literal.neg 2418), (Sat.Literal.pos 2427)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_2 s)

theorem clause_8682 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2417), (Sat.Literal.pos 2427)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2417), (Sat.Literal.pos 2427)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2417), (Sat.Literal.pos 2427)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_2 s)

theorem clause_8683 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417))
    [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_2 s)

theorem clause_8684 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 2417)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2427) (Sat.Literal.pos 2418) (Sat.Literal.pos 245) (Sat.Literal.pos 2417))
    [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 2417)] [(Sat.Literal.neg 2427), (Sat.Literal.pos 2418), (Sat.Literal.pos 2417)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_2 s)

theorem counter_246_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418)) := by
  exact counter_gate s 245 2 (assignment s)
    (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418)
    rfl (rfl) rfl (rfl)

theorem clause_8685 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2419), (Sat.Literal.pos 2428)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418))
    [(Sat.Literal.neg 2419), (Sat.Literal.pos 2428)] [(Sat.Literal.neg 2419), (Sat.Literal.pos 2428)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_3 s)

theorem clause_8686 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2418), (Sat.Literal.pos 2428)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2418), (Sat.Literal.pos 2428)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2418), (Sat.Literal.pos 2428)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_3 s)

theorem clause_8687 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418))
    [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_3 s)

theorem clause_8688 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 2418)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2428) (Sat.Literal.pos 2419) (Sat.Literal.pos 245) (Sat.Literal.pos 2418))
    [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 2418)] [(Sat.Literal.neg 2428), (Sat.Literal.pos 2419), (Sat.Literal.pos 2418)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_3 s)

theorem counter_246_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419)) := by
  exact counter_gate s 245 3 (assignment s)
    (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419)
    rfl (rfl) rfl (rfl)

theorem clause_8689 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2420), (Sat.Literal.pos 2429)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419))
    [(Sat.Literal.neg 2420), (Sat.Literal.pos 2429)] [(Sat.Literal.neg 2420), (Sat.Literal.pos 2429)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_4 s)

theorem clause_8690 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2419), (Sat.Literal.pos 2429)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2419), (Sat.Literal.pos 2429)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2419), (Sat.Literal.pos 2429)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_4 s)

theorem clause_8691 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419))
    [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_4 s)

theorem clause_8692 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 2419)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2429) (Sat.Literal.pos 2420) (Sat.Literal.pos 245) (Sat.Literal.pos 2419))
    [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 2419)] [(Sat.Literal.neg 2429), (Sat.Literal.pos 2420), (Sat.Literal.pos 2419)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_4 s)

theorem counter_246_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420)) := by
  exact counter_gate s 245 4 (assignment s)
    (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420)
    rfl (rfl) rfl (rfl)

theorem clause_8693 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2421), (Sat.Literal.pos 2430)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420))
    [(Sat.Literal.neg 2421), (Sat.Literal.pos 2430)] [(Sat.Literal.neg 2421), (Sat.Literal.pos 2430)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_5 s)

theorem clause_8694 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2420), (Sat.Literal.pos 2430)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2420), (Sat.Literal.pos 2430)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2420), (Sat.Literal.pos 2430)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_5 s)

theorem clause_8695 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420))
    [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_5 s)

theorem clause_8696 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 2420)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2430) (Sat.Literal.pos 2421) (Sat.Literal.pos 245) (Sat.Literal.pos 2420))
    [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 2420)] [(Sat.Literal.neg 2430), (Sat.Literal.pos 2421), (Sat.Literal.pos 2420)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_5 s)

theorem counter_246_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421)) := by
  exact counter_gate s 245 5 (assignment s)
    (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421)
    rfl (rfl) rfl (rfl)

theorem clause_8697 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2422), (Sat.Literal.pos 2431)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421))
    [(Sat.Literal.neg 2422), (Sat.Literal.pos 2431)] [(Sat.Literal.neg 2422), (Sat.Literal.pos 2431)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_6 s)

theorem clause_8698 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2421), (Sat.Literal.pos 2431)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2421), (Sat.Literal.pos 2431)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2421), (Sat.Literal.pos 2431)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_6 s)

theorem clause_8699 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421))
    [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_6 s)

theorem clause_8700 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 2421)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2431) (Sat.Literal.pos 2422) (Sat.Literal.pos 245) (Sat.Literal.pos 2421))
    [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 2421)] [(Sat.Literal.neg 2431), (Sat.Literal.pos 2422), (Sat.Literal.pos 2421)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_6 s)

theorem counter_246_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422)) := by
  exact counter_gate s 245 6 (assignment s)
    (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422)
    rfl (rfl) rfl (rfl)

theorem clause_8701 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2423), (Sat.Literal.pos 2432)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422))
    [(Sat.Literal.neg 2423), (Sat.Literal.pos 2432)] [(Sat.Literal.neg 2423), (Sat.Literal.pos 2432)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_7 s)

theorem clause_8702 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2422), (Sat.Literal.pos 2432)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2422), (Sat.Literal.pos 2432)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2422), (Sat.Literal.pos 2432)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_7 s)

theorem clause_8703 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422))
    [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_7 s)

theorem clause_8704 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 2422)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2432) (Sat.Literal.pos 2423) (Sat.Literal.pos 245) (Sat.Literal.pos 2422))
    [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 2422)] [(Sat.Literal.neg 2432), (Sat.Literal.pos 2423), (Sat.Literal.pos 2422)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_7 s)

theorem counter_246_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423)) := by
  exact counter_gate s 245 7 (assignment s)
    (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423)
    rfl (rfl) rfl (rfl)

theorem clause_8705 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2424), (Sat.Literal.pos 2433)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423))
    [(Sat.Literal.neg 2424), (Sat.Literal.pos 2433)] [(Sat.Literal.neg 2424), (Sat.Literal.pos 2433)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_8 s)

theorem clause_8706 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2423), (Sat.Literal.pos 2433)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2423), (Sat.Literal.pos 2433)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2423), (Sat.Literal.pos 2433)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_8 s)

theorem clause_8707 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423))
    [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_8 s)

theorem clause_8708 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 2423)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2433) (Sat.Literal.pos 2424) (Sat.Literal.pos 245) (Sat.Literal.pos 2423))
    [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 2423)] [(Sat.Literal.neg 2433), (Sat.Literal.pos 2424), (Sat.Literal.pos 2423)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_8 s)

theorem counter_246_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424)) := by
  exact counter_gate s 245 8 (assignment s)
    (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424)
    rfl (rfl) rfl (rfl)

theorem clause_8709 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2425), (Sat.Literal.pos 2434)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424))
    [(Sat.Literal.neg 2425), (Sat.Literal.pos 2434)] [(Sat.Literal.neg 2425), (Sat.Literal.pos 2434)] (List.Mem.head _) (by intro l hl; exact hl) (counter_246_9 s)

theorem clause_8710 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 245), (Sat.Literal.neg 2424), (Sat.Literal.pos 2434)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424))
    [(Sat.Literal.neg 245), (Sat.Literal.neg 2424), (Sat.Literal.pos 2434)] [(Sat.Literal.neg 245), (Sat.Literal.neg 2424), (Sat.Literal.pos 2434)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_246_9 s)

theorem clause_8711 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 245)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424))
    [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 245)] [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 245)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_246_9 s)

theorem clause_8712 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 2424)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2434) (Sat.Literal.pos 2425) (Sat.Literal.pos 245) (Sat.Literal.pos 2424))
    [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 2424)] [(Sat.Literal.neg 2434), (Sat.Literal.pos 2425), (Sat.Literal.pos 2424)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_246_9 s)

theorem counter_247_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256)) := by
  exact counter_gate s 246 0 (assignment s)
    (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 246).symm)

theorem clause_8713 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2426), (Sat.Literal.pos 2435)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2426), (Sat.Literal.pos 2435)] [(Sat.Literal.neg 2426), (Sat.Literal.pos 2435)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_1 s)

theorem clause_8714 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.pos 256), (Sat.Literal.pos 2435)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 246), (Sat.Literal.pos 256), (Sat.Literal.pos 2435)] [(Sat.Literal.neg 246), (Sat.Literal.pos 256), (Sat.Literal.pos 2435)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_1 s)

theorem clause_8715 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_1 s)

theorem clause_8716 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2435) (Sat.Literal.pos 2426) (Sat.Literal.pos 246) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2435), (Sat.Literal.pos 2426), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_1 s)

theorem counter_247_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426)) := by
  exact counter_gate s 246 1 (assignment s)
    (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426)
    rfl (rfl) rfl (rfl)

theorem clause_8717 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2427), (Sat.Literal.pos 2436)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426))
    [(Sat.Literal.neg 2427), (Sat.Literal.pos 2436)] [(Sat.Literal.neg 2427), (Sat.Literal.pos 2436)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_2 s)

theorem clause_8718 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2426), (Sat.Literal.pos 2436)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2426), (Sat.Literal.pos 2436)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2426), (Sat.Literal.pos 2436)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_2 s)

theorem clause_8719 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426))
    [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_2 s)

theorem clause_8720 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 2426)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2436) (Sat.Literal.pos 2427) (Sat.Literal.pos 246) (Sat.Literal.pos 2426))
    [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 2426)] [(Sat.Literal.neg 2436), (Sat.Literal.pos 2427), (Sat.Literal.pos 2426)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_2 s)

theorem counter_247_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427)) := by
  exact counter_gate s 246 2 (assignment s)
    (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427)
    rfl (rfl) rfl (rfl)

theorem clause_8721 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2428), (Sat.Literal.pos 2437)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427))
    [(Sat.Literal.neg 2428), (Sat.Literal.pos 2437)] [(Sat.Literal.neg 2428), (Sat.Literal.pos 2437)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_3 s)

theorem clause_8722 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2427), (Sat.Literal.pos 2437)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2427), (Sat.Literal.pos 2437)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2427), (Sat.Literal.pos 2437)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_3 s)

theorem clause_8723 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427))
    [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_3 s)

theorem clause_8724 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 2427)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2437) (Sat.Literal.pos 2428) (Sat.Literal.pos 246) (Sat.Literal.pos 2427))
    [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 2427)] [(Sat.Literal.neg 2437), (Sat.Literal.pos 2428), (Sat.Literal.pos 2427)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_3 s)

theorem counter_247_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428)) := by
  exact counter_gate s 246 3 (assignment s)
    (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428)
    rfl (rfl) rfl (rfl)

theorem clause_8725 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2429), (Sat.Literal.pos 2438)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428))
    [(Sat.Literal.neg 2429), (Sat.Literal.pos 2438)] [(Sat.Literal.neg 2429), (Sat.Literal.pos 2438)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_4 s)

theorem clause_8726 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2428), (Sat.Literal.pos 2438)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2428), (Sat.Literal.pos 2438)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2428), (Sat.Literal.pos 2438)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_4 s)

theorem clause_8727 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428))
    [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_4 s)

theorem clause_8728 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 2428)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2438) (Sat.Literal.pos 2429) (Sat.Literal.pos 246) (Sat.Literal.pos 2428))
    [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 2428)] [(Sat.Literal.neg 2438), (Sat.Literal.pos 2429), (Sat.Literal.pos 2428)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_4 s)

theorem counter_247_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429)) := by
  exact counter_gate s 246 4 (assignment s)
    (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429)
    rfl (rfl) rfl (rfl)

theorem clause_8729 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2430), (Sat.Literal.pos 2439)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429))
    [(Sat.Literal.neg 2430), (Sat.Literal.pos 2439)] [(Sat.Literal.neg 2430), (Sat.Literal.pos 2439)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_5 s)

theorem clause_8730 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2429), (Sat.Literal.pos 2439)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2429), (Sat.Literal.pos 2439)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2429), (Sat.Literal.pos 2439)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_5 s)

theorem clause_8731 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429))
    [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_5 s)

theorem clause_8732 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 2429)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2439) (Sat.Literal.pos 2430) (Sat.Literal.pos 246) (Sat.Literal.pos 2429))
    [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 2429)] [(Sat.Literal.neg 2439), (Sat.Literal.pos 2430), (Sat.Literal.pos 2429)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_5 s)

theorem counter_247_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430)) := by
  exact counter_gate s 246 5 (assignment s)
    (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430)
    rfl (rfl) rfl (rfl)

theorem clause_8733 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2431), (Sat.Literal.pos 2440)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430))
    [(Sat.Literal.neg 2431), (Sat.Literal.pos 2440)] [(Sat.Literal.neg 2431), (Sat.Literal.pos 2440)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_6 s)

theorem clause_8734 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2430), (Sat.Literal.pos 2440)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2430), (Sat.Literal.pos 2440)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2430), (Sat.Literal.pos 2440)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_6 s)

theorem clause_8735 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430))
    [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_6 s)

theorem clause_8736 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 2430)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2440) (Sat.Literal.pos 2431) (Sat.Literal.pos 246) (Sat.Literal.pos 2430))
    [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 2430)] [(Sat.Literal.neg 2440), (Sat.Literal.pos 2431), (Sat.Literal.pos 2430)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_6 s)

theorem counter_247_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431)) := by
  exact counter_gate s 246 6 (assignment s)
    (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431)
    rfl (rfl) rfl (rfl)

theorem clause_8737 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2432), (Sat.Literal.pos 2441)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431))
    [(Sat.Literal.neg 2432), (Sat.Literal.pos 2441)] [(Sat.Literal.neg 2432), (Sat.Literal.pos 2441)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_7 s)

theorem clause_8738 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2431), (Sat.Literal.pos 2441)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2431), (Sat.Literal.pos 2441)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2431), (Sat.Literal.pos 2441)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_7 s)

theorem clause_8739 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431))
    [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_7 s)

theorem clause_8740 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 2431)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2441) (Sat.Literal.pos 2432) (Sat.Literal.pos 246) (Sat.Literal.pos 2431))
    [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 2431)] [(Sat.Literal.neg 2441), (Sat.Literal.pos 2432), (Sat.Literal.pos 2431)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_7 s)

theorem counter_247_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432)) := by
  exact counter_gate s 246 7 (assignment s)
    (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432)
    rfl (rfl) rfl (rfl)

theorem clause_8741 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2433), (Sat.Literal.pos 2442)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432))
    [(Sat.Literal.neg 2433), (Sat.Literal.pos 2442)] [(Sat.Literal.neg 2433), (Sat.Literal.pos 2442)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_8 s)

theorem clause_8742 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2432), (Sat.Literal.pos 2442)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2432), (Sat.Literal.pos 2442)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2432), (Sat.Literal.pos 2442)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_8 s)

theorem clause_8743 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432))
    [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_8 s)

theorem clause_8744 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 2432)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2442) (Sat.Literal.pos 2433) (Sat.Literal.pos 246) (Sat.Literal.pos 2432))
    [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 2432)] [(Sat.Literal.neg 2442), (Sat.Literal.pos 2433), (Sat.Literal.pos 2432)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_8 s)

theorem counter_247_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433)) := by
  exact counter_gate s 246 8 (assignment s)
    (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433)
    rfl (rfl) rfl (rfl)

theorem clause_8745 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2434), (Sat.Literal.pos 2443)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433))
    [(Sat.Literal.neg 2434), (Sat.Literal.pos 2443)] [(Sat.Literal.neg 2434), (Sat.Literal.pos 2443)] (List.Mem.head _) (by intro l hl; exact hl) (counter_247_9 s)

theorem clause_8746 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 246), (Sat.Literal.neg 2433), (Sat.Literal.pos 2443)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433))
    [(Sat.Literal.neg 246), (Sat.Literal.neg 2433), (Sat.Literal.pos 2443)] [(Sat.Literal.neg 246), (Sat.Literal.neg 2433), (Sat.Literal.pos 2443)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_247_9 s)

theorem clause_8747 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 246)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433))
    [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 246)] [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 246)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_247_9 s)

theorem clause_8748 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 2433)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2443) (Sat.Literal.pos 2434) (Sat.Literal.pos 246) (Sat.Literal.pos 2433))
    [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 2433)] [(Sat.Literal.neg 2443), (Sat.Literal.pos 2434), (Sat.Literal.pos 2433)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_247_9 s)

theorem counter_248_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256)) := by
  exact counter_gate s 247 0 (assignment s)
    (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 247).symm)

theorem clause_8749 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2435), (Sat.Literal.pos 2444)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2435), (Sat.Literal.pos 2444)] [(Sat.Literal.neg 2435), (Sat.Literal.pos 2444)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_1 s)

theorem clause_8750 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.pos 256), (Sat.Literal.pos 2444)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 247), (Sat.Literal.pos 256), (Sat.Literal.pos 2444)] [(Sat.Literal.neg 247), (Sat.Literal.pos 256), (Sat.Literal.pos 2444)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_1 s)

theorem clause_8751 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_1 s)

theorem clause_8752 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2444) (Sat.Literal.pos 2435) (Sat.Literal.pos 247) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2444), (Sat.Literal.pos 2435), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_1 s)

theorem counter_248_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435)) := by
  exact counter_gate s 247 1 (assignment s)
    (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435)
    rfl (rfl) rfl (rfl)

theorem clause_8753 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2436), (Sat.Literal.pos 2445)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435))
    [(Sat.Literal.neg 2436), (Sat.Literal.pos 2445)] [(Sat.Literal.neg 2436), (Sat.Literal.pos 2445)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_2 s)

theorem clause_8754 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2435), (Sat.Literal.pos 2445)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2435), (Sat.Literal.pos 2445)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2435), (Sat.Literal.pos 2445)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_2 s)

theorem clause_8755 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435))
    [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_2 s)

theorem clause_8756 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 2435)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2445) (Sat.Literal.pos 2436) (Sat.Literal.pos 247) (Sat.Literal.pos 2435))
    [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 2435)] [(Sat.Literal.neg 2445), (Sat.Literal.pos 2436), (Sat.Literal.pos 2435)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_2 s)

theorem counter_248_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436)) := by
  exact counter_gate s 247 2 (assignment s)
    (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436)
    rfl (rfl) rfl (rfl)

theorem clause_8757 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2437), (Sat.Literal.pos 2446)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436))
    [(Sat.Literal.neg 2437), (Sat.Literal.pos 2446)] [(Sat.Literal.neg 2437), (Sat.Literal.pos 2446)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_3 s)

theorem clause_8758 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2436), (Sat.Literal.pos 2446)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2436), (Sat.Literal.pos 2446)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2436), (Sat.Literal.pos 2446)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_3 s)

theorem clause_8759 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436))
    [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_3 s)

theorem clause_8760 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 2436)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2446) (Sat.Literal.pos 2437) (Sat.Literal.pos 247) (Sat.Literal.pos 2436))
    [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 2436)] [(Sat.Literal.neg 2446), (Sat.Literal.pos 2437), (Sat.Literal.pos 2436)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_3 s)

theorem counter_248_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437)) := by
  exact counter_gate s 247 3 (assignment s)
    (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437)
    rfl (rfl) rfl (rfl)

theorem clause_8761 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2438), (Sat.Literal.pos 2447)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437))
    [(Sat.Literal.neg 2438), (Sat.Literal.pos 2447)] [(Sat.Literal.neg 2438), (Sat.Literal.pos 2447)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_4 s)

theorem clause_8762 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2437), (Sat.Literal.pos 2447)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2437), (Sat.Literal.pos 2447)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2437), (Sat.Literal.pos 2447)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_4 s)

theorem clause_8763 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437))
    [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_4 s)

theorem clause_8764 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 2437)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2447) (Sat.Literal.pos 2438) (Sat.Literal.pos 247) (Sat.Literal.pos 2437))
    [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 2437)] [(Sat.Literal.neg 2447), (Sat.Literal.pos 2438), (Sat.Literal.pos 2437)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_4 s)

theorem counter_248_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438)) := by
  exact counter_gate s 247 4 (assignment s)
    (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438)
    rfl (rfl) rfl (rfl)

theorem clause_8765 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2439), (Sat.Literal.pos 2448)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438))
    [(Sat.Literal.neg 2439), (Sat.Literal.pos 2448)] [(Sat.Literal.neg 2439), (Sat.Literal.pos 2448)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_5 s)

theorem clause_8766 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2438), (Sat.Literal.pos 2448)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2438), (Sat.Literal.pos 2448)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2438), (Sat.Literal.pos 2448)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_5 s)

theorem clause_8767 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438))
    [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_5 s)

theorem clause_8768 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 2438)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2448) (Sat.Literal.pos 2439) (Sat.Literal.pos 247) (Sat.Literal.pos 2438))
    [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 2438)] [(Sat.Literal.neg 2448), (Sat.Literal.pos 2439), (Sat.Literal.pos 2438)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_5 s)

theorem counter_248_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439)) := by
  exact counter_gate s 247 5 (assignment s)
    (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439)
    rfl (rfl) rfl (rfl)

theorem clause_8769 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2440), (Sat.Literal.pos 2449)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439))
    [(Sat.Literal.neg 2440), (Sat.Literal.pos 2449)] [(Sat.Literal.neg 2440), (Sat.Literal.pos 2449)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_6 s)

theorem clause_8770 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2439), (Sat.Literal.pos 2449)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2439), (Sat.Literal.pos 2449)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2439), (Sat.Literal.pos 2449)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_6 s)

theorem clause_8771 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439))
    [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_6 s)

theorem clause_8772 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 2439)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2449) (Sat.Literal.pos 2440) (Sat.Literal.pos 247) (Sat.Literal.pos 2439))
    [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 2439)] [(Sat.Literal.neg 2449), (Sat.Literal.pos 2440), (Sat.Literal.pos 2439)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_6 s)

theorem counter_248_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440)) := by
  exact counter_gate s 247 6 (assignment s)
    (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440)
    rfl (rfl) rfl (rfl)

theorem clause_8773 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2441), (Sat.Literal.pos 2450)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440))
    [(Sat.Literal.neg 2441), (Sat.Literal.pos 2450)] [(Sat.Literal.neg 2441), (Sat.Literal.pos 2450)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_7 s)

theorem clause_8774 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2440), (Sat.Literal.pos 2450)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2440), (Sat.Literal.pos 2450)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2440), (Sat.Literal.pos 2450)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_7 s)

theorem clause_8775 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440))
    [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_7 s)

theorem clause_8776 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 2440)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2450) (Sat.Literal.pos 2441) (Sat.Literal.pos 247) (Sat.Literal.pos 2440))
    [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 2440)] [(Sat.Literal.neg 2450), (Sat.Literal.pos 2441), (Sat.Literal.pos 2440)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_7 s)

theorem counter_248_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441)) := by
  exact counter_gate s 247 7 (assignment s)
    (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441)
    rfl (rfl) rfl (rfl)

theorem clause_8777 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2442), (Sat.Literal.pos 2451)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441))
    [(Sat.Literal.neg 2442), (Sat.Literal.pos 2451)] [(Sat.Literal.neg 2442), (Sat.Literal.pos 2451)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_8 s)

theorem clause_8778 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2441), (Sat.Literal.pos 2451)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2441), (Sat.Literal.pos 2451)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2441), (Sat.Literal.pos 2451)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_8 s)

theorem clause_8779 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441))
    [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_8 s)

theorem clause_8780 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 2441)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2451) (Sat.Literal.pos 2442) (Sat.Literal.pos 247) (Sat.Literal.pos 2441))
    [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 2441)] [(Sat.Literal.neg 2451), (Sat.Literal.pos 2442), (Sat.Literal.pos 2441)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_8 s)

theorem counter_248_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442)) := by
  exact counter_gate s 247 8 (assignment s)
    (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442)
    rfl (rfl) rfl (rfl)

theorem clause_8781 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2443), (Sat.Literal.pos 2452)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442))
    [(Sat.Literal.neg 2443), (Sat.Literal.pos 2452)] [(Sat.Literal.neg 2443), (Sat.Literal.pos 2452)] (List.Mem.head _) (by intro l hl; exact hl) (counter_248_9 s)

theorem clause_8782 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 247), (Sat.Literal.neg 2442), (Sat.Literal.pos 2452)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442))
    [(Sat.Literal.neg 247), (Sat.Literal.neg 2442), (Sat.Literal.pos 2452)] [(Sat.Literal.neg 247), (Sat.Literal.neg 2442), (Sat.Literal.pos 2452)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_248_9 s)

theorem clause_8783 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 247)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442))
    [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 247)] [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 247)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_248_9 s)

theorem clause_8784 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 2442)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2452) (Sat.Literal.pos 2443) (Sat.Literal.pos 247) (Sat.Literal.pos 2442))
    [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 2442)] [(Sat.Literal.neg 2452), (Sat.Literal.pos 2443), (Sat.Literal.pos 2442)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_248_9 s)

theorem counter_249_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256)) := by
  exact counter_gate s 248 0 (assignment s)
    (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 248).symm)

theorem clause_8785 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2444), (Sat.Literal.pos 2453)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2444), (Sat.Literal.pos 2453)] [(Sat.Literal.neg 2444), (Sat.Literal.pos 2453)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_1 s)

theorem clause_8786 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.pos 256), (Sat.Literal.pos 2453)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 248), (Sat.Literal.pos 256), (Sat.Literal.pos 2453)] [(Sat.Literal.neg 248), (Sat.Literal.pos 256), (Sat.Literal.pos 2453)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_1 s)

theorem clause_8787 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_1 s)

theorem clause_8788 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2453) (Sat.Literal.pos 2444) (Sat.Literal.pos 248) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2453), (Sat.Literal.pos 2444), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_1 s)

theorem counter_249_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444)) := by
  exact counter_gate s 248 1 (assignment s)
    (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444)
    rfl (rfl) rfl (rfl)

theorem clause_8789 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2445), (Sat.Literal.pos 2454)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444))
    [(Sat.Literal.neg 2445), (Sat.Literal.pos 2454)] [(Sat.Literal.neg 2445), (Sat.Literal.pos 2454)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_2 s)

theorem clause_8790 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2444), (Sat.Literal.pos 2454)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2444), (Sat.Literal.pos 2454)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2444), (Sat.Literal.pos 2454)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_2 s)

theorem clause_8791 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444))
    [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_2 s)

theorem clause_8792 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 2444)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2454) (Sat.Literal.pos 2445) (Sat.Literal.pos 248) (Sat.Literal.pos 2444))
    [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 2444)] [(Sat.Literal.neg 2454), (Sat.Literal.pos 2445), (Sat.Literal.pos 2444)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_2 s)

theorem counter_249_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445)) := by
  exact counter_gate s 248 2 (assignment s)
    (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445)
    rfl (rfl) rfl (rfl)

theorem clause_8793 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2446), (Sat.Literal.pos 2455)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445))
    [(Sat.Literal.neg 2446), (Sat.Literal.pos 2455)] [(Sat.Literal.neg 2446), (Sat.Literal.pos 2455)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_3 s)

theorem clause_8794 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2445), (Sat.Literal.pos 2455)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2445), (Sat.Literal.pos 2455)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2445), (Sat.Literal.pos 2455)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_3 s)

theorem clause_8795 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445))
    [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_3 s)

theorem clause_8796 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 2445)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2455) (Sat.Literal.pos 2446) (Sat.Literal.pos 248) (Sat.Literal.pos 2445))
    [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 2445)] [(Sat.Literal.neg 2455), (Sat.Literal.pos 2446), (Sat.Literal.pos 2445)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_3 s)

theorem counter_249_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446)) := by
  exact counter_gate s 248 3 (assignment s)
    (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446)
    rfl (rfl) rfl (rfl)

theorem clause_8797 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2447), (Sat.Literal.pos 2456)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446))
    [(Sat.Literal.neg 2447), (Sat.Literal.pos 2456)] [(Sat.Literal.neg 2447), (Sat.Literal.pos 2456)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_4 s)

theorem clause_8798 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2446), (Sat.Literal.pos 2456)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2446), (Sat.Literal.pos 2456)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2446), (Sat.Literal.pos 2456)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_4 s)

theorem clause_8799 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446))
    [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_4 s)

theorem clause_8800 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 2446)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2456) (Sat.Literal.pos 2447) (Sat.Literal.pos 248) (Sat.Literal.pos 2446))
    [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 2446)] [(Sat.Literal.neg 2456), (Sat.Literal.pos 2447), (Sat.Literal.pos 2446)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_4 s)

theorem counter_249_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447)) := by
  exact counter_gate s 248 4 (assignment s)
    (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447)
    rfl (rfl) rfl (rfl)

theorem clause_8801 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2448), (Sat.Literal.pos 2457)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447))
    [(Sat.Literal.neg 2448), (Sat.Literal.pos 2457)] [(Sat.Literal.neg 2448), (Sat.Literal.pos 2457)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_5 s)

theorem clause_8802 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2447), (Sat.Literal.pos 2457)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2447), (Sat.Literal.pos 2457)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2447), (Sat.Literal.pos 2457)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_5 s)

theorem clause_8803 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447))
    [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_5 s)

theorem clause_8804 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 2447)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2457) (Sat.Literal.pos 2448) (Sat.Literal.pos 248) (Sat.Literal.pos 2447))
    [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 2447)] [(Sat.Literal.neg 2457), (Sat.Literal.pos 2448), (Sat.Literal.pos 2447)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_5 s)

theorem counter_249_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448)) := by
  exact counter_gate s 248 5 (assignment s)
    (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448)
    rfl (rfl) rfl (rfl)

theorem clause_8805 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2449), (Sat.Literal.pos 2458)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448))
    [(Sat.Literal.neg 2449), (Sat.Literal.pos 2458)] [(Sat.Literal.neg 2449), (Sat.Literal.pos 2458)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_6 s)

theorem clause_8806 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2448), (Sat.Literal.pos 2458)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2448), (Sat.Literal.pos 2458)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2448), (Sat.Literal.pos 2458)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_6 s)

theorem clause_8807 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448))
    [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_6 s)

theorem clause_8808 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 2448)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2458) (Sat.Literal.pos 2449) (Sat.Literal.pos 248) (Sat.Literal.pos 2448))
    [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 2448)] [(Sat.Literal.neg 2458), (Sat.Literal.pos 2449), (Sat.Literal.pos 2448)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_6 s)

theorem counter_249_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449)) := by
  exact counter_gate s 248 6 (assignment s)
    (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449)
    rfl (rfl) rfl (rfl)

theorem clause_8809 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2450), (Sat.Literal.pos 2459)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449))
    [(Sat.Literal.neg 2450), (Sat.Literal.pos 2459)] [(Sat.Literal.neg 2450), (Sat.Literal.pos 2459)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_7 s)

theorem clause_8810 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2449), (Sat.Literal.pos 2459)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2449), (Sat.Literal.pos 2459)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2449), (Sat.Literal.pos 2459)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_7 s)

theorem clause_8811 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449))
    [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_7 s)

theorem clause_8812 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 2449)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2459) (Sat.Literal.pos 2450) (Sat.Literal.pos 248) (Sat.Literal.pos 2449))
    [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 2449)] [(Sat.Literal.neg 2459), (Sat.Literal.pos 2450), (Sat.Literal.pos 2449)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_7 s)

theorem counter_249_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450)) := by
  exact counter_gate s 248 7 (assignment s)
    (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450)
    rfl (rfl) rfl (rfl)

theorem clause_8813 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2451), (Sat.Literal.pos 2460)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450))
    [(Sat.Literal.neg 2451), (Sat.Literal.pos 2460)] [(Sat.Literal.neg 2451), (Sat.Literal.pos 2460)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_8 s)

theorem clause_8814 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2450), (Sat.Literal.pos 2460)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2450), (Sat.Literal.pos 2460)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2450), (Sat.Literal.pos 2460)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_8 s)

theorem clause_8815 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450))
    [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_8 s)

theorem clause_8816 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 2450)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2460) (Sat.Literal.pos 2451) (Sat.Literal.pos 248) (Sat.Literal.pos 2450))
    [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 2450)] [(Sat.Literal.neg 2460), (Sat.Literal.pos 2451), (Sat.Literal.pos 2450)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_8 s)

theorem counter_249_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451)) := by
  exact counter_gate s 248 8 (assignment s)
    (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451)
    rfl (rfl) rfl (rfl)

theorem clause_8817 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2452), (Sat.Literal.pos 2461)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451))
    [(Sat.Literal.neg 2452), (Sat.Literal.pos 2461)] [(Sat.Literal.neg 2452), (Sat.Literal.pos 2461)] (List.Mem.head _) (by intro l hl; exact hl) (counter_249_9 s)

theorem clause_8818 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 248), (Sat.Literal.neg 2451), (Sat.Literal.pos 2461)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451))
    [(Sat.Literal.neg 248), (Sat.Literal.neg 2451), (Sat.Literal.pos 2461)] [(Sat.Literal.neg 248), (Sat.Literal.neg 2451), (Sat.Literal.pos 2461)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_249_9 s)

theorem clause_8819 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 248)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451))
    [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 248)] [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 248)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_249_9 s)

theorem clause_8820 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 2451)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2461) (Sat.Literal.pos 2452) (Sat.Literal.pos 248) (Sat.Literal.pos 2451))
    [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 2451)] [(Sat.Literal.neg 2461), (Sat.Literal.pos 2452), (Sat.Literal.pos 2451)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_249_9 s)

theorem counter_250_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256)) := by
  exact counter_gate s 249 0 (assignment s)
    (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 249).symm)

theorem clause_8821 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2453), (Sat.Literal.pos 2462)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2453), (Sat.Literal.pos 2462)] [(Sat.Literal.neg 2453), (Sat.Literal.pos 2462)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_1 s)

theorem clause_8822 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.pos 256), (Sat.Literal.pos 2462)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 249), (Sat.Literal.pos 256), (Sat.Literal.pos 2462)] [(Sat.Literal.neg 249), (Sat.Literal.pos 256), (Sat.Literal.pos 2462)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_1 s)

theorem clause_8823 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_1 s)

theorem clause_8824 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2462) (Sat.Literal.pos 2453) (Sat.Literal.pos 249) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2462), (Sat.Literal.pos 2453), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_1 s)

theorem counter_250_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453)) := by
  exact counter_gate s 249 1 (assignment s)
    (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453)
    rfl (rfl) rfl (rfl)

theorem clause_8825 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2454), (Sat.Literal.pos 2463)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453))
    [(Sat.Literal.neg 2454), (Sat.Literal.pos 2463)] [(Sat.Literal.neg 2454), (Sat.Literal.pos 2463)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_2 s)

theorem clause_8826 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2453), (Sat.Literal.pos 2463)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2453), (Sat.Literal.pos 2463)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2453), (Sat.Literal.pos 2463)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_2 s)

theorem clause_8827 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453))
    [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_2 s)

theorem clause_8828 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 2453)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2463) (Sat.Literal.pos 2454) (Sat.Literal.pos 249) (Sat.Literal.pos 2453))
    [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 2453)] [(Sat.Literal.neg 2463), (Sat.Literal.pos 2454), (Sat.Literal.pos 2453)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_2 s)

theorem counter_250_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454)) := by
  exact counter_gate s 249 2 (assignment s)
    (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454)
    rfl (rfl) rfl (rfl)

theorem clause_8829 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2455), (Sat.Literal.pos 2464)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454))
    [(Sat.Literal.neg 2455), (Sat.Literal.pos 2464)] [(Sat.Literal.neg 2455), (Sat.Literal.pos 2464)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_3 s)

theorem clause_8830 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2454), (Sat.Literal.pos 2464)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2454), (Sat.Literal.pos 2464)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2454), (Sat.Literal.pos 2464)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_3 s)

theorem clause_8831 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454))
    [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_3 s)

theorem clause_8832 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 2454)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2464) (Sat.Literal.pos 2455) (Sat.Literal.pos 249) (Sat.Literal.pos 2454))
    [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 2454)] [(Sat.Literal.neg 2464), (Sat.Literal.pos 2455), (Sat.Literal.pos 2454)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_3 s)

theorem counter_250_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455)) := by
  exact counter_gate s 249 3 (assignment s)
    (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455)
    rfl (rfl) rfl (rfl)

theorem clause_8833 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2456), (Sat.Literal.pos 2465)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455))
    [(Sat.Literal.neg 2456), (Sat.Literal.pos 2465)] [(Sat.Literal.neg 2456), (Sat.Literal.pos 2465)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_4 s)

theorem clause_8834 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2455), (Sat.Literal.pos 2465)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2455), (Sat.Literal.pos 2465)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2455), (Sat.Literal.pos 2465)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_4 s)

theorem clause_8835 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455))
    [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_4 s)

theorem clause_8836 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 2455)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2465) (Sat.Literal.pos 2456) (Sat.Literal.pos 249) (Sat.Literal.pos 2455))
    [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 2455)] [(Sat.Literal.neg 2465), (Sat.Literal.pos 2456), (Sat.Literal.pos 2455)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_4 s)

theorem counter_250_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456)) := by
  exact counter_gate s 249 4 (assignment s)
    (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456)
    rfl (rfl) rfl (rfl)

theorem clause_8837 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2457), (Sat.Literal.pos 2466)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456))
    [(Sat.Literal.neg 2457), (Sat.Literal.pos 2466)] [(Sat.Literal.neg 2457), (Sat.Literal.pos 2466)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_5 s)

theorem clause_8838 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2456), (Sat.Literal.pos 2466)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2456), (Sat.Literal.pos 2466)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2456), (Sat.Literal.pos 2466)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_5 s)

theorem clause_8839 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456))
    [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_5 s)

theorem clause_8840 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 2456)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2466) (Sat.Literal.pos 2457) (Sat.Literal.pos 249) (Sat.Literal.pos 2456))
    [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 2456)] [(Sat.Literal.neg 2466), (Sat.Literal.pos 2457), (Sat.Literal.pos 2456)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_5 s)

theorem counter_250_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457)) := by
  exact counter_gate s 249 5 (assignment s)
    (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457)
    rfl (rfl) rfl (rfl)

theorem clause_8841 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2458), (Sat.Literal.pos 2467)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457))
    [(Sat.Literal.neg 2458), (Sat.Literal.pos 2467)] [(Sat.Literal.neg 2458), (Sat.Literal.pos 2467)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_6 s)

theorem clause_8842 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2457), (Sat.Literal.pos 2467)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2457), (Sat.Literal.pos 2467)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2457), (Sat.Literal.pos 2467)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_6 s)

theorem clause_8843 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457))
    [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_6 s)

theorem clause_8844 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 2457)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2467) (Sat.Literal.pos 2458) (Sat.Literal.pos 249) (Sat.Literal.pos 2457))
    [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 2457)] [(Sat.Literal.neg 2467), (Sat.Literal.pos 2458), (Sat.Literal.pos 2457)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_6 s)

theorem counter_250_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458)) := by
  exact counter_gate s 249 6 (assignment s)
    (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458)
    rfl (rfl) rfl (rfl)

theorem clause_8845 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2459), (Sat.Literal.pos 2468)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458))
    [(Sat.Literal.neg 2459), (Sat.Literal.pos 2468)] [(Sat.Literal.neg 2459), (Sat.Literal.pos 2468)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_7 s)

theorem clause_8846 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2458), (Sat.Literal.pos 2468)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2458), (Sat.Literal.pos 2468)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2458), (Sat.Literal.pos 2468)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_7 s)

theorem clause_8847 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458))
    [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_7 s)

theorem clause_8848 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 2458)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2468) (Sat.Literal.pos 2459) (Sat.Literal.pos 249) (Sat.Literal.pos 2458))
    [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 2458)] [(Sat.Literal.neg 2468), (Sat.Literal.pos 2459), (Sat.Literal.pos 2458)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_7 s)

theorem counter_250_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459)) := by
  exact counter_gate s 249 7 (assignment s)
    (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459)
    rfl (rfl) rfl (rfl)

theorem clause_8849 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2460), (Sat.Literal.pos 2469)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459))
    [(Sat.Literal.neg 2460), (Sat.Literal.pos 2469)] [(Sat.Literal.neg 2460), (Sat.Literal.pos 2469)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_8 s)

theorem clause_8850 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2459), (Sat.Literal.pos 2469)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2459), (Sat.Literal.pos 2469)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2459), (Sat.Literal.pos 2469)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_8 s)

theorem clause_8851 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459))
    [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_8 s)

theorem clause_8852 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 2459)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2469) (Sat.Literal.pos 2460) (Sat.Literal.pos 249) (Sat.Literal.pos 2459))
    [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 2459)] [(Sat.Literal.neg 2469), (Sat.Literal.pos 2460), (Sat.Literal.pos 2459)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_8 s)

theorem counter_250_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460)) := by
  exact counter_gate s 249 8 (assignment s)
    (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460)
    rfl (rfl) rfl (rfl)

theorem clause_8853 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2461), (Sat.Literal.pos 2470)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460))
    [(Sat.Literal.neg 2461), (Sat.Literal.pos 2470)] [(Sat.Literal.neg 2461), (Sat.Literal.pos 2470)] (List.Mem.head _) (by intro l hl; exact hl) (counter_250_9 s)

theorem clause_8854 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 249), (Sat.Literal.neg 2460), (Sat.Literal.pos 2470)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460))
    [(Sat.Literal.neg 249), (Sat.Literal.neg 2460), (Sat.Literal.pos 2470)] [(Sat.Literal.neg 249), (Sat.Literal.neg 2460), (Sat.Literal.pos 2470)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_250_9 s)

theorem clause_8855 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 249)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460))
    [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 249)] [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 249)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_250_9 s)

theorem clause_8856 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 2460)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2470) (Sat.Literal.pos 2461) (Sat.Literal.pos 249) (Sat.Literal.pos 2460))
    [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 2460)] [(Sat.Literal.neg 2470), (Sat.Literal.pos 2461), (Sat.Literal.pos 2460)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_250_9 s)

theorem counter_251_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256)) := by
  exact counter_gate s 250 0 (assignment s)
    (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 250).symm)

theorem clause_8857 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2462), (Sat.Literal.pos 2471)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2462), (Sat.Literal.pos 2471)] [(Sat.Literal.neg 2462), (Sat.Literal.pos 2471)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_1 s)

theorem clause_8858 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.pos 256), (Sat.Literal.pos 2471)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 250), (Sat.Literal.pos 256), (Sat.Literal.pos 2471)] [(Sat.Literal.neg 250), (Sat.Literal.pos 256), (Sat.Literal.pos 2471)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_1 s)

theorem clause_8859 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_1 s)

theorem clause_8860 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2471) (Sat.Literal.pos 2462) (Sat.Literal.pos 250) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2471), (Sat.Literal.pos 2462), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_1 s)

theorem counter_251_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462)) := by
  exact counter_gate s 250 1 (assignment s)
    (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462)
    rfl (rfl) rfl (rfl)

theorem clause_8861 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2463), (Sat.Literal.pos 2472)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462))
    [(Sat.Literal.neg 2463), (Sat.Literal.pos 2472)] [(Sat.Literal.neg 2463), (Sat.Literal.pos 2472)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_2 s)

theorem clause_8862 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2462), (Sat.Literal.pos 2472)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2462), (Sat.Literal.pos 2472)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2462), (Sat.Literal.pos 2472)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_2 s)

theorem clause_8863 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462))
    [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_2 s)

theorem clause_8864 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 2462)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2472) (Sat.Literal.pos 2463) (Sat.Literal.pos 250) (Sat.Literal.pos 2462))
    [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 2462)] [(Sat.Literal.neg 2472), (Sat.Literal.pos 2463), (Sat.Literal.pos 2462)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_2 s)

theorem counter_251_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463)) := by
  exact counter_gate s 250 2 (assignment s)
    (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463)
    rfl (rfl) rfl (rfl)

theorem clause_8865 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2464), (Sat.Literal.pos 2473)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463))
    [(Sat.Literal.neg 2464), (Sat.Literal.pos 2473)] [(Sat.Literal.neg 2464), (Sat.Literal.pos 2473)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_3 s)

theorem clause_8866 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2463), (Sat.Literal.pos 2473)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2463), (Sat.Literal.pos 2473)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2463), (Sat.Literal.pos 2473)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_3 s)

theorem clause_8867 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463))
    [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_3 s)

theorem clause_8868 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 2463)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2473) (Sat.Literal.pos 2464) (Sat.Literal.pos 250) (Sat.Literal.pos 2463))
    [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 2463)] [(Sat.Literal.neg 2473), (Sat.Literal.pos 2464), (Sat.Literal.pos 2463)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_3 s)

theorem counter_251_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464)) := by
  exact counter_gate s 250 3 (assignment s)
    (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464)
    rfl (rfl) rfl (rfl)

theorem clause_8869 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2465), (Sat.Literal.pos 2474)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464))
    [(Sat.Literal.neg 2465), (Sat.Literal.pos 2474)] [(Sat.Literal.neg 2465), (Sat.Literal.pos 2474)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_4 s)

theorem clause_8870 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2464), (Sat.Literal.pos 2474)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2464), (Sat.Literal.pos 2474)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2464), (Sat.Literal.pos 2474)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_4 s)

theorem clause_8871 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464))
    [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_4 s)

theorem clause_8872 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 2464)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2474) (Sat.Literal.pos 2465) (Sat.Literal.pos 250) (Sat.Literal.pos 2464))
    [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 2464)] [(Sat.Literal.neg 2474), (Sat.Literal.pos 2465), (Sat.Literal.pos 2464)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_4 s)

theorem counter_251_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465)) := by
  exact counter_gate s 250 4 (assignment s)
    (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465)
    rfl (rfl) rfl (rfl)

theorem clause_8873 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2466), (Sat.Literal.pos 2475)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465))
    [(Sat.Literal.neg 2466), (Sat.Literal.pos 2475)] [(Sat.Literal.neg 2466), (Sat.Literal.pos 2475)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_5 s)

theorem clause_8874 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2465), (Sat.Literal.pos 2475)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2465), (Sat.Literal.pos 2475)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2465), (Sat.Literal.pos 2475)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_5 s)

theorem clause_8875 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465))
    [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_5 s)

theorem clause_8876 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 2465)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2475) (Sat.Literal.pos 2466) (Sat.Literal.pos 250) (Sat.Literal.pos 2465))
    [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 2465)] [(Sat.Literal.neg 2475), (Sat.Literal.pos 2466), (Sat.Literal.pos 2465)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_5 s)

theorem counter_251_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466)) := by
  exact counter_gate s 250 5 (assignment s)
    (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466)
    rfl (rfl) rfl (rfl)

theorem clause_8877 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2467), (Sat.Literal.pos 2476)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466))
    [(Sat.Literal.neg 2467), (Sat.Literal.pos 2476)] [(Sat.Literal.neg 2467), (Sat.Literal.pos 2476)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_6 s)

theorem clause_8878 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2466), (Sat.Literal.pos 2476)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2466), (Sat.Literal.pos 2476)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2466), (Sat.Literal.pos 2476)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_6 s)

theorem clause_8879 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466))
    [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_6 s)

theorem clause_8880 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 2466)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2476) (Sat.Literal.pos 2467) (Sat.Literal.pos 250) (Sat.Literal.pos 2466))
    [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 2466)] [(Sat.Literal.neg 2476), (Sat.Literal.pos 2467), (Sat.Literal.pos 2466)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_6 s)

theorem counter_251_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467)) := by
  exact counter_gate s 250 6 (assignment s)
    (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467)
    rfl (rfl) rfl (rfl)

theorem clause_8881 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2468), (Sat.Literal.pos 2477)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467))
    [(Sat.Literal.neg 2468), (Sat.Literal.pos 2477)] [(Sat.Literal.neg 2468), (Sat.Literal.pos 2477)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_7 s)

theorem clause_8882 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2467), (Sat.Literal.pos 2477)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2467), (Sat.Literal.pos 2477)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2467), (Sat.Literal.pos 2477)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_7 s)

theorem clause_8883 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467))
    [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_7 s)

theorem clause_8884 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 2467)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2477) (Sat.Literal.pos 2468) (Sat.Literal.pos 250) (Sat.Literal.pos 2467))
    [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 2467)] [(Sat.Literal.neg 2477), (Sat.Literal.pos 2468), (Sat.Literal.pos 2467)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_7 s)

theorem counter_251_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468)) := by
  exact counter_gate s 250 7 (assignment s)
    (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468)
    rfl (rfl) rfl (rfl)

theorem clause_8885 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2469), (Sat.Literal.pos 2478)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468))
    [(Sat.Literal.neg 2469), (Sat.Literal.pos 2478)] [(Sat.Literal.neg 2469), (Sat.Literal.pos 2478)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_8 s)

theorem clause_8886 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2468), (Sat.Literal.pos 2478)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2468), (Sat.Literal.pos 2478)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2468), (Sat.Literal.pos 2478)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_8 s)

theorem clause_8887 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468))
    [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_8 s)

theorem clause_8888 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 2468)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2478) (Sat.Literal.pos 2469) (Sat.Literal.pos 250) (Sat.Literal.pos 2468))
    [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 2468)] [(Sat.Literal.neg 2478), (Sat.Literal.pos 2469), (Sat.Literal.pos 2468)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_8 s)

theorem counter_251_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469)) := by
  exact counter_gate s 250 8 (assignment s)
    (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469)
    rfl (rfl) rfl (rfl)

theorem clause_8889 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2470), (Sat.Literal.pos 2479)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469))
    [(Sat.Literal.neg 2470), (Sat.Literal.pos 2479)] [(Sat.Literal.neg 2470), (Sat.Literal.pos 2479)] (List.Mem.head _) (by intro l hl; exact hl) (counter_251_9 s)

theorem clause_8890 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 250), (Sat.Literal.neg 2469), (Sat.Literal.pos 2479)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469))
    [(Sat.Literal.neg 250), (Sat.Literal.neg 2469), (Sat.Literal.pos 2479)] [(Sat.Literal.neg 250), (Sat.Literal.neg 2469), (Sat.Literal.pos 2479)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_251_9 s)

theorem clause_8891 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 250)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469))
    [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 250)] [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 250)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_251_9 s)

theorem clause_8892 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 2469)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2479) (Sat.Literal.pos 2470) (Sat.Literal.pos 250) (Sat.Literal.pos 2469))
    [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 2469)] [(Sat.Literal.neg 2479), (Sat.Literal.pos 2470), (Sat.Literal.pos 2469)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_251_9 s)

theorem counter_252_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256)) := by
  exact counter_gate s 251 0 (assignment s)
    (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 251).symm)

theorem clause_8893 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2471), (Sat.Literal.pos 2480)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2471), (Sat.Literal.pos 2480)] [(Sat.Literal.neg 2471), (Sat.Literal.pos 2480)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_1 s)

theorem clause_8894 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.pos 256), (Sat.Literal.pos 2480)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 251), (Sat.Literal.pos 256), (Sat.Literal.pos 2480)] [(Sat.Literal.neg 251), (Sat.Literal.pos 256), (Sat.Literal.pos 2480)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_1 s)

theorem clause_8895 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_1 s)

theorem clause_8896 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2480) (Sat.Literal.pos 2471) (Sat.Literal.pos 251) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2480), (Sat.Literal.pos 2471), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_1 s)

theorem counter_252_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471)) := by
  exact counter_gate s 251 1 (assignment s)
    (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471)
    rfl (rfl) rfl (rfl)

theorem clause_8897 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2472), (Sat.Literal.pos 2481)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471))
    [(Sat.Literal.neg 2472), (Sat.Literal.pos 2481)] [(Sat.Literal.neg 2472), (Sat.Literal.pos 2481)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_2 s)

theorem clause_8898 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2471), (Sat.Literal.pos 2481)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2471), (Sat.Literal.pos 2481)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2471), (Sat.Literal.pos 2481)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_2 s)

theorem clause_8899 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471))
    [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_2 s)

theorem clause_8900 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 2471)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2481) (Sat.Literal.pos 2472) (Sat.Literal.pos 251) (Sat.Literal.pos 2471))
    [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 2471)] [(Sat.Literal.neg 2481), (Sat.Literal.pos 2472), (Sat.Literal.pos 2471)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_2 s)

theorem counter_252_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472)) := by
  exact counter_gate s 251 2 (assignment s)
    (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472)
    rfl (rfl) rfl (rfl)

theorem clause_8901 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2473), (Sat.Literal.pos 2482)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472))
    [(Sat.Literal.neg 2473), (Sat.Literal.pos 2482)] [(Sat.Literal.neg 2473), (Sat.Literal.pos 2482)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_3 s)

theorem clause_8902 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2472), (Sat.Literal.pos 2482)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2472), (Sat.Literal.pos 2482)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2472), (Sat.Literal.pos 2482)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_3 s)

theorem clause_8903 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472))
    [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_3 s)

theorem clause_8904 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 2472)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2482) (Sat.Literal.pos 2473) (Sat.Literal.pos 251) (Sat.Literal.pos 2472))
    [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 2472)] [(Sat.Literal.neg 2482), (Sat.Literal.pos 2473), (Sat.Literal.pos 2472)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_3 s)

theorem counter_252_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473)) := by
  exact counter_gate s 251 3 (assignment s)
    (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473)
    rfl (rfl) rfl (rfl)

theorem clause_8905 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2474), (Sat.Literal.pos 2483)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473))
    [(Sat.Literal.neg 2474), (Sat.Literal.pos 2483)] [(Sat.Literal.neg 2474), (Sat.Literal.pos 2483)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_4 s)

theorem clause_8906 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2473), (Sat.Literal.pos 2483)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2473), (Sat.Literal.pos 2483)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2473), (Sat.Literal.pos 2483)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_4 s)

theorem clause_8907 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473))
    [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_4 s)

theorem clause_8908 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 2473)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2483) (Sat.Literal.pos 2474) (Sat.Literal.pos 251) (Sat.Literal.pos 2473))
    [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 2473)] [(Sat.Literal.neg 2483), (Sat.Literal.pos 2474), (Sat.Literal.pos 2473)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_4 s)

theorem counter_252_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474)) := by
  exact counter_gate s 251 4 (assignment s)
    (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474)
    rfl (rfl) rfl (rfl)

theorem clause_8909 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2475), (Sat.Literal.pos 2484)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474))
    [(Sat.Literal.neg 2475), (Sat.Literal.pos 2484)] [(Sat.Literal.neg 2475), (Sat.Literal.pos 2484)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_5 s)

theorem clause_8910 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2474), (Sat.Literal.pos 2484)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2474), (Sat.Literal.pos 2484)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2474), (Sat.Literal.pos 2484)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_5 s)

theorem clause_8911 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474))
    [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_5 s)

theorem clause_8912 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 2474)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2484) (Sat.Literal.pos 2475) (Sat.Literal.pos 251) (Sat.Literal.pos 2474))
    [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 2474)] [(Sat.Literal.neg 2484), (Sat.Literal.pos 2475), (Sat.Literal.pos 2474)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_5 s)

theorem counter_252_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475)) := by
  exact counter_gate s 251 5 (assignment s)
    (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475)
    rfl (rfl) rfl (rfl)

theorem clause_8913 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2476), (Sat.Literal.pos 2485)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475))
    [(Sat.Literal.neg 2476), (Sat.Literal.pos 2485)] [(Sat.Literal.neg 2476), (Sat.Literal.pos 2485)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_6 s)

theorem clause_8914 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2475), (Sat.Literal.pos 2485)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2475), (Sat.Literal.pos 2485)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2475), (Sat.Literal.pos 2485)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_6 s)

theorem clause_8915 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475))
    [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_6 s)

theorem clause_8916 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 2475)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2485) (Sat.Literal.pos 2476) (Sat.Literal.pos 251) (Sat.Literal.pos 2475))
    [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 2475)] [(Sat.Literal.neg 2485), (Sat.Literal.pos 2476), (Sat.Literal.pos 2475)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_6 s)

theorem counter_252_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476)) := by
  exact counter_gate s 251 6 (assignment s)
    (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476)
    rfl (rfl) rfl (rfl)

theorem clause_8917 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2477), (Sat.Literal.pos 2486)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476))
    [(Sat.Literal.neg 2477), (Sat.Literal.pos 2486)] [(Sat.Literal.neg 2477), (Sat.Literal.pos 2486)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_7 s)

theorem clause_8918 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2476), (Sat.Literal.pos 2486)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2476), (Sat.Literal.pos 2486)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2476), (Sat.Literal.pos 2486)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_7 s)

theorem clause_8919 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476))
    [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_7 s)

theorem clause_8920 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 2476)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2486) (Sat.Literal.pos 2477) (Sat.Literal.pos 251) (Sat.Literal.pos 2476))
    [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 2476)] [(Sat.Literal.neg 2486), (Sat.Literal.pos 2477), (Sat.Literal.pos 2476)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_7 s)

theorem counter_252_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477)) := by
  exact counter_gate s 251 7 (assignment s)
    (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477)
    rfl (rfl) rfl (rfl)

theorem clause_8921 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2478), (Sat.Literal.pos 2487)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477))
    [(Sat.Literal.neg 2478), (Sat.Literal.pos 2487)] [(Sat.Literal.neg 2478), (Sat.Literal.pos 2487)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_8 s)

theorem clause_8922 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2477), (Sat.Literal.pos 2487)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2477), (Sat.Literal.pos 2487)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2477), (Sat.Literal.pos 2487)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_8 s)

theorem clause_8923 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477))
    [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_8 s)

theorem clause_8924 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 2477)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2487) (Sat.Literal.pos 2478) (Sat.Literal.pos 251) (Sat.Literal.pos 2477))
    [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 2477)] [(Sat.Literal.neg 2487), (Sat.Literal.pos 2478), (Sat.Literal.pos 2477)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_8 s)

theorem counter_252_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478)) := by
  exact counter_gate s 251 8 (assignment s)
    (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478)
    rfl (rfl) rfl (rfl)

theorem clause_8925 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2479), (Sat.Literal.pos 2488)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478))
    [(Sat.Literal.neg 2479), (Sat.Literal.pos 2488)] [(Sat.Literal.neg 2479), (Sat.Literal.pos 2488)] (List.Mem.head _) (by intro l hl; exact hl) (counter_252_9 s)

theorem clause_8926 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 251), (Sat.Literal.neg 2478), (Sat.Literal.pos 2488)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478))
    [(Sat.Literal.neg 251), (Sat.Literal.neg 2478), (Sat.Literal.pos 2488)] [(Sat.Literal.neg 251), (Sat.Literal.neg 2478), (Sat.Literal.pos 2488)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_252_9 s)

theorem clause_8927 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 251)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478))
    [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 251)] [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 251)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_252_9 s)

theorem clause_8928 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 2478)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2488) (Sat.Literal.pos 2479) (Sat.Literal.pos 251) (Sat.Literal.pos 2478))
    [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 2478)] [(Sat.Literal.neg 2488), (Sat.Literal.pos 2479), (Sat.Literal.pos 2478)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_252_9 s)

theorem counter_253_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256)) := by
  exact counter_gate s 252 0 (assignment s)
    (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 252).symm)

theorem clause_8929 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2480), (Sat.Literal.pos 2489)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2480), (Sat.Literal.pos 2489)] [(Sat.Literal.neg 2480), (Sat.Literal.pos 2489)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_1 s)

theorem clause_8930 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.pos 256), (Sat.Literal.pos 2489)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 252), (Sat.Literal.pos 256), (Sat.Literal.pos 2489)] [(Sat.Literal.neg 252), (Sat.Literal.pos 256), (Sat.Literal.pos 2489)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_1 s)

theorem clause_8931 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_1 s)

theorem clause_8932 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2489) (Sat.Literal.pos 2480) (Sat.Literal.pos 252) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2489), (Sat.Literal.pos 2480), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_1 s)

theorem counter_253_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480)) := by
  exact counter_gate s 252 1 (assignment s)
    (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480)
    rfl (rfl) rfl (rfl)

theorem clause_8933 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2481), (Sat.Literal.pos 2490)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480))
    [(Sat.Literal.neg 2481), (Sat.Literal.pos 2490)] [(Sat.Literal.neg 2481), (Sat.Literal.pos 2490)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_2 s)

theorem clause_8934 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2480), (Sat.Literal.pos 2490)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2480), (Sat.Literal.pos 2490)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2480), (Sat.Literal.pos 2490)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_2 s)

theorem clause_8935 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480))
    [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_2 s)

theorem clause_8936 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 2480)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2490) (Sat.Literal.pos 2481) (Sat.Literal.pos 252) (Sat.Literal.pos 2480))
    [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 2480)] [(Sat.Literal.neg 2490), (Sat.Literal.pos 2481), (Sat.Literal.pos 2480)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_2 s)

theorem counter_253_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481)) := by
  exact counter_gate s 252 2 (assignment s)
    (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481)
    rfl (rfl) rfl (rfl)

theorem clause_8937 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2482), (Sat.Literal.pos 2491)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481))
    [(Sat.Literal.neg 2482), (Sat.Literal.pos 2491)] [(Sat.Literal.neg 2482), (Sat.Literal.pos 2491)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_3 s)

theorem clause_8938 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2481), (Sat.Literal.pos 2491)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2481), (Sat.Literal.pos 2491)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2481), (Sat.Literal.pos 2491)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_3 s)

theorem clause_8939 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481))
    [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_3 s)

theorem clause_8940 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 2481)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2491) (Sat.Literal.pos 2482) (Sat.Literal.pos 252) (Sat.Literal.pos 2481))
    [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 2481)] [(Sat.Literal.neg 2491), (Sat.Literal.pos 2482), (Sat.Literal.pos 2481)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_3 s)

theorem counter_253_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482)) := by
  exact counter_gate s 252 3 (assignment s)
    (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482)
    rfl (rfl) rfl (rfl)

theorem clause_8941 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2483), (Sat.Literal.pos 2492)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482))
    [(Sat.Literal.neg 2483), (Sat.Literal.pos 2492)] [(Sat.Literal.neg 2483), (Sat.Literal.pos 2492)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_4 s)

theorem clause_8942 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2482), (Sat.Literal.pos 2492)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2482), (Sat.Literal.pos 2492)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2482), (Sat.Literal.pos 2492)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_4 s)

theorem clause_8943 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482))
    [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_4 s)

theorem clause_8944 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 2482)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2492) (Sat.Literal.pos 2483) (Sat.Literal.pos 252) (Sat.Literal.pos 2482))
    [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 2482)] [(Sat.Literal.neg 2492), (Sat.Literal.pos 2483), (Sat.Literal.pos 2482)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_4 s)

theorem counter_253_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483)) := by
  exact counter_gate s 252 4 (assignment s)
    (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483)
    rfl (rfl) rfl (rfl)

theorem clause_8945 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2484), (Sat.Literal.pos 2493)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483))
    [(Sat.Literal.neg 2484), (Sat.Literal.pos 2493)] [(Sat.Literal.neg 2484), (Sat.Literal.pos 2493)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_5 s)

theorem clause_8946 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2483), (Sat.Literal.pos 2493)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2483), (Sat.Literal.pos 2493)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2483), (Sat.Literal.pos 2493)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_5 s)

theorem clause_8947 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483))
    [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_5 s)

theorem clause_8948 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 2483)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2493) (Sat.Literal.pos 2484) (Sat.Literal.pos 252) (Sat.Literal.pos 2483))
    [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 2483)] [(Sat.Literal.neg 2493), (Sat.Literal.pos 2484), (Sat.Literal.pos 2483)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_5 s)

theorem counter_253_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484)) := by
  exact counter_gate s 252 5 (assignment s)
    (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484)
    rfl (rfl) rfl (rfl)

theorem clause_8949 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2485), (Sat.Literal.pos 2494)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484))
    [(Sat.Literal.neg 2485), (Sat.Literal.pos 2494)] [(Sat.Literal.neg 2485), (Sat.Literal.pos 2494)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_6 s)

theorem clause_8950 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2484), (Sat.Literal.pos 2494)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2484), (Sat.Literal.pos 2494)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2484), (Sat.Literal.pos 2494)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_6 s)

theorem clause_8951 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484))
    [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_6 s)

theorem clause_8952 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 2484)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2494) (Sat.Literal.pos 2485) (Sat.Literal.pos 252) (Sat.Literal.pos 2484))
    [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 2484)] [(Sat.Literal.neg 2494), (Sat.Literal.pos 2485), (Sat.Literal.pos 2484)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_6 s)

theorem counter_253_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485)) := by
  exact counter_gate s 252 6 (assignment s)
    (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485)
    rfl (rfl) rfl (rfl)

theorem clause_8953 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2486), (Sat.Literal.pos 2495)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485))
    [(Sat.Literal.neg 2486), (Sat.Literal.pos 2495)] [(Sat.Literal.neg 2486), (Sat.Literal.pos 2495)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_7 s)

theorem clause_8954 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2485), (Sat.Literal.pos 2495)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2485), (Sat.Literal.pos 2495)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2485), (Sat.Literal.pos 2495)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_7 s)

theorem clause_8955 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485))
    [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_7 s)

theorem clause_8956 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 2485)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2495) (Sat.Literal.pos 2486) (Sat.Literal.pos 252) (Sat.Literal.pos 2485))
    [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 2485)] [(Sat.Literal.neg 2495), (Sat.Literal.pos 2486), (Sat.Literal.pos 2485)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_7 s)

theorem counter_253_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486)) := by
  exact counter_gate s 252 7 (assignment s)
    (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486)
    rfl (rfl) rfl (rfl)

theorem clause_8957 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2487), (Sat.Literal.pos 2496)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486))
    [(Sat.Literal.neg 2487), (Sat.Literal.pos 2496)] [(Sat.Literal.neg 2487), (Sat.Literal.pos 2496)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_8 s)

theorem clause_8958 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2486), (Sat.Literal.pos 2496)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2486), (Sat.Literal.pos 2496)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2486), (Sat.Literal.pos 2496)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_8 s)

theorem clause_8959 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486))
    [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_8 s)

theorem clause_8960 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 2486)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2496) (Sat.Literal.pos 2487) (Sat.Literal.pos 252) (Sat.Literal.pos 2486))
    [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 2486)] [(Sat.Literal.neg 2496), (Sat.Literal.pos 2487), (Sat.Literal.pos 2486)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_8 s)

theorem counter_253_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487)) := by
  exact counter_gate s 252 8 (assignment s)
    (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487)
    rfl (rfl) rfl (rfl)

theorem clause_8961 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2488), (Sat.Literal.pos 2497)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487))
    [(Sat.Literal.neg 2488), (Sat.Literal.pos 2497)] [(Sat.Literal.neg 2488), (Sat.Literal.pos 2497)] (List.Mem.head _) (by intro l hl; exact hl) (counter_253_9 s)

theorem clause_8962 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 252), (Sat.Literal.neg 2487), (Sat.Literal.pos 2497)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487))
    [(Sat.Literal.neg 252), (Sat.Literal.neg 2487), (Sat.Literal.pos 2497)] [(Sat.Literal.neg 252), (Sat.Literal.neg 2487), (Sat.Literal.pos 2497)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_253_9 s)

theorem clause_8963 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 252)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487))
    [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 252)] [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 252)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_253_9 s)

theorem clause_8964 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 2487)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2497) (Sat.Literal.pos 2488) (Sat.Literal.pos 252) (Sat.Literal.pos 2487))
    [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 2487)] [(Sat.Literal.neg 2497), (Sat.Literal.pos 2488), (Sat.Literal.pos 2487)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_253_9 s)

theorem counter_254_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256)) := by
  exact counter_gate s 253 0 (assignment s)
    (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 253).symm)

theorem clause_8965 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2489), (Sat.Literal.pos 2498)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2489), (Sat.Literal.pos 2498)] [(Sat.Literal.neg 2489), (Sat.Literal.pos 2498)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_1 s)

theorem clause_8966 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.pos 256), (Sat.Literal.pos 2498)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 253), (Sat.Literal.pos 256), (Sat.Literal.pos 2498)] [(Sat.Literal.neg 253), (Sat.Literal.pos 256), (Sat.Literal.pos 2498)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_1 s)

theorem clause_8967 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_1 s)

theorem clause_8968 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2498) (Sat.Literal.pos 2489) (Sat.Literal.pos 253) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2498), (Sat.Literal.pos 2489), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_1 s)

theorem counter_254_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489)) := by
  exact counter_gate s 253 1 (assignment s)
    (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489)
    rfl (rfl) rfl (rfl)

theorem clause_8969 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2490), (Sat.Literal.pos 2499)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489))
    [(Sat.Literal.neg 2490), (Sat.Literal.pos 2499)] [(Sat.Literal.neg 2490), (Sat.Literal.pos 2499)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_2 s)

theorem clause_8970 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2489), (Sat.Literal.pos 2499)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2489), (Sat.Literal.pos 2499)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2489), (Sat.Literal.pos 2499)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_2 s)

theorem clause_8971 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489))
    [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_2 s)

theorem clause_8972 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 2489)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2499) (Sat.Literal.pos 2490) (Sat.Literal.pos 253) (Sat.Literal.pos 2489))
    [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 2489)] [(Sat.Literal.neg 2499), (Sat.Literal.pos 2490), (Sat.Literal.pos 2489)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_2 s)

theorem counter_254_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490)) := by
  exact counter_gate s 253 2 (assignment s)
    (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490)
    rfl (rfl) rfl (rfl)

theorem clause_8973 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2491), (Sat.Literal.pos 2500)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490))
    [(Sat.Literal.neg 2491), (Sat.Literal.pos 2500)] [(Sat.Literal.neg 2491), (Sat.Literal.pos 2500)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_3 s)

theorem clause_8974 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2490), (Sat.Literal.pos 2500)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2490), (Sat.Literal.pos 2500)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2490), (Sat.Literal.pos 2500)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_3 s)

theorem clause_8975 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490))
    [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_3 s)

theorem clause_8976 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 2490)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2500) (Sat.Literal.pos 2491) (Sat.Literal.pos 253) (Sat.Literal.pos 2490))
    [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 2490)] [(Sat.Literal.neg 2500), (Sat.Literal.pos 2491), (Sat.Literal.pos 2490)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_3 s)

theorem counter_254_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491)) := by
  exact counter_gate s 253 3 (assignment s)
    (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491)
    rfl (rfl) rfl (rfl)

theorem clause_8977 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2492), (Sat.Literal.pos 2501)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491))
    [(Sat.Literal.neg 2492), (Sat.Literal.pos 2501)] [(Sat.Literal.neg 2492), (Sat.Literal.pos 2501)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_4 s)

theorem clause_8978 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2491), (Sat.Literal.pos 2501)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2491), (Sat.Literal.pos 2501)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2491), (Sat.Literal.pos 2501)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_4 s)

theorem clause_8979 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491))
    [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_4 s)

theorem clause_8980 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 2491)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2501) (Sat.Literal.pos 2492) (Sat.Literal.pos 253) (Sat.Literal.pos 2491))
    [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 2491)] [(Sat.Literal.neg 2501), (Sat.Literal.pos 2492), (Sat.Literal.pos 2491)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_4 s)

theorem counter_254_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492)) := by
  exact counter_gate s 253 4 (assignment s)
    (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492)
    rfl (rfl) rfl (rfl)

theorem clause_8981 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2493), (Sat.Literal.pos 2502)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492))
    [(Sat.Literal.neg 2493), (Sat.Literal.pos 2502)] [(Sat.Literal.neg 2493), (Sat.Literal.pos 2502)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_5 s)

theorem clause_8982 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2492), (Sat.Literal.pos 2502)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2492), (Sat.Literal.pos 2502)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2492), (Sat.Literal.pos 2502)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_5 s)

theorem clause_8983 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492))
    [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_5 s)

theorem clause_8984 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 2492)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2502) (Sat.Literal.pos 2493) (Sat.Literal.pos 253) (Sat.Literal.pos 2492))
    [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 2492)] [(Sat.Literal.neg 2502), (Sat.Literal.pos 2493), (Sat.Literal.pos 2492)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_5 s)

theorem counter_254_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493)) := by
  exact counter_gate s 253 5 (assignment s)
    (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493)
    rfl (rfl) rfl (rfl)

theorem clause_8985 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2494), (Sat.Literal.pos 2503)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493))
    [(Sat.Literal.neg 2494), (Sat.Literal.pos 2503)] [(Sat.Literal.neg 2494), (Sat.Literal.pos 2503)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_6 s)

theorem clause_8986 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2493), (Sat.Literal.pos 2503)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2493), (Sat.Literal.pos 2503)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2493), (Sat.Literal.pos 2503)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_6 s)

theorem clause_8987 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493))
    [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_6 s)

theorem clause_8988 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 2493)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2503) (Sat.Literal.pos 2494) (Sat.Literal.pos 253) (Sat.Literal.pos 2493))
    [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 2493)] [(Sat.Literal.neg 2503), (Sat.Literal.pos 2494), (Sat.Literal.pos 2493)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_6 s)

theorem counter_254_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494)) := by
  exact counter_gate s 253 6 (assignment s)
    (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494)
    rfl (rfl) rfl (rfl)

theorem clause_8989 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2495), (Sat.Literal.pos 2504)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494))
    [(Sat.Literal.neg 2495), (Sat.Literal.pos 2504)] [(Sat.Literal.neg 2495), (Sat.Literal.pos 2504)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_7 s)

theorem clause_8990 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2494), (Sat.Literal.pos 2504)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2494), (Sat.Literal.pos 2504)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2494), (Sat.Literal.pos 2504)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_7 s)

theorem clause_8991 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494))
    [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_7 s)

theorem clause_8992 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 2494)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2504) (Sat.Literal.pos 2495) (Sat.Literal.pos 253) (Sat.Literal.pos 2494))
    [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 2494)] [(Sat.Literal.neg 2504), (Sat.Literal.pos 2495), (Sat.Literal.pos 2494)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_7 s)

theorem counter_254_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495)) := by
  exact counter_gate s 253 7 (assignment s)
    (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495)
    rfl (rfl) rfl (rfl)

theorem clause_8993 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2496), (Sat.Literal.pos 2505)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495))
    [(Sat.Literal.neg 2496), (Sat.Literal.pos 2505)] [(Sat.Literal.neg 2496), (Sat.Literal.pos 2505)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_8 s)

theorem clause_8994 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2495), (Sat.Literal.pos 2505)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2495), (Sat.Literal.pos 2505)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2495), (Sat.Literal.pos 2505)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_8 s)

theorem clause_8995 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495))
    [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_8 s)

theorem clause_8996 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 2495)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2505) (Sat.Literal.pos 2496) (Sat.Literal.pos 253) (Sat.Literal.pos 2495))
    [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 2495)] [(Sat.Literal.neg 2505), (Sat.Literal.pos 2496), (Sat.Literal.pos 2495)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_8 s)

theorem counter_254_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496)) := by
  exact counter_gate s 253 8 (assignment s)
    (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496)
    rfl (rfl) rfl (rfl)

theorem clause_8997 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2497), (Sat.Literal.pos 2506)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496))
    [(Sat.Literal.neg 2497), (Sat.Literal.pos 2506)] [(Sat.Literal.neg 2497), (Sat.Literal.pos 2506)] (List.Mem.head _) (by intro l hl; exact hl) (counter_254_9 s)

theorem clause_8998 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 253), (Sat.Literal.neg 2496), (Sat.Literal.pos 2506)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496))
    [(Sat.Literal.neg 253), (Sat.Literal.neg 2496), (Sat.Literal.pos 2506)] [(Sat.Literal.neg 253), (Sat.Literal.neg 2496), (Sat.Literal.pos 2506)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_254_9 s)

theorem clause_8999 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 253)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496))
    [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 253)] [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 253)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_254_9 s)

theorem clause_9000 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 2496)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2506) (Sat.Literal.pos 2497) (Sat.Literal.pos 253) (Sat.Literal.pos 2496))
    [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 2496)] [(Sat.Literal.neg 2506), (Sat.Literal.pos 2497), (Sat.Literal.pos 2496)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_254_9 s)

theorem counter_255_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256)) := by
  exact counter_gate s 254 0 (assignment s)
    (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 254).symm)

theorem clause_9001 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2498), (Sat.Literal.pos 2507)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2498), (Sat.Literal.pos 2507)] [(Sat.Literal.neg 2498), (Sat.Literal.pos 2507)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_1 s)

theorem clause_9002 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.pos 256), (Sat.Literal.pos 2507)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 254), (Sat.Literal.pos 256), (Sat.Literal.pos 2507)] [(Sat.Literal.neg 254), (Sat.Literal.pos 256), (Sat.Literal.pos 2507)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_1 s)

theorem clause_9003 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_1 s)

theorem clause_9004 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2507) (Sat.Literal.pos 2498) (Sat.Literal.pos 254) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2507), (Sat.Literal.pos 2498), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_1 s)

theorem counter_255_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498)) := by
  exact counter_gate s 254 1 (assignment s)
    (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498)
    rfl (rfl) rfl (rfl)

theorem clause_9005 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2499), (Sat.Literal.pos 2508)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498))
    [(Sat.Literal.neg 2499), (Sat.Literal.pos 2508)] [(Sat.Literal.neg 2499), (Sat.Literal.pos 2508)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_2 s)

theorem clause_9006 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2498), (Sat.Literal.pos 2508)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2498), (Sat.Literal.pos 2508)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2498), (Sat.Literal.pos 2508)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_2 s)

theorem clause_9007 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498))
    [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_2 s)

theorem clause_9008 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 2498)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2508) (Sat.Literal.pos 2499) (Sat.Literal.pos 254) (Sat.Literal.pos 2498))
    [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 2498)] [(Sat.Literal.neg 2508), (Sat.Literal.pos 2499), (Sat.Literal.pos 2498)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_2 s)

theorem counter_255_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499)) := by
  exact counter_gate s 254 2 (assignment s)
    (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499)
    rfl (rfl) rfl (rfl)

theorem clause_9009 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2500), (Sat.Literal.pos 2509)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499))
    [(Sat.Literal.neg 2500), (Sat.Literal.pos 2509)] [(Sat.Literal.neg 2500), (Sat.Literal.pos 2509)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_3 s)

theorem clause_9010 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2499), (Sat.Literal.pos 2509)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2499), (Sat.Literal.pos 2509)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2499), (Sat.Literal.pos 2509)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_3 s)

theorem clause_9011 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499))
    [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_3 s)

theorem clause_9012 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 2499)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2509) (Sat.Literal.pos 2500) (Sat.Literal.pos 254) (Sat.Literal.pos 2499))
    [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 2499)] [(Sat.Literal.neg 2509), (Sat.Literal.pos 2500), (Sat.Literal.pos 2499)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_3 s)

theorem counter_255_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500)) := by
  exact counter_gate s 254 3 (assignment s)
    (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500)
    rfl (rfl) rfl (rfl)

theorem clause_9013 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2501), (Sat.Literal.pos 2510)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500))
    [(Sat.Literal.neg 2501), (Sat.Literal.pos 2510)] [(Sat.Literal.neg 2501), (Sat.Literal.pos 2510)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_4 s)

theorem clause_9014 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2500), (Sat.Literal.pos 2510)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2500), (Sat.Literal.pos 2510)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2500), (Sat.Literal.pos 2510)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_4 s)

theorem clause_9015 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500))
    [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_4 s)

theorem clause_9016 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 2500)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2510) (Sat.Literal.pos 2501) (Sat.Literal.pos 254) (Sat.Literal.pos 2500))
    [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 2500)] [(Sat.Literal.neg 2510), (Sat.Literal.pos 2501), (Sat.Literal.pos 2500)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_4 s)

theorem counter_255_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501)) := by
  exact counter_gate s 254 4 (assignment s)
    (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501)
    rfl (rfl) rfl (rfl)

theorem clause_9017 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2502), (Sat.Literal.pos 2511)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501))
    [(Sat.Literal.neg 2502), (Sat.Literal.pos 2511)] [(Sat.Literal.neg 2502), (Sat.Literal.pos 2511)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_5 s)

theorem clause_9018 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2501), (Sat.Literal.pos 2511)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2501), (Sat.Literal.pos 2511)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2501), (Sat.Literal.pos 2511)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_5 s)

theorem clause_9019 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501))
    [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_5 s)

theorem clause_9020 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 2501)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2511) (Sat.Literal.pos 2502) (Sat.Literal.pos 254) (Sat.Literal.pos 2501))
    [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 2501)] [(Sat.Literal.neg 2511), (Sat.Literal.pos 2502), (Sat.Literal.pos 2501)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_5 s)

theorem counter_255_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502)) := by
  exact counter_gate s 254 5 (assignment s)
    (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502)
    rfl (rfl) rfl (rfl)

theorem clause_9021 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2503), (Sat.Literal.pos 2512)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502))
    [(Sat.Literal.neg 2503), (Sat.Literal.pos 2512)] [(Sat.Literal.neg 2503), (Sat.Literal.pos 2512)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_6 s)

theorem clause_9022 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2502), (Sat.Literal.pos 2512)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2502), (Sat.Literal.pos 2512)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2502), (Sat.Literal.pos 2512)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_6 s)

theorem clause_9023 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502))
    [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_6 s)

theorem clause_9024 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 2502)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2512) (Sat.Literal.pos 2503) (Sat.Literal.pos 254) (Sat.Literal.pos 2502))
    [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 2502)] [(Sat.Literal.neg 2512), (Sat.Literal.pos 2503), (Sat.Literal.pos 2502)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_6 s)

theorem counter_255_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503)) := by
  exact counter_gate s 254 6 (assignment s)
    (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503)
    rfl (rfl) rfl (rfl)

theorem clause_9025 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2504), (Sat.Literal.pos 2513)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503))
    [(Sat.Literal.neg 2504), (Sat.Literal.pos 2513)] [(Sat.Literal.neg 2504), (Sat.Literal.pos 2513)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_7 s)

theorem clause_9026 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2503), (Sat.Literal.pos 2513)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2503), (Sat.Literal.pos 2513)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2503), (Sat.Literal.pos 2513)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_7 s)

theorem clause_9027 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503))
    [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_7 s)

theorem clause_9028 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 2503)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2513) (Sat.Literal.pos 2504) (Sat.Literal.pos 254) (Sat.Literal.pos 2503))
    [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 2503)] [(Sat.Literal.neg 2513), (Sat.Literal.pos 2504), (Sat.Literal.pos 2503)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_7 s)

theorem counter_255_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504)) := by
  exact counter_gate s 254 7 (assignment s)
    (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504)
    rfl (rfl) rfl (rfl)

theorem clause_9029 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2505), (Sat.Literal.pos 2514)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504))
    [(Sat.Literal.neg 2505), (Sat.Literal.pos 2514)] [(Sat.Literal.neg 2505), (Sat.Literal.pos 2514)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_8 s)

theorem clause_9030 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2504), (Sat.Literal.pos 2514)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2504), (Sat.Literal.pos 2514)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2504), (Sat.Literal.pos 2514)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_8 s)

theorem clause_9031 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504))
    [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_8 s)

theorem clause_9032 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 2504)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2514) (Sat.Literal.pos 2505) (Sat.Literal.pos 254) (Sat.Literal.pos 2504))
    [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 2504)] [(Sat.Literal.neg 2514), (Sat.Literal.pos 2505), (Sat.Literal.pos 2504)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_8 s)

theorem counter_255_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505)) := by
  exact counter_gate s 254 8 (assignment s)
    (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505)
    rfl (rfl) rfl (rfl)

theorem clause_9033 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2506), (Sat.Literal.pos 2515)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505))
    [(Sat.Literal.neg 2506), (Sat.Literal.pos 2515)] [(Sat.Literal.neg 2506), (Sat.Literal.pos 2515)] (List.Mem.head _) (by intro l hl; exact hl) (counter_255_9 s)

theorem clause_9034 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 254), (Sat.Literal.neg 2505), (Sat.Literal.pos 2515)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505))
    [(Sat.Literal.neg 254), (Sat.Literal.neg 2505), (Sat.Literal.pos 2515)] [(Sat.Literal.neg 254), (Sat.Literal.neg 2505), (Sat.Literal.pos 2515)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_255_9 s)

theorem clause_9035 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 254)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505))
    [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 254)] [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 254)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_255_9 s)

theorem clause_9036 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 2505)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2515) (Sat.Literal.pos 2506) (Sat.Literal.pos 254) (Sat.Literal.pos 2505))
    [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 2505)] [(Sat.Literal.neg 2515), (Sat.Literal.pos 2506), (Sat.Literal.pos 2505)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_255_9 s)

theorem counter_256_1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256)) := by
  exact counter_gate s 255 0 (assignment s)
    (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256)
    rfl (rfl) rfl ((count_zero s 255).symm)

theorem clause_9037 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2507), (Sat.Literal.pos 2516)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2507), (Sat.Literal.pos 2516)] [(Sat.Literal.neg 2507), (Sat.Literal.pos 2516)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_1 s)

theorem clause_9038 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.pos 256), (Sat.Literal.pos 2516)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 255), (Sat.Literal.pos 256), (Sat.Literal.pos 2516)] [(Sat.Literal.neg 255), (Sat.Literal.pos 256), (Sat.Literal.pos 2516)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_1 s)

theorem clause_9039 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_1 s)

theorem clause_9040 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.neg 256)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2516) (Sat.Literal.pos 2507) (Sat.Literal.pos 255) (Sat.Literal.neg 256))
    [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.neg 256)] [(Sat.Literal.neg 2516), (Sat.Literal.pos 2507), (Sat.Literal.neg 256)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_1 s)

theorem counter_256_2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507)) := by
  exact counter_gate s 255 1 (assignment s)
    (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507)
    rfl (rfl) rfl (rfl)

theorem clause_9041 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2508), (Sat.Literal.pos 2517)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507))
    [(Sat.Literal.neg 2508), (Sat.Literal.pos 2517)] [(Sat.Literal.neg 2508), (Sat.Literal.pos 2517)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_2 s)

theorem clause_9042 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2507), (Sat.Literal.pos 2517)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2507), (Sat.Literal.pos 2517)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2507), (Sat.Literal.pos 2517)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_2 s)

theorem clause_9043 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507))
    [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_2 s)

theorem clause_9044 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 2507)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2517) (Sat.Literal.pos 2508) (Sat.Literal.pos 255) (Sat.Literal.pos 2507))
    [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 2507)] [(Sat.Literal.neg 2517), (Sat.Literal.pos 2508), (Sat.Literal.pos 2507)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_2 s)

theorem counter_256_3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508)) := by
  exact counter_gate s 255 2 (assignment s)
    (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508)
    rfl (rfl) rfl (rfl)

theorem clause_9045 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2509), (Sat.Literal.pos 2518)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508))
    [(Sat.Literal.neg 2509), (Sat.Literal.pos 2518)] [(Sat.Literal.neg 2509), (Sat.Literal.pos 2518)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_3 s)

theorem clause_9046 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2508), (Sat.Literal.pos 2518)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2508), (Sat.Literal.pos 2518)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2508), (Sat.Literal.pos 2518)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_3 s)

theorem clause_9047 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508))
    [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_3 s)

theorem clause_9048 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 2508)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2518) (Sat.Literal.pos 2509) (Sat.Literal.pos 255) (Sat.Literal.pos 2508))
    [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 2508)] [(Sat.Literal.neg 2518), (Sat.Literal.pos 2509), (Sat.Literal.pos 2508)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_3 s)

theorem counter_256_4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509)) := by
  exact counter_gate s 255 3 (assignment s)
    (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509)
    rfl (rfl) rfl (rfl)

theorem clause_9049 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2510), (Sat.Literal.pos 2519)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509))
    [(Sat.Literal.neg 2510), (Sat.Literal.pos 2519)] [(Sat.Literal.neg 2510), (Sat.Literal.pos 2519)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_4 s)

theorem clause_9050 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2509), (Sat.Literal.pos 2519)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2509), (Sat.Literal.pos 2519)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2509), (Sat.Literal.pos 2519)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_4 s)

theorem clause_9051 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509))
    [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_4 s)

theorem clause_9052 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 2509)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2519) (Sat.Literal.pos 2510) (Sat.Literal.pos 255) (Sat.Literal.pos 2509))
    [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 2509)] [(Sat.Literal.neg 2519), (Sat.Literal.pos 2510), (Sat.Literal.pos 2509)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_4 s)

theorem counter_256_5 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510)) := by
  exact counter_gate s 255 4 (assignment s)
    (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510)
    rfl (rfl) rfl (rfl)

theorem clause_9053 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2511), (Sat.Literal.pos 2520)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510))
    [(Sat.Literal.neg 2511), (Sat.Literal.pos 2520)] [(Sat.Literal.neg 2511), (Sat.Literal.pos 2520)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_5 s)

theorem clause_9054 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2510), (Sat.Literal.pos 2520)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2510), (Sat.Literal.pos 2520)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2510), (Sat.Literal.pos 2520)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_5 s)

theorem clause_9055 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510))
    [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_5 s)

theorem clause_9056 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 2510)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2520) (Sat.Literal.pos 2511) (Sat.Literal.pos 255) (Sat.Literal.pos 2510))
    [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 2510)] [(Sat.Literal.neg 2520), (Sat.Literal.pos 2511), (Sat.Literal.pos 2510)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_5 s)

theorem counter_256_6 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511)) := by
  exact counter_gate s 255 5 (assignment s)
    (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511)
    rfl (rfl) rfl (rfl)

theorem clause_9057 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2512), (Sat.Literal.pos 2521)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511))
    [(Sat.Literal.neg 2512), (Sat.Literal.pos 2521)] [(Sat.Literal.neg 2512), (Sat.Literal.pos 2521)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_6 s)

theorem clause_9058 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2511), (Sat.Literal.pos 2521)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2511), (Sat.Literal.pos 2521)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2511), (Sat.Literal.pos 2521)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_6 s)

theorem clause_9059 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511))
    [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_6 s)

theorem clause_9060 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 2511)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2521) (Sat.Literal.pos 2512) (Sat.Literal.pos 255) (Sat.Literal.pos 2511))
    [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 2511)] [(Sat.Literal.neg 2521), (Sat.Literal.pos 2512), (Sat.Literal.pos 2511)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_6 s)

theorem counter_256_7 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512)) := by
  exact counter_gate s 255 6 (assignment s)
    (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512)
    rfl (rfl) rfl (rfl)

theorem clause_9061 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2513), (Sat.Literal.pos 2522)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512))
    [(Sat.Literal.neg 2513), (Sat.Literal.pos 2522)] [(Sat.Literal.neg 2513), (Sat.Literal.pos 2522)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_7 s)

theorem clause_9062 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2512), (Sat.Literal.pos 2522)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2512), (Sat.Literal.pos 2522)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2512), (Sat.Literal.pos 2522)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_7 s)

theorem clause_9063 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512))
    [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_7 s)

theorem clause_9064 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 2512)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2522) (Sat.Literal.pos 2513) (Sat.Literal.pos 255) (Sat.Literal.pos 2512))
    [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 2512)] [(Sat.Literal.neg 2522), (Sat.Literal.pos 2513), (Sat.Literal.pos 2512)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_7 s)

theorem counter_256_8 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513)) := by
  exact counter_gate s 255 7 (assignment s)
    (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513)
    rfl (rfl) rfl (rfl)

theorem clause_9065 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2514), (Sat.Literal.pos 2523)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513))
    [(Sat.Literal.neg 2514), (Sat.Literal.pos 2523)] [(Sat.Literal.neg 2514), (Sat.Literal.pos 2523)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_8 s)

theorem clause_9066 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2513), (Sat.Literal.pos 2523)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2513), (Sat.Literal.pos 2523)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2513), (Sat.Literal.pos 2523)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_8 s)

theorem clause_9067 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513))
    [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_8 s)

theorem clause_9068 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 2513)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2523) (Sat.Literal.pos 2514) (Sat.Literal.pos 255) (Sat.Literal.pos 2513))
    [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 2513)] [(Sat.Literal.neg 2523), (Sat.Literal.pos 2514), (Sat.Literal.pos 2513)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_8 s)

theorem counter_256_9 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (counterCNF (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514)) := by
  exact counter_gate s 255 8 (assignment s)
    (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514)
    rfl (rfl) rfl (rfl)

theorem clause_9069 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2515), (Sat.Literal.pos 2524)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514))
    [(Sat.Literal.neg 2515), (Sat.Literal.pos 2524)] [(Sat.Literal.neg 2515), (Sat.Literal.pos 2524)] (List.Mem.head _) (by intro l hl; exact hl) (counter_256_9 s)

theorem clause_9070 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 255), (Sat.Literal.neg 2514), (Sat.Literal.pos 2524)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514))
    [(Sat.Literal.neg 255), (Sat.Literal.neg 2514), (Sat.Literal.pos 2524)] [(Sat.Literal.neg 255), (Sat.Literal.neg 2514), (Sat.Literal.pos 2524)] (List.Mem.tail _ (List.Mem.head _)) (by intro l hl; exact hl) (counter_256_9 s)

theorem clause_9071 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 255)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514))
    [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 255)] [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 255)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by intro l hl; exact hl) (counter_256_9 s)

theorem clause_9072 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 2514)] := by
  exact gate_clause (assignment s) (counterCNF (Sat.Literal.pos 2524) (Sat.Literal.pos 2515) (Sat.Literal.pos 255) (Sat.Literal.pos 2514))
    [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 2514)] [(Sat.Literal.neg 2524), (Sat.Literal.pos 2515), (Sat.Literal.pos 2514)] (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by intro l hl; exact hl) (counter_256_9 s)

#print axioms counter_227_3

end Crown.CertificateData
