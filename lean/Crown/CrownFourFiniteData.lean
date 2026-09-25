import Crown.CrownFourFiniteCore
import Mathlib.Tactic.FinCases

namespace Crown.CrownFourFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem check_000 : ∀ d e f g h : Fin 4, Obstructed [0,0,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_000

theorem check_001 : ∀ d e f g h : Fin 4, Obstructed [0,0,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_001

theorem check_002 : ∀ d e f g h : Fin 4, Obstructed [0,0,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_002

theorem check_003 : ∀ d e f g h : Fin 4, Obstructed [0,0,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_003

theorem check_010 : ∀ d e f g h : Fin 4, Obstructed [0,1,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_010

theorem check_011 : ∀ d e f g h : Fin 4, Obstructed [0,1,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_011

theorem check_013 : ∀ d e f g h : Fin 4, Obstructed [0,1,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_013

theorem check_020 : ∀ d e f g h : Fin 4, Obstructed [0,2,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_020

theorem check_021 : ∀ d e f g h : Fin 4, Obstructed [0,2,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_021

theorem check_022 : ∀ d e f g h : Fin 4, Obstructed [0,2,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_022

theorem check_023 : ∀ d e f g h : Fin 4, Obstructed [0,2,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_023

theorem check_030 : ∀ d e f g h : Fin 4, Obstructed [0,3,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_030

theorem check_031 : ∀ d e f g h : Fin 4, Obstructed [0,3,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_031

theorem check_032 : ∀ d e f g h : Fin 4, Obstructed [0,3,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_032

theorem check_033 : ∀ d e f g h : Fin 4, Obstructed [0,3,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_033

theorem check_100 : ∀ d e f g h : Fin 4, Obstructed [1,0,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_100

theorem check_101 : ∀ d e f g h : Fin 4, Obstructed [1,0,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_101

theorem check_102 : ∀ d e f g h : Fin 4, Obstructed [1,0,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_102

theorem check_103 : ∀ d e f g h : Fin 4, Obstructed [1,0,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_103

theorem check_110 : ∀ d e f g h : Fin 4, Obstructed [1,1,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_110

theorem check_111 : ∀ d e f g h : Fin 4, Obstructed [1,1,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_111

theorem check_112 : ∀ d e f g h : Fin 4, Obstructed [1,1,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_112

theorem check_113 : ∀ d e f g h : Fin 4, Obstructed [1,1,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_113

theorem check_120 : ∀ d e f g h : Fin 4, Obstructed [1,2,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_120

theorem check_121 : ∀ d e f g h : Fin 4, Obstructed [1,2,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_121

theorem check_122 : ∀ d e f g h : Fin 4, Obstructed [1,2,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_122

theorem check_123 : ∀ d e f g h : Fin 4, Obstructed [1,2,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_123

theorem check_130 : ∀ d e f g h : Fin 4, Obstructed [1,3,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_130

theorem check_131 : ∀ d e f g h : Fin 4, Obstructed [1,3,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_131

theorem check_132 : ∀ d e f g h : Fin 4, Obstructed [1,3,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_132

theorem check_133 : ∀ d e f g h : Fin 4, Obstructed [1,3,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_133

theorem check_200 : ∀ d e f g h : Fin 4, Obstructed [2,0,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_200

theorem check_201 : ∀ d e f g h : Fin 4, Obstructed [2,0,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_201

theorem check_202 : ∀ d e f g h : Fin 4, Obstructed [2,0,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_202

theorem check_203 : ∀ d e f g h : Fin 4, Obstructed [2,0,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_203

theorem check_210 : ∀ d e f g h : Fin 4, Obstructed [2,1,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_210

theorem check_211 : ∀ d e f g h : Fin 4, Obstructed [2,1,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_211

theorem check_212 : ∀ d e f g h : Fin 4, Obstructed [2,1,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_212

theorem check_213 : ∀ d e f g h : Fin 4, Obstructed [2,1,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_213

theorem check_220 : ∀ d e f g h : Fin 4, Obstructed [2,2,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_220

theorem check_221 : ∀ d e f g h : Fin 4, Obstructed [2,2,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_221

theorem check_222 : ∀ d e f g h : Fin 4, Obstructed [2,2,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_222

theorem check_223 : ∀ d e f g h : Fin 4, Obstructed [2,2,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_223

theorem check_230 : ∀ d e f g h : Fin 4, Obstructed [2,3,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_230

theorem check_231 : ∀ d e f g h : Fin 4, Obstructed [2,3,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_231

theorem check_232 : ∀ d e f g h : Fin 4, Obstructed [2,3,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_232

theorem check_233 : ∀ d e f g h : Fin 4, Obstructed [2,3,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_233

theorem check_300 : ∀ d e f g h : Fin 4, Obstructed [3,0,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_300

theorem check_301 : ∀ d e f g h : Fin 4, Obstructed [3,0,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_301

theorem check_302 : ∀ d e f g h : Fin 4, Obstructed [3,0,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_302

theorem check_303 : ∀ d e f g h : Fin 4, Obstructed [3,0,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_303

theorem check_310 : ∀ d e f g h : Fin 4, Obstructed [3,1,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_310

theorem check_311 : ∀ d e f g h : Fin 4, Obstructed [3,1,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_311

theorem check_312 : ∀ d e f g h : Fin 4, Obstructed [3,1,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_312

theorem check_313 : ∀ d e f g h : Fin 4, Obstructed [3,1,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_313

theorem check_320 : ∀ d e f g h : Fin 4, Obstructed [3,2,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_320

theorem check_321 : ∀ d e f g h : Fin 4, Obstructed [3,2,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_321

theorem check_322 : ∀ d e f g h : Fin 4, Obstructed [3,2,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_322

theorem check_323 : ∀ d e f g h : Fin 4, Obstructed [3,2,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_323

theorem check_330 : ∀ d e f g h : Fin 4, Obstructed [3,3,0,d,e,f,g,h] := by
  decide +kernel

#print axioms check_330

theorem check_331 : ∀ d e f g h : Fin 4, Obstructed [3,3,1,d,e,f,g,h] := by
  decide +kernel

#print axioms check_331

theorem check_332 : ∀ d e f g h : Fin 4, Obstructed [3,3,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_332

theorem check_333 : ∀ d e f g h : Fin 4, Obstructed [3,3,3,d,e,f,g,h] := by
  decide +kernel

#print axioms check_333

theorem all_words : ∀ a b c d e f g h : Fin 4, Obstructed [a,b,c,d,e,f,g,h] := by
  intro a b c
  fin_cases a
  · fin_cases b
    · fin_cases c
      · exact check_000
      · exact check_001
      · exact check_002
      · exact check_003
    · fin_cases c
      · exact check_010
      · exact check_011
      · exact check_012
      · exact check_013
    · fin_cases c
      · exact check_020
      · exact check_021
      · exact check_022
      · exact check_023
    · fin_cases c
      · exact check_030
      · exact check_031
      · exact check_032
      · exact check_033
  · fin_cases b
    · fin_cases c
      · exact check_100
      · exact check_101
      · exact check_102
      · exact check_103
    · fin_cases c
      · exact check_110
      · exact check_111
      · exact check_112
      · exact check_113
    · fin_cases c
      · exact check_120
      · exact check_121
      · exact check_122
      · exact check_123
    · fin_cases c
      · exact check_130
      · exact check_131
      · exact check_132
      · exact check_133
  · fin_cases b
    · fin_cases c
      · exact check_200
      · exact check_201
      · exact check_202
      · exact check_203
    · fin_cases c
      · exact check_210
      · exact check_211
      · exact check_212
      · exact check_213
    · fin_cases c
      · exact check_220
      · exact check_221
      · exact check_222
      · exact check_223
    · fin_cases c
      · exact check_230
      · exact check_231
      · exact check_232
      · exact check_233
  · fin_cases b
    · fin_cases c
      · exact check_300
      · exact check_301
      · exact check_302
      · exact check_303
    · fin_cases c
      · exact check_310
      · exact check_311
      · exact check_312
      · exact check_313
    · fin_cases c
      · exact check_320
      · exact check_321
      · exact check_322
      · exact check_323
    · fin_cases c
      · exact check_330
      · exact check_331
      · exact check_332
      · exact check_333

#print axioms all_words

end Crown.CrownFourFinite
