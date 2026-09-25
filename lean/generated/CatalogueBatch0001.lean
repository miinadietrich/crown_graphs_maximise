import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0000 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0000 : List (Fin 4935) := templateData0000

noncomputable def witness0000 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 67 else if t 3 = 1 then 62 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 65 else if t 3 = 1 then 60 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 101) else if t 2 = 1 then (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 87) else (if t 3 = 0 then 75 else if t 3 = 1 then 73 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0000 pairing0000 template0000 witness0000

theorem coverage0000 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0000) (maskBits m))
    cores template0000 witness0000 := by
  rw [← coresFast_eq]
  exact fastCoverage0000

theorem coverageSize0000 : ∀ q : Pattern,
    (cores (witness0000 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0000 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0000
#print axioms coverageSize0000

noncomputable def pairing0001 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0001 : List (Fin 4935) := templateData0001

noncomputable def witness0001 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 201 else if t 3 = 1 then 157 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 199 else if t 3 = 1 then 140 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 173) else if t 2 = 1 then (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 143) else (if t 3 = 0 then 205 else if t 3 = 1 then 141 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0001 pairing0001 template0001 witness0001

theorem coverage0001 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0001) (maskBits m))
    cores template0001 witness0001 := by
  rw [← coresFast_eq]
  exact fastCoverage0001

theorem coverageSize0001 : ∀ q : Pattern,
    (cores (witness0001 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0001 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0001
#print axioms coverageSize0001

noncomputable def pairing0002 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0002 : List (Fin 4935) := templateData0002

noncomputable def witness0002 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 271 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 269 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 305) else if t 2 = 1 then (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 291) else (if t 3 = 0 then 279 else if t 3 = 1 then 277 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0002 pairing0002 template0002 witness0002

theorem coverage0002 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0002) (maskBits m))
    cores template0002 witness0002 := by
  rw [← coresFast_eq]
  exact fastCoverage0002

theorem coverageSize0002 : ∀ q : Pattern,
    (cores (witness0002 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0002 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0002
#print axioms coverageSize0002

noncomputable def pairing0003 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0003 : List (Fin 4935) := templateData0003

noncomputable def witness0003 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 402 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 400 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 374) else if t 2 = 1 then (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 343) else (if t 3 = 0 then 406 else if t 3 = 1 then 341 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0003 pairing0003 template0003 witness0003

theorem coverage0003 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0003) (maskBits m))
    cores template0003 witness0003 := by
  rw [← coresFast_eq]
  exact fastCoverage0003

theorem coverageSize0003 : ∀ q : Pattern,
    (cores (witness0003 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0003 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0003
#print axioms coverageSize0003

noncomputable def pairing0004 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0004 : List (Fin 4935) := templateData0004

noncomputable def witness0004 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else (if t 3 = 0 then 469 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 467 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 503) else if t 2 = 1 then (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 489) else (if t 3 = 0 then 477 else if t 3 = 1 then 475 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0004 pairing0004 template0004 witness0004

theorem coverage0004 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0004) (maskBits m))
    cores template0004 witness0004 := by
  rw [← coresFast_eq]
  exact fastCoverage0004

theorem coverageSize0004 : ∀ q : Pattern,
    (cores (witness0004 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0004 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0004
#print axioms coverageSize0004

noncomputable def pairing0005 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0005 : List (Fin 4935) := templateData0005

noncomputable def witness0005 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else (if t 3 = 0 then 597 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 595 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 569) else if t 2 = 1 then (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 538) else (if t 3 = 0 then 601 else if t 3 = 1 then 536 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0005 pairing0005 template0005 witness0005

theorem coverage0005 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0005) (maskBits m))
    cores template0005 witness0005 := by
  rw [← coresFast_eq]
  exact fastCoverage0005

theorem coverageSize0005 : ∀ q : Pattern,
    (cores (witness0005 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0005 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0005
#print axioms coverageSize0005

noncomputable def pairing0006 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0006 : List (Fin 4935) := templateData0006

noncomputable def witness0006 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 661 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 659 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 695) else if t 2 = 1 then (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 681) else (if t 3 = 0 then 669 else if t 3 = 1 then 667 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0006 pairing0006 template0006 witness0006

theorem coverage0006 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0006) (maskBits m))
    cores template0006 witness0006 := by
  rw [← coresFast_eq]
  exact fastCoverage0006

theorem coverageSize0006 : ∀ q : Pattern,
    (cores (witness0006 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0006 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0006
#print axioms coverageSize0006

noncomputable def pairing0007 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0007 : List (Fin 4935) := templateData0007

noncomputable def witness0007 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 786 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 784 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 758) else if t 2 = 1 then (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 726) else (if t 3 = 0 then 790 else if t 3 = 1 then 724 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0007 pairing0007 template0007 witness0007

theorem coverage0007 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0007) (maskBits m))
    cores template0007 witness0007 := by
  rw [← coresFast_eq]
  exact fastCoverage0007

theorem coverageSize0007 : ∀ q : Pattern,
    (cores (witness0007 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0007 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0007
#print axioms coverageSize0007

noncomputable def pairing0008 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0008 : List (Fin 4935) := templateData0008

noncomputable def witness0008 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 67 else if t 3 = 1 then 855 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 65 else if t 3 = 1 then 853 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 406) else if t 2 = 1 then (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 868) else (if t 3 = 0 then 75 else if t 3 = 1 then 859 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0008 pairing0008 template0008 witness0008

theorem coverage0008 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0008) (maskBits m))
    cores template0008 witness0008 := by
  rw [← coresFast_eq]
  exact fastCoverage0008

theorem coverageSize0008 : ∀ q : Pattern,
    (cores (witness0008 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0008 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0008
#print axioms coverageSize0008

noncomputable def pairing0009 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0009 : List (Fin 4935) := templateData0009

noncomputable def witness0009 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 900 else if t 3 = 1 then 158 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 898 else if t 3 = 1 then 142 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 893) else if t 2 = 1 then (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 141) else (if t 3 = 0 then 904 else if t 3 = 1 then 143 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0009 pairing0009 template0009 witness0009

theorem coverage0009 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0009) (maskBits m))
    cores template0009 witness0009 := by
  rw [← coresFast_eq]
  exact fastCoverage0009

theorem coverageSize0009 : ∀ q : Pattern,
    (cores (witness0009 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0009 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0009
#print axioms coverageSize0009

noncomputable def pairing0010 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0010 : List (Fin 4935) := templateData0010

noncomputable def witness0010 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 918 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 916 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 929) else if t 2 = 1 then (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 291) else (if t 3 = 0 then 922 else if t 3 = 1 then 277 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0010 pairing0010 template0010 witness0010

theorem coverage0010 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0010) (maskBits m))
    cores template0010 witness0010 := by
  rw [← coresFast_eq]
  exact fastCoverage0010

theorem coverageSize0010 : ∀ q : Pattern,
    (cores (witness0010 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0010 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0010
#print axioms coverageSize0010

noncomputable def pairing0011 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0011 : List (Fin 4935) := templateData0011

noncomputable def witness0011 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 104 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 100 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 374) else if t 2 = 1 then (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 964) else (if t 3 = 0 then 101 else if t 3 = 1 then 962 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0011 pairing0011 template0011 witness0011

theorem coverage0011 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0011) (maskBits m))
    cores template0011 witness0011 := by
  rw [← coresFast_eq]
  exact fastCoverage0011

theorem coverageSize0011 : ∀ q : Pattern,
    (cores (witness0011 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0011 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0011
#print axioms coverageSize0011

noncomputable def pairing0012 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0012 : List (Fin 4935) := templateData0012

noncomputable def witness0012 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else (if t 3 = 0 then 469 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 467 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 790) else if t 2 = 1 then (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1084) else (if t 3 = 0 then 477 else if t 3 = 1 then 1075 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0012 pairing0012 template0012 witness0012

theorem coverage0012 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0012) (maskBits m))
    cores template0012 witness0012 := by
  rw [← coresFast_eq]
  exact fastCoverage0012

theorem coverageSize0012 : ∀ q : Pattern,
    (cores (witness0012 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0012 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0012
#print axioms coverageSize0012

noncomputable def pairing0013 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0013 : List (Fin 4935) := templateData0013

noncomputable def witness0013 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else (if t 3 = 0 then 1116 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1114 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 1109) else if t 2 = 1 then (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 536) else (if t 3 = 0 then 1120 else if t 3 = 1 then 538 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0013 pairing0013 template0013 witness0013

theorem coverage0013 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0013) (maskBits m))
    cores template0013 witness0013 := by
  rw [← coresFast_eq]
  exact fastCoverage0013

theorem coverageSize0013 : ∀ q : Pattern,
    (cores (witness0013 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0013 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0013
#print axioms coverageSize0013

noncomputable def pairing0014 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0014 : List (Fin 4935) := templateData0014

noncomputable def witness0014 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 1134 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1132 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 1145) else if t 2 = 1 then (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 681) else (if t 3 = 0 then 1138 else if t 3 = 1 then 667 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0014 pairing0014 template0014 witness0014

theorem coverage0014 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0014) (maskBits m))
    cores template0014 witness0014 := by
  rw [← coresFast_eq]
  exact fastCoverage0014

theorem coverageSize0014 : ∀ q : Pattern,
    (cores (witness0014 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0014 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0014
#print axioms coverageSize0014

noncomputable def pairing0015 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0015 : List (Fin 4935) := templateData0015

noncomputable def witness0015 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 506 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 502 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 758) else if t 2 = 1 then (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1173) else (if t 3 = 0 then 503 else if t 3 = 1 then 1171 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0015 pairing0015 template0015 witness0015

theorem coverage0015 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0015) (maskBits m))
    cores template0015 witness0015 := by
  rw [← coresFast_eq]
  exact fastCoverage0015

theorem coverageSize0015 : ∀ q : Pattern,
    (cores (witness0015 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0015 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0015
#print axioms coverageSize0015

noncomputable def pairing0016 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0016 : List (Fin 4935) := templateData0016

noncomputable def witness0016 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 201 else if t 3 = 1 then 864 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 199 else if t 3 = 1 then 862 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 279) else if t 2 = 1 then (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 859) else (if t 3 = 0 then 205 else if t 3 = 1 then 868 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0016 pairing0016 template0016 witness0016

theorem coverage0016 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0016) (maskBits m))
    cores template0016 witness0016 := by
  rw [← coresFast_eq]
  exact fastCoverage0016

theorem coverageSize0016 : ∀ q : Pattern,
    (cores (witness0016 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0016 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0016
#print axioms coverageSize0016

noncomputable def pairing0017 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0017 : List (Fin 4935) := templateData0017

noncomputable def witness0017 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 900 else if t 3 = 1 then 94 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 898 else if t 3 = 1 then 86 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 922) else if t 2 = 1 then (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 73) else (if t 3 = 0 then 904 else if t 3 = 1 then 87 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0017 pairing0017 template0017 witness0017

theorem coverage0017 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0017) (maskBits m))
    cores template0017 witness0017 := by
  rw [← coresFast_eq]
  exact fastCoverage0017

theorem coverageSize0017 : ∀ q : Pattern,
    (cores (witness0017 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0017 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0017
#print axioms coverageSize0017

noncomputable def pairing0018 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0018 : List (Fin 4935) := templateData0018

noncomputable def witness0018 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 896 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 892 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 929) else if t 2 = 1 then (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 343) else (if t 3 = 0 then 893 else if t 3 = 1 then 341 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0018 pairing0018 template0018 witness0018

theorem coverage0018 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0018) (maskBits m))
    cores template0018 witness0018 := by
  rw [← coresFast_eq]
  exact fastCoverage0018

theorem coverageSize0018 : ∀ q : Pattern,
    (cores (witness0018 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0018 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0018
#print axioms coverageSize0018

noncomputable def pairing0019 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0019 : List (Fin 4935) := templateData0019

noncomputable def witness0019 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 179 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 172 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 305) else if t 2 = 1 then (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 964) else (if t 3 = 0 then 173 else if t 3 = 1 then 962 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0019 pairing0019 template0019 witness0019

theorem coverage0019 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0019) (maskBits m))
    cores template0019 witness0019 := by
  rw [← coresFast_eq]
  exact fastCoverage0019

theorem coverageSize0019 : ∀ q : Pattern,
    (cores (witness0019 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0019 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0019
#print axioms coverageSize0019

noncomputable def pairing0020 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0020 : List (Fin 4935) := templateData0020

noncomputable def witness0020 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else (if t 3 = 0 then 597 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 595 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 669) else if t 2 = 1 then (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1075) else (if t 3 = 0 then 601 else if t 3 = 1 then 1084 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0020 pairing0020 template0020 witness0020

theorem coverage0020 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0020) (maskBits m))
    cores template0020 witness0020 := by
  rw [← coresFast_eq]
  exact fastCoverage0020

theorem coverageSize0020 : ∀ q : Pattern,
    (cores (witness0020 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0020 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0020
#print axioms coverageSize0020

noncomputable def pairing0021 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0021 : List (Fin 4935) := templateData0021

noncomputable def witness0021 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else (if t 3 = 0 then 1116 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1114 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 1138) else if t 2 = 1 then (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 475) else (if t 3 = 0 then 1120 else if t 3 = 1 then 489 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0021 pairing0021 template0021 witness0021

theorem coverage0021 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0021) (maskBits m))
    cores template0021 witness0021 := by
  rw [← coresFast_eq]
  exact fastCoverage0021

theorem coverageSize0021 : ∀ q : Pattern,
    (cores (witness0021 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0021 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0021
#print axioms coverageSize0021

noncomputable def pairing0022 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0022 : List (Fin 4935) := templateData0022

noncomputable def witness0022 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 1112 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1108 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 1145) else if t 2 = 1 then (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 726) else (if t 3 = 0 then 1109 else if t 3 = 1 then 724 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0022 pairing0022 template0022 witness0022

theorem coverage0022 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0022) (maskBits m))
    cores template0022 witness0022 := by
  rw [← coresFast_eq]
  exact fastCoverage0022

theorem coverageSize0022 : ∀ q : Pattern,
    (cores (witness0022 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0022 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0022
#print axioms coverageSize0022

noncomputable def pairing0023 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0023 : List (Fin 4935) := templateData0023

noncomputable def witness0023 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 575 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 568 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 695) else if t 2 = 1 then (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1173) else (if t 3 = 0 then 569 else if t 3 = 1 then 1171 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0023 pairing0023 template0023 witness0023

theorem coverage0023 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0023) (maskBits m))
    cores template0023 witness0023 := by
  rw [← coresFast_eq]
  exact fastCoverage0023

theorem coverageSize0023 : ∀ q : Pattern,
    (cores (witness0023 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0023 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0023
#print axioms coverageSize0023

noncomputable def pairing0024 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0024 : List (Fin 4935) := templateData0024

noncomputable def witness0024 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 101) else if t 2 = 1 then (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1371) else (if t 3 = 0 then 1359 else if t 3 = 1 then 1357 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0024 pairing0024 template0024 witness0024

theorem coverage0024 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0024) (maskBits m))
    cores template0024 witness0024 := by
  rw [← coresFast_eq]
  exact fastCoverage0024

theorem coverageSize0024 : ∀ q : Pattern,
    (cores (witness0024 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0024 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0024
#print axioms coverageSize0024

noncomputable def pairing0025 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0025 : List (Fin 4935) := templateData0025

noncomputable def witness0025 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 173) else if t 2 = 1 then (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1415) else (if t 3 = 0 then 1453 else if t 3 = 1 then 1413 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0025 pairing0025 template0025 witness0025

theorem coverage0025 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0025) (maskBits m))
    cores template0025 witness0025 := by
  rw [← coresFast_eq]
  exact fastCoverage0025

theorem coverageSize0025 : ∀ q : Pattern,
    (cores (witness0025 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0025 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0025
#print axioms coverageSize0025

noncomputable def pairing0026 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0026 : List (Fin 4935) := templateData0026

noncomputable def witness0026 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 1478) else if t 2 = 1 then (if t 3 = 0 then 269 else if t 3 = 1 then 264 else 292) else (if t 3 = 0 then 279 else if t 3 = 1 then 277 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0026 pairing0026 template0026 witness0026

theorem coverage0026 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0026) (maskBits m))
    cores template0026 witness0026 := by
  rw [← coresFast_eq]
  exact fastCoverage0026

theorem coverageSize0026 : ∀ q : Pattern,
    (cores (witness0026 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0026 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0026
#print axioms coverageSize0026

noncomputable def pairing0027 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0027 : List (Fin 4935) := templateData0027

noncomputable def witness0027 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 1496) else if t 2 = 1 then (if t 3 = 0 then 400 else if t 3 = 1 then 340 else 344) else (if t 3 = 0 then 406 else if t 3 = 1 then 341 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0027 pairing0027 template0027 witness0027

theorem coverage0027 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0027) (maskBits m))
    cores template0027 witness0027 := by
  rw [← coresFast_eq]
  exact fastCoverage0027

theorem coverageSize0027 : ∀ q : Pattern,
    (cores (witness0027 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0027 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0027
#print axioms coverageSize0027

noncomputable def pairing0028 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0028 : List (Fin 4935) := templateData0028

noncomputable def witness0028 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else (if t 3 = 0 then 1519 else if t 3 = 1 then 1132 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 467 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1523) else if t 2 = 1 then (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 489) else (if t 3 = 0 then 477 else if t 3 = 1 then 475 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0028 pairing0028 template0028 witness0028

theorem coverage0028 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0028) (maskBits m))
    cores template0028 witness0028 := by
  rw [← coresFast_eq]
  exact fastCoverage0028

theorem coverageSize0028 : ∀ q : Pattern,
    (cores (witness0028 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0028 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0028
#print axioms coverageSize0028

noncomputable def pairing0029 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0029 : List (Fin 4935) := templateData0029

noncomputable def witness0029 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else (if t 3 = 0 then 1549 else if t 3 = 1 then 1108 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 595 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1538) else if t 2 = 1 then (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 538) else (if t 3 = 0 then 601 else if t 3 = 1 then 536 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0029 pairing0029 template0029 witness0029

theorem coverage0029 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0029) (maskBits m))
    cores template0029 witness0029 := by
  rw [← coresFast_eq]
  exact fastCoverage0029

theorem coverageSize0029 : ∀ q : Pattern,
    (cores (witness0029 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0029 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0029
#print axioms coverageSize0029

noncomputable def pairing0030 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0030 : List (Fin 4935) := templateData0030

noncomputable def witness0030 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 661 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 1071 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 67 else if t 3 = 1 then 62 else 95) else if t 2 = 1 then (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0030 pairing0030 template0030 witness0030

theorem coverage0030 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0030) (maskBits m))
    cores template0030 witness0030 := by
  rw [← coresFast_eq]
  exact fastCoverage0030

theorem coverageSize0030 : ∀ q : Pattern,
    (cores (witness0030 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0030 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0030
#print axioms coverageSize0030

noncomputable def pairing0031 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0031 : List (Fin 4935) := templateData0031

noncomputable def witness0031 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 786 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 1080 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 201 else if t 3 = 1 then 157 else 159) else if t 2 = 1 then (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0031 pairing0031 template0031 witness0031

theorem coverage0031 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0031) (maskBits m))
    cores template0031 witness0031 := by
  rw [← coresFast_eq]
  exact fastCoverage0031

theorem coverageSize0031 : ∀ q : Pattern,
    (cores (witness0031 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0031 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0031
#print axioms coverageSize0031

noncomputable def pairing0032 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0032 : List (Fin 4935) := templateData0032

noncomputable def witness0032 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 406) else if t 2 = 1 then (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1756) else (if t 3 = 0 then 1359 else if t 3 = 1 then 1750 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0032 pairing0032 template0032 witness0032

theorem coverage0032 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0032) (maskBits m))
    cores template0032 witness0032 := by
  rw [← coresFast_eq]
  exact fastCoverage0032

theorem coverageSize0032 : ∀ q : Pattern,
    (cores (witness0032 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0032 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0032
#print axioms coverageSize0032

noncomputable def pairing0033 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0033 : List (Fin 4935) := templateData0033

noncomputable def witness0033 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 893) else if t 2 = 1 then (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1413) else (if t 3 = 0 then 1780 else if t 3 = 1 then 1415 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0033 pairing0033 template0033 witness0033

theorem coverage0033 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0033) (maskBits m))
    cores template0033 witness0033 := by
  rw [← coresFast_eq]
  exact fastCoverage0033

theorem coverageSize0033 : ∀ q : Pattern,
    (cores (witness0033 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0033 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0033
#print axioms coverageSize0033

noncomputable def pairing0034 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0034 : List (Fin 4935) := templateData0034

noncomputable def witness0034 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 1790) else if t 2 = 1 then (if t 3 = 0 then 916 else if t 3 = 1 then 264 else 292) else (if t 3 = 0 then 922 else if t 3 = 1 then 277 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0034 pairing0034 template0034 witness0034

theorem coverage0034 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0034) (maskBits m))
    cores template0034 witness0034 := by
  rw [← coresFast_eq]
  exact fastCoverage0034

theorem coverageSize0034 : ∀ q : Pattern,
    (cores (witness0034 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0034 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0034
#print axioms coverageSize0034

noncomputable def pairing0035 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0035 : List (Fin 4935) := templateData0035

noncomputable def witness0035 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 1496) else if t 2 = 1 then (if t 3 = 0 then 100 else if t 3 = 1 then 961 else 965) else (if t 3 = 0 then 101 else if t 3 = 1 then 962 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0035 pairing0035 template0035 witness0035

theorem coverage0035 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0035) (maskBits m))
    cores template0035 witness0035 := by
  rw [← coresFast_eq]
  exact fastCoverage0035

theorem coverageSize0035 : ∀ q : Pattern,
    (cores (witness0035 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0035 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0035
#print axioms coverageSize0035

noncomputable def pairing0036 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0036 : List (Fin 4935) := templateData0036

noncomputable def witness0036 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else (if t 3 = 0 then 1519 else if t 3 = 1 then 659 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 467 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1084) else (if t 3 = 0 then 477 else if t 3 = 1 then 1075 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0036 pairing0036 template0036 witness0036

theorem coverage0036 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0036) (maskBits m))
    cores template0036 witness0036 := by
  rw [← coresFast_eq]
  exact fastCoverage0036

theorem coverageSize0036 : ∀ q : Pattern,
    (cores (witness0036 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0036 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0036
#print axioms coverageSize0036

noncomputable def pairing0037 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0037 : List (Fin 4935) := templateData0037

noncomputable def witness0037 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else (if t 3 = 0 then 1837 else if t 3 = 1 then 568 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1114 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1835) else if t 2 = 1 then (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 536) else (if t 3 = 0 then 1120 else if t 3 = 1 then 538 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0037 pairing0037 template0037 witness0037

theorem coverage0037 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0037) (maskBits m))
    cores template0037 witness0037 := by
  rw [← coresFast_eq]
  exact fastCoverage0037

theorem coverageSize0037 : ∀ q : Pattern,
    (cores (witness0037 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0037 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0037
#print axioms coverageSize0037

noncomputable def pairing0038 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0038 : List (Fin 4935) := templateData0038

noncomputable def witness0038 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 1134 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 464 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 67 else if t 3 = 1 then 855 else 878) else if t 2 = 1 then (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0038 pairing0038 template0038 witness0038

theorem coverage0038 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0038) (maskBits m))
    cores template0038 witness0038 := by
  rw [← coresFast_eq]
  exact fastCoverage0038

theorem coverageSize0038 : ∀ q : Pattern,
    (cores (witness0038 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0038 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0038
#print axioms coverageSize0038

noncomputable def pairing0039 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0039 : List (Fin 4935) := templateData0039

noncomputable def witness0039 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 506 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 496 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 900 else if t 3 = 1 then 158 else 159) else if t 2 = 1 then (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0039 pairing0039 template0039 witness0039

theorem coverage0039 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0039) (maskBits m))
    cores template0039 witness0039 := by
  rw [← coresFast_eq]
  exact fastCoverage0039

theorem coverageSize0039 : ∀ q : Pattern,
    (cores (witness0039 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0039 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0039
#print axioms coverageSize0039

end Crown.CertificateData
