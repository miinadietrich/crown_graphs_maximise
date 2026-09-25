import generated.ThreeClosureInitial
import generated.ThreeClosureDispatch0000
import generated.ThreeClosureDispatch0001
import generated.ThreeClosureDispatch0002
import generated.ThreeClosureDispatch0003
import generated.ThreeClosureDispatch0004
import generated.ThreeClosureDispatch0005
import generated.ThreeClosureDispatch0006
import generated.ThreeClosureDispatch0007
import generated.ThreeClosureDispatch0008
import generated.ThreeClosureDispatch0009
import generated.ThreeClosureDispatch0010
import generated.ThreeClosureDispatch0011
import generated.ThreeClosureDispatch0012
import generated.ThreeClosureDispatch0013
import generated.ThreeClosureDispatch0014
import generated.ThreeClosureDispatch0015
import generated.ThreeClosureDispatch0016
import generated.ThreeClosureDispatch0017
import generated.ThreeClosureDispatch0018
import generated.ThreeClosureDispatch0019
import generated.ThreeClosureDispatch0020
import generated.ThreeClosureDispatch0021
import generated.ThreeClosureDispatch0022
import generated.ThreeClosureDispatch0023
import generated.ThreeClosureDispatch0024
import generated.ThreeClosureDispatch0025
namespace Crown.ThreeClosure
open Crown.Ranks Crown.FiniteClosureChecks
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
theorem steps_checked : ∀ a, StepCheck rows owner support core nextHint lastHint 6 a := by
  intro a
  have ha := a.isLt
  by_cases h0 : a.val < 100
  ·
    have hi : a.val - 0 < 100 := by omega
    have he : rangeIndex 0 100 (by decide) ⟨a.val - 0, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0000 ⟨a.val - 0, hi⟩
  by_cases h1 : a.val < 200
  ·
    have hi : a.val - 100 < 100 := by omega
    have he : rangeIndex 100 100 (by decide) ⟨a.val - 100, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0001 ⟨a.val - 100, hi⟩
  by_cases h2 : a.val < 300
  ·
    have hi : a.val - 200 < 100 := by omega
    have he : rangeIndex 200 100 (by decide) ⟨a.val - 200, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0002 ⟨a.val - 200, hi⟩
  by_cases h3 : a.val < 400
  ·
    have hi : a.val - 300 < 100 := by omega
    have he : rangeIndex 300 100 (by decide) ⟨a.val - 300, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0003 ⟨a.val - 300, hi⟩
  by_cases h4 : a.val < 500
  ·
    have hi : a.val - 400 < 100 := by omega
    have he : rangeIndex 400 100 (by decide) ⟨a.val - 400, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0004 ⟨a.val - 400, hi⟩
  by_cases h5 : a.val < 600
  ·
    have hi : a.val - 500 < 100 := by omega
    have he : rangeIndex 500 100 (by decide) ⟨a.val - 500, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0005 ⟨a.val - 500, hi⟩
  by_cases h6 : a.val < 700
  ·
    have hi : a.val - 600 < 100 := by omega
    have he : rangeIndex 600 100 (by decide) ⟨a.val - 600, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0006 ⟨a.val - 600, hi⟩
  by_cases h7 : a.val < 800
  ·
    have hi : a.val - 700 < 100 := by omega
    have he : rangeIndex 700 100 (by decide) ⟨a.val - 700, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0007 ⟨a.val - 700, hi⟩
  by_cases h8 : a.val < 900
  ·
    have hi : a.val - 800 < 100 := by omega
    have he : rangeIndex 800 100 (by decide) ⟨a.val - 800, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0008 ⟨a.val - 800, hi⟩
  by_cases h9 : a.val < 1000
  ·
    have hi : a.val - 900 < 100 := by omega
    have he : rangeIndex 900 100 (by decide) ⟨a.val - 900, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0009 ⟨a.val - 900, hi⟩
  by_cases h10 : a.val < 1100
  ·
    have hi : a.val - 1000 < 100 := by omega
    have he : rangeIndex 1000 100 (by decide) ⟨a.val - 1000, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0010 ⟨a.val - 1000, hi⟩
  by_cases h11 : a.val < 1200
  ·
    have hi : a.val - 1100 < 100 := by omega
    have he : rangeIndex 1100 100 (by decide) ⟨a.val - 1100, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0011 ⟨a.val - 1100, hi⟩
  by_cases h12 : a.val < 1300
  ·
    have hi : a.val - 1200 < 100 := by omega
    have he : rangeIndex 1200 100 (by decide) ⟨a.val - 1200, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0012 ⟨a.val - 1200, hi⟩
  by_cases h13 : a.val < 1400
  ·
    have hi : a.val - 1300 < 100 := by omega
    have he : rangeIndex 1300 100 (by decide) ⟨a.val - 1300, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0013 ⟨a.val - 1300, hi⟩
  by_cases h14 : a.val < 1500
  ·
    have hi : a.val - 1400 < 100 := by omega
    have he : rangeIndex 1400 100 (by decide) ⟨a.val - 1400, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0014 ⟨a.val - 1400, hi⟩
  by_cases h15 : a.val < 1600
  ·
    have hi : a.val - 1500 < 100 := by omega
    have he : rangeIndex 1500 100 (by decide) ⟨a.val - 1500, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0015 ⟨a.val - 1500, hi⟩
  by_cases h16 : a.val < 1700
  ·
    have hi : a.val - 1600 < 100 := by omega
    have he : rangeIndex 1600 100 (by decide) ⟨a.val - 1600, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0016 ⟨a.val - 1600, hi⟩
  by_cases h17 : a.val < 1800
  ·
    have hi : a.val - 1700 < 100 := by omega
    have he : rangeIndex 1700 100 (by decide) ⟨a.val - 1700, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0017 ⟨a.val - 1700, hi⟩
  by_cases h18 : a.val < 1900
  ·
    have hi : a.val - 1800 < 100 := by omega
    have he : rangeIndex 1800 100 (by decide) ⟨a.val - 1800, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0018 ⟨a.val - 1800, hi⟩
  by_cases h19 : a.val < 2000
  ·
    have hi : a.val - 1900 < 100 := by omega
    have he : rangeIndex 1900 100 (by decide) ⟨a.val - 1900, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0019 ⟨a.val - 1900, hi⟩
  by_cases h20 : a.val < 2100
  ·
    have hi : a.val - 2000 < 100 := by omega
    have he : rangeIndex 2000 100 (by decide) ⟨a.val - 2000, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0020 ⟨a.val - 2000, hi⟩
  by_cases h21 : a.val < 2200
  ·
    have hi : a.val - 2100 < 100 := by omega
    have he : rangeIndex 2100 100 (by decide) ⟨a.val - 2100, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0021 ⟨a.val - 2100, hi⟩
  by_cases h22 : a.val < 2300
  ·
    have hi : a.val - 2200 < 100 := by omega
    have he : rangeIndex 2200 100 (by decide) ⟨a.val - 2200, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0022 ⟨a.val - 2200, hi⟩
  by_cases h23 : a.val < 2400
  ·
    have hi : a.val - 2300 < 100 := by omega
    have he : rangeIndex 2300 100 (by decide) ⟨a.val - 2300, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0023 ⟨a.val - 2300, hi⟩
  by_cases h24 : a.val < 2500
  ·
    have hi : a.val - 2400 < 100 := by omega
    have he : rangeIndex 2400 100 (by decide) ⟨a.val - 2400, hi⟩ = a := by
      apply Fin.ext
      dsimp [rangeIndex]
      omega
    exact he ▸ dispatch0024 ⟨a.val - 2400, hi⟩
  have hi : a.val - 2500 < 17 := by omega
  have he : rangeIndex 2500 17 (by decide) ⟨a.val - 2500, hi⟩ = a := by
    apply Fin.ext
    dsimp [rangeIndex]
    omega
  exact he ▸ dispatch0025 ⟨a.val - 2500, hi⟩
theorem certificate : IndexedFiniteClosure.Certificate rows owner support
    ((List.finRange 759).map core) 6 :=
  certificate_of_checks rows owner support core seed fixedHint nextHint lastHint 6
    seed_checked fixed_checked steps_checked
#print axioms steps_checked
#print axioms certificate
end Crown.ThreeClosure
