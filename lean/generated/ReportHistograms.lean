import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
namespace Crown.ReportHistograms
/-! Equalities of the supplied report data only. These theorems do not assert
that executing either C++ program produces the report or prove feasibility. -/
def balanced6 : List Nat := [62716396, 9909762, 1900054, 330678, 65917, 17266, 8157, 11708, 7122, 2287, 1361, 568, 1584, 778, 262, 46, 258, 61, 1, 6, 7, 2, 0, 0, 62, 12, 2, 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem balanced6_length : balanced6.length = 61 := by decide +kernel
def balanced6_independent : List Nat := [62716396, 9909762, 1900054, 330678, 65917, 17266, 8157, 11708, 7122, 2287, 1361, 568, 1584, 778, 262, 46, 258, 61, 1, 6, 7, 2, 0, 0, 62, 12, 2, 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem balanced6_independent_length : balanced6_independent.length = 61 := by decide +kernel
def odd5 : List Nat := [3342105, 0, 23400, 0, 350, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem odd5_length : odd5.length = 61 := by decide +kernel
def odd5_independent : List Nat := [3342105, 0, 23400, 0, 350, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem odd5_independent_length : odd5_independent.length = 61 := by decide +kernel
theorem balanced6_agreement : balanced6 = balanced6_independent := by decide +kernel
theorem balanced6_total : balanced6.sum = 74974368 := by decide +kernel
theorem balanced6_failure_bin : balanced6[60]? = some 0 := by decide +kernel
#print axioms balanced6_agreement
#print axioms balanced6_total
#print axioms balanced6_failure_bin
theorem odd5_agreement : odd5 = odd5_independent := by decide +kernel
theorem odd5_total : odd5.sum = 3365856 := by decide +kernel
theorem odd5_failure_bin : odd5[60]? = some 0 := by decide +kernel
#print axioms odd5_agreement
#print axioms odd5_total
#print axioms odd5_failure_bin
end Crown.ReportHistograms
