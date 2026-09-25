import Crown.CertificateAssembly

/-! Group many core implications into one structural proof. The finite check
only tests membership of the selected mask in its core. -/
namespace Crown.CoreClauseTree
open Crown.CertificateSemantics Crown.CertificateAssembly

inductive Tree (g v : ℕ) where
  | leaf (core : Fin g) (mask : Fin v)
  | branch (left right : Tree g v)

def check {g v : ℕ} (cores : Fin g → List (Fin v)) : Tree g v → Bool
  | .leaf c m => (cores c).contains m
  | .branch l r => check cores l && check cores r

def formula {g v : ℕ} (offset : ℕ) : Tree g v → Sat.Fmla
  | .leaf c m => .one [.neg (offset+c.val), .pos m.val]
  | .branch l r => .and (formula offset l) (formula offset r)

theorem satisfies {g v : ℕ} (cores : Fin g → List (Fin v))
    (s : Fin v → Bool) (a : ℕ → Bool) (offset : ℕ)
    (hcore : ∀ c, a (offset+c.val) = (cores c).all s)
    (hselect : ∀ m : Fin v, a m.val = s m)
    (tree : Tree g v) (h : check cores tree = true) :
    (valuation a).satisfies_fmla (formula offset tree) := by
  induction tree with
  | leaf c m =>
    apply formula_one
    apply (implication_clause_iff a (.pos (offset+c.val)) (.pos m.val)).mpr
    change a (offset+c.val) = true → a m.val = true
    rw [hcore, hselect]
    intro hs
    exact List.all_eq_true.mp hs m (List.contains_iff_mem.mp h)
  | branch l r hl hr =>
    have hh : check cores l = true ∧ check cores r = true := by
      simpa only [check, Bool.and_eq_true] using h
    exact formula_and _ _ _ (hl hh.1) (hr hh.2)

#print axioms satisfies
end Crown.CoreClauseTree
