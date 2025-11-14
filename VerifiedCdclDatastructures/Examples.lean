import VerifiedCdclDatastructures.Basic

def v0 := (0 : CDCL.Var)
def v1 := (1 : CDCL.Var)
def l0pos : CDCL.Lit := { var := v0, sign := true }
def l0neg : CDCL.Lit := { var := v0, sign := false }
def l1pos : CDCL.Lit := { var := v1, sign := true }
def l1neg : CDCL.Lit := { var := v1, sign := false }

-- v0 ∨ v1 (we use one clause here because of CNF)
def sat_example : CDCL.Formula :=
  { num_vars := 2, num_clauses := 1, clauses := #[ { lits := #[l0pos, l1pos]} ] }

-- v0 ∧ ¬v0 (via CNF)
def unsat_example : CDCL.Formula :=
  {num_vars := 2, num_clauses := 2, clauses := #[ {lits := #[l0pos]}, { lits := #[l0neg]}] }
