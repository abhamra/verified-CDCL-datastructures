import VerifiedCdclDatastructures.Basic

-- x1 ∨ x2 (we use one clause here because of CNF)
def sat_example : CDCL.Formula 1 :=
  { num_vars := 2, clauses := #[ { lits := #[1, 2] } ].toVector }

-- x1 ∧ ¬x1 (via CNF)
def unsat_example : CDCL.Formula 2 :=
  { num_vars := 1, clauses := #[ {lits := #[1] }, { lits := #[-1] } ].toVector }
