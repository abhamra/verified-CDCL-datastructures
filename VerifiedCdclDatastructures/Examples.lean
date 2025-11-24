import VerifiedCdclDatastructures.Basic
import VerifiedCdclDatastructures.AssignmentTrail

-- x1 ∨ x2 (we use one clause here because of CNF)
def sat_example : CDCL.Formula 1 :=
  { num_vars := 2, clauses := #[ { lits := #[1, 2] } ].toVector }

-- x1 ∧ ¬x1 (via CNF)
def unsat_example : CDCL.Formula 2 :=
  { num_vars := 1, clauses := #[ {lits := #[1] }, { lits := #[-1] } ].toVector }

-- check for popVar
def l1 : CDCL.Lit := 1
def l2 : CDCL.Lit := -2
def l3 : CDCL.Lit := 3

def trail : AssignmentTrail :={ stack := Stack.empty }
def trail1 := trail.push l1 0
def trail2 := trail1.push l2 1
def trail3 := trail2.push l3 2

#eval trail3.toList
-- expect [(3, 2), (-2, 1), (1, 0)

def trailPostPop := trail3.popVar 2

#eval trailPostPop.toList
-- expect [(3, 2), (1, 0) bc removed l2 with var 2
