import VerifiedCdclDatastructures.Basic
namespace Solver
/-- Solver state. -/
structure Solver where
  clauses     : ClauseDB
  assignment  : Assignment
  decision_lvl : Nat := 0
  trail       : Array Lit := #[] -- FIXME: Change this to AssignmentTrail later
  deriving Repr


/- Decision heuristics (VSIDS, LRB, etc.) can be plugged in. -/
class Heuristic (α : Type) where
  pickVar : Solver → Option Var

/- Stub for BCP (unit propagation with 2WL).
   TODO: Revisit this function!
-/
def bcp (s : Solver) : Solver × Option Clause := 
  -- TODO: implement watched literals
  (s, none)

/- Stub for making a decision. -/
def decide (s : Solver) : Solver :=
  -- TODO: use heuristic
  s

/- Stub for conflict analysis. -/
def analyze (s : Solver) (conflict : Clause) : Solver × Clause :=
  -- TODO: implement 1-UIP
  (s, conflict)

/- Stub for clause learning. -/
def learn (s : Solver) (c : Clause) : Solver :=
  { s with clauses.learnt_clauses := s.clauses.learnt_clauses.push c }

/- Stub for backtracking. -/
def backtrack (s : Solver) (lvl : Nat) : Solver :=
  -- TODO: trim trail, reset assignment
  { s with decision_lvl := lvl }

end Solver
