import VerifiedCdclDatastructures.AssignmentTrail
import VerifiedCdclDatastructures.Basic
namespace CDCL.Solver
/-- Solver state. -/
structure Solver where
  num_vars     : Nat
  num_clauses  : Nat
  clauses      : ClauseDB
  assignment   : Assignment
  decision_lvl : Nat := 0
  trail        : AssignmentTrail
  -- deriving Repr

/- Decision heuristics (VSIDS, LRB, etc.) can be plugged in. -/
class Heuristic (α : Type) where
  pickVar : Solver → Option Var

/- Finds the first unassigned variable and pics it.
   A bad decision heuristic!
-/ 
def naivePickVar (s : Solver) : Option Var :=
  let vars := List.range s.num_vars
  vars.findSome? (fun v =>
    match s.assignment.vals.get? v with
    | none   => some v   -- unassigned
    | some _ => none)

instance : Heuristic Naive where
  pickVar := naivePickVar

/- Stub for BCP (unit propagation with 2WL).
   TODO: Revisit this function!
-/
def bcp (s : Solver) : Solver × Option Clause := 
  -- TODO: implement watched literals
  (s, none)

/- Stub for making a decision. -/
-- def decide (s : Solver) : Solver :=
--   -- TODO: use heuristic
--   s

def decide {α : Type} [h : Heuristic α] (s : Solver) : Solver :=
  match h.pickVar s with
  | none   => s  -- no unassigned variable left
  | some v =>
    -- increment decision level and assign the variable
    let l : Lit := { var := v, sign := true, dl := s.decision_lvl + 1 }
    { s with
      decision_lvl := s.decision_lvl + 1,
      assignment   := assign s.assignment v true  -- for now, just pick True
      trail        := s.trail.push l -- we add to the assignment trail @ decision time!
    }

/- Stub for conflict analysis. This should, given some solver and 
   initial conflict clause, use the 1-UIP scheme to find new conflictclauses and add them to the solver's ClauseDB. Then, it will
   return the backjump level.
-/
def analyzeConflict (s : Solver) (conflict : Clause) : Solver × Nat :=
  -- TODO: implement 1-UIP
  (s, 0) -- TODO: Should return the backjump level!

/- Stub for clause learning. -/
def learn (s : Solver) (c : Clause) : Solver :=
  { s with clauses.clauses := s.clauses.clauses.push c }

/- Stub for backjumping/backtracking. -/
def backjump (s : Solver) (lvl : Nat) : Solver :=
  -- TODO: trim trail, reset assignment
  { s with decision_lvl := lvl }

/- A function that takes in a given formula and initializes
   the solver's state!
-/
def initSolver (f : Formula) : Solver :=
  let num_vars := f.num_vars
  let num_clauses := f.num_clauses
  let init_clauses := f.clauses
  let db : ClauseDB := { clauses := init_clauses }
  let trail : AssignmentTrail := { stack := Stack.empty }
  { num_vars := num_vars, num_clauses := num_clauses, clauses := db,
    assignment := { vals := {}, num_assigned := 0 },
    decision_lvl := 0, trail := trail }

/- A function that does all of the actual solving, and returns
   either a satisfying assignment to the literals, or none

   NOTE: We currently mark this `partial`, since we have to figure out a way to
   prove some sort of measure for "decreasing" or termination that Lean can abide by!
-/
partial def solve? [Heuristic α] (s : Solver) : Option Assignment :=
  let (s', conflict?) := bcp s
  match conflict? with
  | some conflict =>
    let (s'', backjumpLvl) := analyzeConflict s' conflict
    -- top level conflict => UNSAT
    if backjumpLvl == 0 then
      none
    else
      -- backjump!
      let s''' := backjump s'' backjumpLvl
      solve? (α := α) s'''
  | none =>
    -- if all variables assigned, we have SAT!
    if s'.assignment.vals.size == s'.assignment.num_assigned then
       some s'.assignment
    else
      -- branching!
      let s_w_decide := decide (α := α) s'
      solve? (α := α) s_w_decide

end CDCL.Solver

-- TODO: Theorems about solver functions!
