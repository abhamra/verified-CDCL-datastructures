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

variable (Naive : Type)
instance : Heuristic Naive where
  pickVar := naivePickVar

/- Stub for BCP (unit propagation with 2WL).
   TODO: Revisit this function!
-/
def bcp (s : Solver) : Solver × Option Clause := 
  -- NOTE: No 2WL -- too difficult to prove.
  -- To make later searches faster I'm going to have a sort of "two stacks" implementation
  -- (satisfied and unsatisfied)
  
  let propOne (s_and_conf : Solver × Option Clause) (v : Var): Solver × Option Clause :=
    let (s, conflict_clause?) := s_and_conf
    -- Check all the clauses to see if they contain `v`.
    let v_pos : Lit := { var := v, sign := true, dl := 0 }
    let v_neg : Lit := { var := v, sign := false, dl := 0 }
    -- TODO: We should be able to prove that v_pos or v_neg is in the map.
    -- We can invariants about the solver easily accessible by adding a field with type (`inv`)
    let s' := Array.foldl (λ (s : Solver) (c_ind : Nat) =>
      sorry
    ) s (sorry)

    sorry
  -- Naively folding
  let rec propagate (s : Solver) 
      (open_clauses : Array Clause := s.clauses.clauses)
      (unsat_clauses : Stack Clause := Stack.empty):
      Solver × Option Clause :=

    Array.foldl propOne (s, none) (Array.range s.num_vars)
 propagate s

/-
def bcp2WL (s : Solver) : Solver × Option Clause :=
  -- This thing returns the state of the solver or the clause that led to a conflict.
  let rec propagate (s : Solver) (prop_lit : Lit) : Solver × Option Clause :=
    -- It's starting to make sense.
    let prop_lit := { prop_lit with dl := s.decision_lvl }
    let next_at := s.trail.push prop_lit
    let neg_lit := { prop_lit with sign := ¬prop_lit.sign }

    -- Propagate positively through `init`
    -- No conflicts will arise (we set him to true)
    let sat_clauses := s.watch_list[prop_lit]!

    -- We don't know for sure if ¬lit is represented, in which case we iterate over
    let resolving_clauses := s.watch_list.getD neg_lit #[]

    sorry

  let litIfUnit (c : Clause) : Option Lit :=
    match c.wls with
    | CDCL.Watched.unit_clause l => some l
    | _ => none

  -- Find a unit clause. If there are none, we are done.
  match Array.findSome? litIfUnit s.clauses.clauses with
  | some lit => 
    -- Start propagating, continuing the loop if we find more unit clauses.
    propagate s lit
  | none => (s, none) -- We are done, no resolution can happen.
-/

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
   initial conflict clause, use the 1-UIP scheme to find new conflict
   clauses and add them to the solver's ClauseDB. Then, it will
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

/-
/- For a given clause index, update the watchlist for it, and the corresponding
   clauses' watched literals
-/
def initClauseWatches (idx : Nat) (c : Clause) (wl : WatchList) : Clause × WatchList :=
  match c.lits[0]?, c.lits[1]? with
  | some l1, some l2 =>
      let wl := addWatch wl l1 #[idx]
      let wl := addWatch wl l2 #[idx]
      ({ c with wls := Watched.two_plus l1 l2 }, wl)
  | some l1, none =>
      let wl := addWatch wl l1 #[idx]
      ({ c with wls := Watched.unit_clause l1 }, wl)
  | _, _ =>
      (c, wl)
-/

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
