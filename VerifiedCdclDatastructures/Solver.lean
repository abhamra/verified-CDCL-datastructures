import VerifiedCdclDatastructures.Basic
import VerifiedCdclDatastructures.AssignmentTrail
namespace CDCL.Solver
/-- Solver state. -/
structure Solver where
  num_vars     : Nat
  num_clauses  : Nat
  clauses      : ClauseDB
  assignment   : Assignment
  decision_lvl : Nat := 0
  trail        : AssignmentTrail
  sat_clauses  : Std.HashSet Nat := {} -- Stores _indices_ to clauses in ClauseDB
  prop_reason  : Array (Option Nat) := #[] -- Stores variable whose assignment led to propagation. prop_reason[n] = m → n is forced to ⊤/⊥ because of m.
  activity     : VsidsActivity
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

/- Uses the Variable State Independent Decaying Sum
   (VSIDS) Decision Heuristic!

   TODO:
   - What invariants do we care about?
   - Need to show that this function terminates (we eventually get through all vars)
-/
partial def vsidsPickVar (s : Solver) : Option Var :=
  match VsidsActivity.popMax s.activity with
  | none => none
  | some (var, activity') =>
    -- care only about unassigned vars
    match s.assignment.vals.get? var with
    | some _ => vsidsPickVar { s with activity := activity' } -- skip assigned vars, try again
    | none => some var

variable (Naive : Type)
instance : Heuristic Naive where
  pickVar := naivePickVar

variable (VSIDS : Type)
instance : Heuristic VSIDS where
  pickVar := vsidsPickVar

abbrev BCPResult := Except (Solver × Clause) Solver
#check Array.foldlM
#check Except

-- NOTE:
-- DPLL + VSIDS proof
-- Understand and extend SATurn
-- Discover invariants on the behavior of VSIDS and formalize & prove them.
-- Cover all invariants in the presentation, including those Siddartha discovered.

/- If satisfied or unknown, returns (ok s), otherwise returns (error (s, conflict))
-/
def bcp (s : Solver) : BCPResult :=
  -- NOTE: No 2WL -- too difficult to prove.

  -- We actually only want to do this for literals that are unit.
  let propOne (s : Solver) (v : Var): BCPResult :=
    -- Check all the clauses to see if they contain `v`.
    let v_pos : Lit := { var := v, sign := true }
    let v_neg : Lit := { var := v, sign := false }
    -- Propagate positively
    let sat_clauses' := s.sat_clauses.insertMany
      (Array.filter (λ (c_ind : Nat) =>
        not (s.sat_clauses.contains c_ind) && s.clauses.clauses[c_ind]!.lits.elem v_pos)
        (Array.range s.clauses.clauses.size))

    -- Propagate negatively.

    Except.ok { s with
                sat_clauses := sat_clauses' }

  -- Find which literals are unit. (Maybe we could just maintain this as we go along?)

  -- Naively folding
  Array.foldlM propOne s (Array.range s.num_vars)

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
    let l : Lit := { var := v, sign := true }
    let dl := s.decision_lvl + 1
    { s with
      decision_lvl := dl,
      assignment   := assign s.assignment v true  -- for now, just pick True
      trail        := s.trail.push l dl -- we add to the assignment trail @ decision time!
    }

/- Stub for conflict analysis. This should, given some solver and
   initial conflict clause, use the 1-UIP scheme to find new conflict
   clauses and add them to the solver's ClauseDB. Then, it will
   return the backjump level.

  -- TODO: implement 1-UIP as a *stretch* goal, but goal for now
     is to just use the assignment trail and create a conflict clause from there.
-/
def analyzeConflict (s : Solver) (conflict : Clause) : Solver × Nat :=
  -- get all vars from clause, then
  let conflict_vars := conflict.lits.map (·.var) -- ignores sign
  -- bump and decay all, then
  let updated_activity := VsidsActivity.bump_and_decay_all s.activity conflict_vars
  -- update solver activity, then
  let s' := { s with activity := updated_activity };

  -- NOTE: Not doing this rn, no real learning cuz DPLL + VSIDS
  /- find a new conflict clause and
    add it to the clausedb, then
   let new_clauses : Array Clause := s'.clauses.clauses.push new_conflict
   let new_db : ClauseDB := { s'.clauses with clauses := new_clauses }
   let s'' := { s' with clauses := new_db } -/

  -- figure out backjump level. We do this by selecting the variable
  -- with the 2nd highest decision level.
  -- NOTE: The highest deicision level is the level of our conflict, so we
  -- want at least one before that, to prevent that same conflict from arising
 -- NOTE: If we don't do clause learning, then backjump level is always
 --       the curr level - 1
  (s', s'.decision_lvl - 1)

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
  let activity : VsidsActivity := { activities := Array.replicate num_vars 0.0,
                                    heap := Batteries.BinomialHeap.empty }
  { num_vars := num_vars, num_clauses := num_clauses, clauses := db,
    assignment := { vals := {}, num_assigned := 0 },
    decision_lvl := 0, trail := trail, activity := activity }

/- A function that does all of the actual solving, and returns
   either a satisfying assignment to the literals, or none

   NOTE: We currently mark this `partial`, since we have to figure out a way to
   prove some sort of measure for "decreasing" or termination that Lean can abide by!
-/
partial def solve? [Heuristic α] (s : Solver) : Except ResolutionTree Assignment :=
  match bcp s with
  | Except.ok s' =>
    -- if all variables assigned, we have SAT!
    if s'.assignment.vals.size == s'.assignment.num_assigned then
       Except.ok s'.assignment
    else
      -- branching!
      let s_w_decide := decide (α := α) s'
      solve? (α := α) s_w_decide
  | Except.error (s', conflict) =>
    let (s'', backjumpLvl) := analyzeConflict s' conflict
    -- top level conflict => UNSAT
    if backjumpLvl == 0 then
      -- TODO: Return a proof.
      Except.error (ResolutionTree.leaf 0)
    else
      -- backjump!
      let s''' := backjump s'' backjumpLvl
      solve? (α := α) s'''

end CDCL.Solver

-- TODO: Theorems about solver functions!
