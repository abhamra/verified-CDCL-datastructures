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
  -- TODO: Add resolution tree here?
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
      assignment   := Assignment.assign s.assignment v true  -- for now, just pick True
      trail        := s.trail.push l dl -- we add to the assignment trail @ decision time!
    }

-- (Helper) look at all the clauses and pick unseen clauses that contain l,
-- then return the unseen clause containing l as well as an unseen literal in l
def pickIncomingEdge (s : Solver) (l : CDCL.Lit) (seenClauses : Std.HashSet Nat) : (Clause × CDCL.Lit) :=
  sorry
  -- let candidate_clauses := s.clauses.clauses.filter
  -- TODO: Finish this!

-- add intermediary assignments to res tree, bookkeeping?
def resolveOnVar (c1 c2 : Clause) (piv : CDCL.Var) : Clause :=
  let keepFrom (c : Clause) : Array Lit :=
    c.lits.foldl (fun acc l => if l.var == piv then acc else if acc.elem l then acc else acc.push l) #[]

  let merged := (keepFrom c1) ++ (keepFrom c2)
  { lits := merged, learnt := true }
  

/- Stub for clause learning. Use this for 1-UIP, it takes
   in the current solver state and a conflict clause, and
   generates a learnt conflict clause via the first unique
   implication point formulation
-/
def learn (s : Solver) (conflict : Clause) : Clause :=
  /-
    1. Start from conflict clause, set the "curr" clause to be the
       negation of all literals in the clause. For example, with
       conflict = (¬x1 ∨ ¬x2), curr becomes (x1 ∨ x2)
    2. In the current clause c, find the last assigned literal l
    3. Pick an incoming edge to l (a clause c' that contains literal l)
       and pick an unseen literal in that clause that points to it
    4. Resolve curr and c'
    5. set curr = resolve curr c'
    6. repeat until only one literal in curr @ s.dl
    7. set clause to learnt = True
    8. ya termine
  -/
  let seenClauses : Std.HashSet Nat := Std.HashSet.empty
  let dl := s.decision_lvl

  let rec loop (curr : Clause) (seen : Std.HashSet CDCL.Var) : Clause :=
    let lits_at_dl :=
      curr.lits.filter (fun (l : Lit) =>
        let var_dl := AssignmentTrail.dlOfVar s.trail l.var |>.getD 0 -- default 0 else var_dl
        var_dl = dl)
    if lits_at_dl.size == 1 then curr else 
      -- find last assigned literal l
      let last_assigned_lit := AssignmentTrail.findLastAssigned s.trail curr
      -- pick incoming edge
      let (clause_that_implied, new_lit) := pickIncomingEdge s last_assigned_lit seenClauses
      -- resolve clause_that_implied and curr 
      -- NOTE: we know that last_assigned_lit's sign in curr is the opposite of its sign in
      -- clause_that_implied

      -- TODO: Figure out if this correctly shadows
      let curr := resolveOnVar curr clause_that_implied last_assigned_lit.var
      loop curr seen -- FIXME: Need to prove this recurses correctly, show termination!!!

  let curr := { conflict with lits := conflict.lits.map (fun l => { l with sign := !l.sign } ) }

  loop curr (Std.HashSet.empty)

def secondMax (xs : Array Nat) : Option Nat :=
  if xs.size < 2 then none
  else
    let (_, max2) := 
      xs.foldl
      (init := (0, 0))
      fun (m1, m2) x => 
      if x > m1 then (x, m1)
      else if x >= m2 then (m1, x)
      else (m1, m2)
  some max2

#eval secondMax #[1, 5, 3, 4, 5]  -- some 5
#eval secondMax #[7]              -- none

-- want 2nd highest dl
def computeBackjumpLevel (s : Solver) (conflict : Clause) : Nat :=
  -- get list of dls of all vars
  let dls : Array Nat := conflict.lits.map (fun l => (AssignmentTrail.dlOfVar s.trail l.var |>.getD 0))
  -- get 2nd highest value
  (secondMax dls).getD 0 -- NOTE: Is this safe to do? because 0 is a "dangerous" val for backjumping

  -- let secondHighest? : Option Nat :=
  --   let uniq := dls.toList.eraseDups |>.qsort (· > ·)
  --   match uniq with
  --   | _ :: second :: _ => some second
  --   | _ => none
  -- secondHighest?.getD 0 

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


  -- find a new conflict clause and
  let new_conflict := learn s' conflict
  -- add it to the clausedb, then
   let new_clauses : Array Clause := s'.clauses.clauses.push new_conflict
   let new_db : ClauseDB := { s'.clauses with clauses := new_clauses }
   let s'' := { s' with clauses := new_db }

  -- figure out backjump level. We do this by selecting the variable
  -- with the 2nd highest decision level.
  -- NOTE: The highest deicision level is the level of our conflict, so we
  -- want at least one before that, to prevent that same conflict from arising
  -- NOTE: If we don't do clause learning, then backjump level is always
  --       the curr level - 1

  -- get max dl from new_conflict
  let backjumpLvl := computeBackjumpLevel s' new_conflict

  (s', backjumpLvl)


-- Uses the kept variables from the trail to update the assignment!
def assignmentFromTrail (s : Solver) (keepVars : Std.HashSet Var) : Assignment :=
  let a := s.assignment
  a.vals.toList.foldl (fun acc (v, _) => if keepVars.contains v then acc else Assignment.unassign acc v) a

/- Stub for backjumping/backtracking. -/
def backjump (s : Solver) (lvl : Nat) : Solver :=
  let trimmedTrail := AssignmentTrail.trimToLevel s.trail lvl
  let keepVars : Std.HashSet Var :=
    (AssignmentTrail.toList trimmedTrail).map (fun (lit, _) => lit.var) |> Std.HashSet.ofList
  let newAssign := assignmentFromTrail s keepVars
  let newPropReason : Array (Option Nat) := s.prop_reason.mapIdx (fun v old => if keepVars.contains v then old else none)

  -- TODO: Fix the resolution tree as well, if we add it to the Solver? 
  { s with trail := trimmedTrail, assignment := newAssign, prop_reason := newPropReason, decision_lvl := lvl }

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
