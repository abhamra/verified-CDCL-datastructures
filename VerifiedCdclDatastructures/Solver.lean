import VerifiedCdclDatastructures.Basic
import VerifiedCdclDatastructures.AssignmentTrail
namespace CDCL.Solver
/-- Solver state. -/
structure Solver where
  num_vars     : Nat
  clauses      : ClauseDB
  assignment   : Assignment
  decision_lvl : Nat := 0
  trail        : AssignmentTrail
  -- Stores _indices_ to clauses in ClauseDB
  sat_clauses  : Std.HashSet Nat := {}
  -- Stores clause whose unit status led to propagation. prop_reason[n] = m → n is forced to ⊤/⊥ because of clause m.
  prop_reason  : Vector (Option Nat) num_vars := Vector.replicate num_vars none 
  activity     : VsidsActivity
  -- TODO: Add resolution tree here?
  -- deriving Repr

def Solver.num_clauses (s : Solver) : Nat := s.clauses.clauses.size

/- A function that takes in a given formula and initializes
   the solver's state!
-/
def Solver.init (f : Formula) : Solver :=
  let num_vars := f.num_vars
  let init_clauses := f.clauses
  let db : ClauseDB := { clauses := init_clauses }
  let trail : AssignmentTrail := { stack := Stack.empty }
  let activity : VsidsActivity := { activities := Array.replicate num_vars 0.0,
                                    heap := Batteries.BinomialHeap.empty }
  { num_vars := num_vars, clauses := db, assignment := Assignment.ofNumVars num_vars
    decision_lvl := 0, trail := trail, activity := activity }

/- Decision heuristics (VSIDS, LRB, etc.) can be plugged in. -/
class Heuristic (α : Type) where
  pickVar : Solver → Option Var

/- Finds the first unassigned variable and pics it.
   A bad decision heuristic!
-/
def naivePickVar (s : Solver) : Option Var :=
  let vars := List.range s.num_vars
  vars.findSome? (fun v =>
    if s.assignment.isAssigned v 
    then none
    else some v)

/- Uses the Variable State Independent Decaying Sum
   (VSIDS) Decision Heuristic!

   TODO:
   - What invariants do we care about?
   - Need to show that this function terminates (we eventually get through all vars)
   - We "exhuast all variables" when...
-/
partial def vsidsPickVar (s : Solver) : Option Var :=
  match VsidsActivity.popMax s.activity with
  | none => none
  | some (var, activity') =>
    -- care only about unassigned vars
    if s.assignment.isAssigned var
    then vsidsPickVar { s with activity := activity' } -- skip assigned vars, try again
    else some var

variable (Naive : Type)
instance : Heuristic Naive where
  pickVar := naivePickVar

variable (VSIDS : Type)
instance : Heuristic VSIDS where
  pickVar := vsidsPickVar

abbrev BCPResult := Except (Solver × Clause) Solver

-- NOTE:
-- DPLL + VSIDS proof
-- Understand and extend SATurn
-- Discover invariants on the behavior of VSIDS and formalize & prove them.
-- Cover all invariants in the presentation, including those Siddartha discovered.

def bcpTests : List (Solver × BCPResult) :=
  [let s1 := Solver.init { 
    num_vars := 2
    num_clauses := 2
    clauses := #[
      { lits := #[1, 2] },
      { lits := #[-2] }
      ]
  }
  (s1, Except.ok {
    s1 with 
    clauses := {
      s1.clauses with
      num_unassigned := #[1, 0]
    }
    assignment := s1.assignment.assign 3 false
    sat_clauses := s1.sat_clauses.insert 1
  })]

/- If satisfied or unknown, returns (ok s), otherwise returns (error (s, conflict))
-/
def bcp (s : Solver) : BCPResult :=
  -- NOTE: No 2WL -- too difficult to prove.

  -- BCP can be implemented naively by doing the following:
  -- Where there are unassigned unit clauses in the formula...
  -- Find any unit clause. Assign its variable `v` to the approriate value. (pos -> ⊤, neg → ⊥)
  -- Scan the non-unit clauses for instances of `v` and `¬v`.
  -- If you find `v`, mark the clause as satisfied.
  -- If you find `¬v`, prune the variable from the clause (e.g. decrease "unassigned" count)

  -- Get the indices of the current unit clauses.
  let uc_inds := 
    Array.filterMap (λ (ci, n) => 
      if n == 1
        then some ci
        else none)
    (Array.zip (Array.range s.num_clauses) s.clauses.num_unassigned)

  -- Then, for each unit clause, we fold and compute a new list of unit clauses.
  -- We show termination by arguing `decreasing_by (total - num_assigned)`
  -- Return an array with new unit clauses.
  let (s, uc_inds) := uc_inds.foldl (λ (s, next_ucis) uci =>
    -- god this is slow
    let uc := s.clauses.clauses[uci]!
    let lit := (uc.lits.find? (λ (l : Lit) => ¬(s.assignment.isAssigned l.var))).get!
    let s := { s with 
      assignment := s.assignment.assign lit.var (lit > 0)
      clauses := s.clauses.propLit uci
      prop_reason := s.prop_reason.set! lit.var (some uci)
    }

    Fin.foldl s.num_clauses (λ ((s' : Solver), (units : Array Nat)) i =>
      -- Maybe we could pass proof values around in the solver :)
      -- These clauses are just my attempt at exploring what would satisfy
      -- Lean's bound-checking requirements.
      have hs : i < s'.num_clauses := sorry
      have hp : i < s'.prop_reason.size := sorry
      have hvc : s'.num_vars < s'.num_clauses := sorry
      
      let prop_clause := s'.clauses.clauses[i]
      if ¬(s'.sat_clauses.contains i)
      then if prop_clause.lits.contains lit
        then ({ s' with sat_clauses := s'.sat_clauses.insert i }, units)
        else if prop_clause.lits.contains (-lit)
          then 
            -- TODO: Maybe remove the panicking? Don't know if it even matters.
            -- I wonder why type inference sometimes has a stroke...
            let s' : Solver := { s' with clauses := s'.clauses.propLit i }
            have hu : i < s'.clauses.num_unassigned.size := sorry
            let units := if s'.clauses.num_unassigned[i] == 1 then units.push i else units
            (s', units)
          else (s', units)
      else (s', units)) (s, #[])
  ) (s, #[])

  -- If we don't discover any more unit clauses, we are done propagating. Now to pass judgment.
  if uc_inds.isEmpty
    then sorry
    else sorry

def decide {α : Type} [h : Heuristic α] (s : Solver) : Solver :=
  match h.pickVar s with
  | none   => s  -- no unassigned variable left
  | some v =>
    -- increment decision level and assign the variable
    let l : Lit := v
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
  let seenClauses : Std.HashSet Nat := Std.HashSet.emptyWithCapacity
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

  let curr := { conflict with lits := conflict.lits.map (λ l => -l) }

  loop curr (Std.HashSet.emptyWithCapacity)

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
  let updated_activity := s.activity.bumpAndDecayAll conflict_vars
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

  (s'', backjumpLvl)


-- Uses the kept variables from the trail to update the assignment!
def assignmentFromTrail (s : Solver) (keepVars : Std.HashSet Var) : Assignment :=
  let a := s.assignment
  Nat.fold s.num_vars (fun v _ acc => if keepVars.contains v then acc else acc.unassign v) a

/- Stub for backjumping/backtracking. -/
def backjump (s : Solver) (lvl : Nat) : Solver :=
  let trimmedTrail := AssignmentTrail.trimToLevel s.trail lvl
  let keepVars : Std.HashSet Var :=
    (AssignmentTrail.toList trimmedTrail).map (fun (lit, _) => lit.var) |> Std.HashSet.ofList
  let newAssign := assignmentFromTrail s keepVars
  let newPropReason := s.prop_reason.mapIdx (fun v old => if keepVars.contains v then old else none)

  -- TODO: Fix the resolution tree as well, if we add it to the Solver? 
  { s with trail := trimmedTrail, assignment := newAssign, prop_reason := newPropReason, decision_lvl := lvl }

/- A function that does all of the actual solving, and returns
   either a satisfying assignment to the literals, or none

   NOTE: We currently mark this `partial`, since we have to figure out a way to
   prove some sort of measure for "decreasing" or termination that Lean can abide by!
-/
partial def solve? [Heuristic α] (s : Solver) : Except ResolutionTree Assignment :=
  match bcp s with
  | Except.ok s' =>
    -- This assignment satisfies all clauses!
    if s'.sat_clauses.size == s'.num_clauses then
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

/- /// NOTES FOR NO RELEARNING THEOREM IDEAS ///
   Proof from slides is as follows:
   - Assume state is (M, N, U, D) for M = trail, N = multiset of *initial* clauses, 
     U = multiset of *learned* clauses, D = a conflict clause ∨ T(rue), this is how the
     CDCL_W calculus was defined in the paper "A Verified SAT Solver Framework with [...] Incrementality"
   - Assume we initialize CDCL_W in the state (ε, N, ∅, T)
   - Theorem says we can't have D ∈ N ∪ U, otherwise we'd have reached the same solver state;
     intuitively this is impossible because creating the conflict clause should ideally ensure that
     the same conflict is never reached at the same solver state, it would have been caught earlier
     by unit propagation.
   - NOTE: Need to correctly reason about the *trail* and perhaps the current state of the resolution tree?
   - Other note: We don't have the state of the resolution tree currently stored in the solver

     Proof: https://pmc.ncbi.nlm.nih.gov/articles/PMC6044257/pdf/10817_2018_Article_9455.pdf
     on page 17. Theorem 10.
   - AFC that CDCL learns the same clause twice, i.e. it reaches the same internal state
     with the same learned clause D, state (M, N, U, D ∨ L) where a backjump is possible
     and D ∨ L ∈ N ∪ U (multiset union) and D ∨ L is a "derived or learned clause"
   - Need to do some sort of layer-by-layer analysis
   - The trail M can be decomposed as Kₙ...K₂K₁† M₂K† M₁
     Decision literals (†) from propagated literals
   - there's more, obviously, will finish later?

   - Invariant we can try instead: the existence of a literal with the highest level in any conflict
     i.e. for every conflict clause, there must be a literal with the highest DL (?)
   - I assume this means the 1-UIP learned clause, and not the immediate conflict clause
-/
