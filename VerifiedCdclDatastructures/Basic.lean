import Std.Data.HashSet
import Std.Data.HashMap
import Batteries.Data.BinomialHeap

/- TODO:
  - Create Literal structure: Is this necessary, or can we just use bools?
    I imagine we might need an actual new Lit construct because we want to hold
    its sign (a vs ¬a, for example). We likely also want each clause to hold its
    decision level, etc.
  - Clauses: Most of the reading I've done has suggested that we basically *have* to
    use the 2WL scheme (for CDCL), and that seems to use a LL and stack in conjunction with each
    other (read more about this!) For each clause in the formula, we want to know if it
    was learned or not, the number of literals it has, etc.
    - Might want to prove some basics of clauses as well, if we choose to go with a simpler
      representation, since we are assuming CNF form for inputs. Stuff like "any clause
      is true if at least one literal (under assignment) is true"
    - How are we representing assignments? Saturn works off of an injective function,
      I believe, and MiniSAT uses a "CMap", mapping clauses to values via hashtable
  - Clause Database: a DB for learned clauses, I wonder how scalable this needs to be?
  - Seen set for other procedures
  - Algorithms for decision procedures, like VSIDS or LRB?
  - Other lazy data structures where possible?, I presume
-/

/- Vars are just identifiers, for some formula
   with variables x0, x1, x2, ..., just use
   0, 1, 2, ... in lookups
-/
namespace CDCL

abbrev Var := Nat

/- A literal is a variable with an associated sign
   like ¬p, or q
-/
structure Lit where
  var  : Var
  sign : Bool := true -- true => var, false => ¬var
  -- dl   : Nat := 0 -- decision level
  /- also add from_unit : Option Nat for the case
     if a clause was learnt via unit resolution,
     which clause caused that? have a ref to it
     (idea from IsaSAT TWL paper)
  -/
  deriving Repr, BEq, DecidableEq, Hashable

/- Helper functions for Lit go here -/

inductive Watched where
  | satisfied
  | conflict
  | unit_clause (watch : Lit)
  | two_plus (watch1 : Lit) (watch2 : Lit)
  deriving Repr, Inhabited

/- A clause is a disjunction of literals
   NOTE: We are assuming this because of CNF
-/
structure Clause where
  lits    : Array Lit
  learnt  : Bool := false -- default
  wls     : Watched
  deriving Repr, Inhabited

/- A formula is a conjunction of clauses
   NOTE: We are assuming this because of DIMACS CNF form
   which gives us the # of vars, # of clauses as well

   NOTE: Do we need this structure in particular?
-/
structure Formula where
  num_vars    : Nat
  num_clauses : Nat
  clauses     : Array Clause
  deriving Repr

/- An assignment for a formula is a mapping from vars
   to truth values
-/
structure Assignment where
  vals : Std.HashMap Var Bool := {}
  num_assigned : Nat := 0 -- works in conjunction with len vals
  deriving Repr

/- Helper functions for Assignment go here -/

def assign (a : Assignment) (v : Var) (b : Bool) : Assignment :=
  -- only increment num_assigned if was originally empty!
  if Option.isNone (a.vals.get? v) then
    { a with
      vals := a.vals.insert v b,
      num_assigned := a.num_assigned + 1 }
  else
    { a with vals := a.vals.insert v b }

/- Invariant: Assume the ClauseDB has no duplicates,
   and never produces clauses containing duplicates
-/
structure ClauseDB where
  -- init_clauses   : Array Clause -- from formula
  -- learnt_clauses : Array Clause -- from conflict analysis
  clauses : Array Clause -- indices >= #vars -> learnt clauses.
  -- FIXME: Per paper, change this to store both at same time?
  deriving Repr

/- Helper functions for ClauseDB go here -/

def addLearnt (db : ClauseDB) (c : Clause) : ClauseDB :=
  { db with clauses := db.clauses.push c }

/- Seen set, for conflict analysis etc. -/
abbrev Seen := Std.HashSet Var

def leFloatVar (f1 f2: Float × Var) : Bool :=
  f1.1 <= f2.1

/- This structure stores all of the necessary components for VSIDS -/
structure VsidsActivity where
  -- stores a variable's activity, NOTE: we have one entry per variable,
  -- NOT one entry per variable and polarity
  activities : Array Float
  var_inc    : Float := 1.0  -- current increment
  decay      : Float := 0.95 -- current decay
  heap       : Batteries.BinomialHeap (Float × Var) leFloatVar
  -- deriving Repr

namespace VsidsActivity

def bump (a : VsidsActivity) (var : Nat) : VsidsActivity :=
  let oldAct := a.activities[var]!
  let newAct := oldAct + a.var_inc
  let acts := a.activities.set! var newAct
  { a with activities := acts }

def decayAll (a : VsidsActivity) : VsidsActivity :=
  let acts := a.activities.map (· * a.decay)
  { a with activities := acts }

def updateHeap (a : VsidsActivity) (vars : Array Nat) : VsidsActivity :=
  let heap := vars.foldl (fun h v => h.insert (-(a.activities[v]!), v)) a.heap
  { a with heap := heap }

def bump_and_decay_all (a : VsidsActivity) (vars : Array Nat) : VsidsActivity :=
  -- 1. Bump all v ∈ vars
  -- 2. Decay all vars (not just ∈ vars)
  -- 3. Update heap for all v ∈ vars with new activity value
  -- NOTE: To self: feel free to unfold this expression into 3 separate ones lol
  updateHeap (decayAll (vars.foldl (fun acc v => bump acc v) a)) vars

def test_bump_and_decay_all : Bool :=
  let initial : VsidsActivity := { activities := Array.replicate 3 0.0, var_inc := 1.0, decay := 0.5, heap := Batteries.BinomialHeap.empty }
  let vars_to_bump := #[0,2]
  let updated := bump_and_decay_all initial vars_to_bump
  let acts := updated.activities
  -- Check activities:
  -- vars 0 and 2: (0 + 1) * 0.5 = 0.5
  -- var 1: 0 * 0.5 = 0
  acts[0]! == 0.5 && acts[1]! == 0.0 && acts[2]! == 0.5

#eval test_bump_and_decay_all  -- should print true

-- Select the most active variable
def popMax (a : VsidsActivity) : Option (Nat × VsidsActivity) :=
  match a.heap.deleteMin with
  | none => none
  | some (score_and_var, rest_of_heap) =>
    some (score_and_var.2, {a with heap := rest_of_heap})

end VsidsActivity

/- TODO: Add other helper functions, or maybe we can just map
   the functions across the solver
-/

/- Need to create a ResolutionTree, or some data structure
   that allows us to store the UNSAT proof

   During resolution we care about:
   - pivot literals
   - clauses derived from the resolution step

   Leaf: existing clause, referred to by id
   Resolve: records pivot + the two other nodes
            used in the resolution step
-/
inductive ResolutionTree where
  /- Leaves are clauses from the original formula, we only
     start with leaves and build up conflict clauses + our
     resolution tree from there
  -/
  | leaf    (clauseIdx : Nat)
  | resolve (pivotVar  : Var)
            (pivotSign : Bool) -- true => left has pos pivot, right has ¬pivot
            (left      : ResolutionTree)
            (right     : ResolutionTree)
  deriving Repr, Inhabited

-- TODO: Helpers for this!

end CDCL

-- TODO: Theorems about these data structures!
-- Write down invariants here
