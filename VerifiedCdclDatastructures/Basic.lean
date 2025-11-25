import Std.Data.HashSet
import Std.Data.HashMap
import Batteries.Data.BinomialHeap
import Batteries.Data.Array

namespace CDCL

/- Vars are just identifiers, for some formula
   with variables x1, x2, x3, ..., just use
   1, 2, 3, ... in lookups
-/
abbrev Var := Nat
/- A literal is a variable with an associated sign
   like ¬p, or q. Positive literals are true, negative literals are false.
   Counting starts at one.
-/
abbrev Lit := Int
def Lit.var (l : Lit) := l.natAbs

/- A clause is a disjunction of literals
   NOTE: We are assuming this because of CNF
-/
structure Clause where
  lits    : Array Lit
  learnt  : Bool := false -- default
  deriving Repr, Inhabited

/- A formula is a conjunction of clauses
   NOTE: We are assuming this because of DIMACS CNF form
   which gives us the # of vars, # of clauses as well

   NOTE: Do we need this structure in particular?
-/

structure Formula (num_clauses : Nat) where
  num_vars    : Nat
  clauses     : Vector Clause num_clauses
  deriving Repr

inductive AssignState where
  | Unassigned
  | True
  | False
  deriving Repr, Inhabited, BEq

def AssignState.fromBool : Bool → AssignState := λ
  | true => AssignState.True
  | false => AssignState.False

/- An assignment for a formula is a mapping from vars
   to truth values
-/
structure Assignment (num_vars : Nat) where
  vals : Vector AssignState num_vars
  num_assigned : Nat := 0 -- works in conjunction with len vals
  deriving Repr

/- Helper functions for Assignment go here -/

namespace Assignment

def ofNumVars (num_vars : Nat) : Assignment num_vars :=
  { vals := Vector.replicate num_vars .Unassigned }

def isAssigned {nv : Nat} (a : Assignment nv) (v : Var) : Bool :=
  a.vals[v]! != .Unassigned

def assign {nv : Nat} (a : Assignment nv) (v : Var) (b : Bool) : Assignment nv :=
  -- only increment num_assigned if was originally empty!
  let vals' := a.vals.set! v (AssignState.fromBool b)
  if a.isAssigned v then
    { a with
      vals := vals'
      num_assigned := a.num_assigned + 1 }
  else
    { a with vals := vals' }

def unassign {nv : Nat} (a : Assignment nv) (v : Var) : Assignment nv :=
  match a.vals[v]! with
  | .Unassigned => a
  | _ =>
    { a with
      vals := a.vals.set! v .Unassigned,
      num_assigned := a.num_assigned - 1 }

end Assignment

/- Invariant: Assume the ClauseDB has no duplicates,
   and never produces clauses containing duplicates
-/
structure ClauseDB (nc : Nat) where
  -- init_clauses   : Array Clause -- from formula
  -- learnt_clauses : Array Clause -- from conflict analysis
  clauses : Vector Clause nc -- indices >= #vars -> learnt clauses.
  num_unassigned : Vector Nat nc := clauses.map (λ c => c.lits.size)
  -- FIXME: Per paper, change this to store both at same time?
  deriving Repr

/- Helper functions for ClauseDB go here -/

def Vector.modify {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) (f : α → α) : Vector α n :=
  v.set i (f v[i])

namespace ClauseDB

def addLearnt {nv nc : Nat} (db : ClauseDB nc) (a : Assignment nv) (c : Clause) : ClauseDB (nc + 1) :=
  let unassigned := c.lits.countP (λ lit => ¬a.isAssigned lit.var)
  { db with clauses := db.clauses.push c 
            num_unassigned := db.num_unassigned.push unassigned
  }

def propLit {nc : Nat} (db : ClauseDB nc) (c_ind : Fin nc) : ClauseDB nc :=
  { db with num_unassigned := Vector.modify db.num_unassigned c_ind (· - 1) }

end ClauseDB

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

def bumpAndDecayAll (a : VsidsActivity) (vars : Array Nat) : VsidsActivity :=
  -- 1. Bump all v ∈ vars
  -- 2. Decay all vars (not just ∈ vars)
  -- 3. Update heap for all v ∈ vars with new activity value
  -- NOTE: To self: feel free to unfold this expression into 3 separate ones lol
  updateHeap (decayAll (vars.foldl (fun acc v => bump acc v) a)) vars

def test_bump_and_decay_all : Bool :=
  let initial : VsidsActivity := { activities := Array.replicate 3 0.0, var_inc := 1.0, decay := 0.5, heap := Batteries.BinomialHeap.empty }
  let vars_to_bump := #[0,2]
  let updated := bumpAndDecayAll initial vars_to_bump
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
