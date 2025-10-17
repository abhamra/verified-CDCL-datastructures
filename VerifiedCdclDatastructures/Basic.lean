import Std.Data.HashMap
import Std.Data.HashSet

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
  dl   : Nat := 0 -- decision level
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
  deriving Repr

/- A clause is a disjunction of literals
   NOTE: We are assuming this because of CNF
-/
structure Clause where
  lits    : Array Lit
  learnt  : Bool := false -- default
  wls     : Watched
  deriving Repr

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
  | leaf    : (clauseIdx : Nat) -> ResolutionTree
  | resolve : (pivotVar  : Var) ->
              (pivotSign : Bool) -> -- true => left has pos pivot, right has ¬pivot
              (left      : ResolutionTree) ->
              (right     : ResolutionTree) ->
              ResolutionTree
  deriving Repr

-- TODO: Helpers for this!

end CDCL

-- TODO: Theorems about these data structures!
-- Write down invariants here
