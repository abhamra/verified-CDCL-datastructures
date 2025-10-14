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

/- A clause is a disjunction of literals
   NOTE: We are assuming this because of CNF
-/
structure Clause where
  lits    : Array Lit
  learnt  : Bool := false -- default
  -- FIXME: Delete this, return to SATurn
  watch1? : Option Nat := none -- default
  watch2? : Option Nat := none -- default
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
  clauses : Array Clause -- can just use indices as normal
  -- FIXME: Per paper, change this to store both at same time?
  deriving Repr

/- Helper functions for ClauseDB go here -/

def addLearnt (db : ClauseDB) (c : Clause) : ClauseDB :=
  { db with clauses := db.clauses.push c }

/- The watch list contains, for each literal, a list of clauses
   that are currently watching that literal
   TODO: Implement this, and figure out if this requires, for ex.,
   p and ¬p to be "unique" watched literals (I don't think so)

   This data structure pairs with the two concrete watched literals
   in each clause of our formula

  invariant: either a clause has two unassigned watch literals or it is unit
  for currently unsatisfied clauses
  where unsatisfied means (not yet satisfied under current partial assignment)

  Unless a conflict has been found, a watched literal may
  be false only if the other watched literal is true and all
  the unwatched literals are false.
  NOTE: ^ Invariant from "A Verified SAT Solver with Watched Literals
          Using Imperative HOL"

  FIXME: Delete this and we try doing regular DPLL?
-/
structure WatchList where
  clauses_per_lit : Std.HashMap Lit (Array Nat) := {}
  -- Each Lit points to a list of indices to clauses in a Formula
  -- since Formula holds an indexable list of clauses
  deriving Repr
  
/- Helper functions for WatchList go here -/
/- Add a number of clause indices to a given literal
   To add only one, just provide a singleton list
-/
def addWatch (wl : WatchList) (lit : Lit) (clauseIndices : Array Nat) : WatchList :=
  let curr_wls_for_lit := wl.clauses_per_lit[lit]?.getD #[]
  let updated := curr_wls_for_lit ++ clauseIndices
  { wl with clauses_per_lit := wl.clauses_per_lit.insert lit updated }

def getWatched (wl : WatchList) (lit : Lit) : Array Nat :=
  wl.clauses_per_lit[lit]?.getD #[]

def emptyWL : WatchList :=
  { clauses_per_lit := {} }


/- FIXME: From IsaSAT TWL paper
  "To capture the 2WL data structure formally, we need a no-
  tion of state that takes into account pending updates. These
  can concern a specific clause or all the clauses associated
  with a literal. As in the example above, we first process the
  clause-specific updates; then we move to the next literal and
  start updating its associated clauses."

  - Store unit and non-unit clauses separately
  - have a "work stack" WS which holds {(L, C_1), ..., (L, C_n)}
    for false literal L and clauses C_i that watch L and thus
    require an update
  - have a queue Q to store all of the other "in flight" literals
    that need to be worked on

    Example on p3-4 is instructive

  - invariant: WS and Q are empty during decide

  - With delete_idx_and_swap(), given a list of clauses relative
    to some literal L, watch_list[L], if the clause w no longer watches L bc of
    update, swap w with the last clause in the list then delete.
    This is constant time!
-/

/- Seen set, for conflict analysis etc. -/
abbrev Seen := Std.HashSet Var

end CDCL

-- TODO: Theorems about these data structures!
-- Write down invariants here
