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
  deriving Repr, BEq, DecidableEq, Hashable

/- Helper functions for Lit go here -/

/- A clause is a disjunction of literals
   NOTE: We are assuming this because of CNF
-/
structure Clause where
  lits    : Array Lit
  learnt  : Bool := false -- default
  watch1? : Option Nat := none -- default
  watch2? : Option Nat := none -- default
  deriving Repr

/- A formula is a conjunction of clauses
   NOTE: We are assuming this because of CNF

   NOTE: Do we need this structure in particular?
-/
structure Formula where
  clauses : Array Clause
  deriving Repr

/- An assignment for a formula is a mapping from vars
   to truth values
-/
structure Assignment where
  vals : Std.HashMap Var Bool
  num_assigned : Nat -- works in conjunction with len vals
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

structure ClauseDB where
  init_clauses   : Array Clause -- from formula
  learnt_clauses : Array Clause -- from conflict analysis
  deriving Repr

/- Helper functions for ClauseDB go here -/

/- The watch list contains, for each literal, a list of clauses
   that are currently watching that literal
   TODO: Implement this, and figure out if this requires, for ex.,
   p and ¬p to be "unique" watched literals (I don't think so)

   This data structure pairs with the two concrete watched literals
   in each clause of our formula
-/
structure WatchList where
  clauses_per_lit : Std.HashMap Lit (Array Nat)
  -- Each Lit points to a list of indices to clauses in a Formula
  -- since Formula holds an indexable list of clauses
  deriving Repr
  
/- Helper functions for WatchList go here -/

/- Seen set, for conflict analysis etc. -/
abbrev Seen := Std.HashSet Var

end CDCL

-- TODO: Theorems about these data structures!
-- Write down invariants here
