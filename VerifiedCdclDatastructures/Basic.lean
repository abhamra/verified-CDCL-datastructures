def hello := "world"

/- TODO:
  - Create Literal structure: Is this necessary, or can we just use bools?
    I imagine we might need an actual new Lit construct because we want to hold
    its sign (a vs ¬a, for example). We likely also want each clause to hold its
    decision level, etc.
  - Clauses: Most of the reading I've done has suggested that we basically *have* to
    use the 2WL scheme (for CDCL), and that seems to use a LL and stack in conjunction with each
    other (read more about this!) For each clause in the formula, we want to know if it
    was learned or not, the number of literals it has, etc.
    - Might want to prove some baics of clauses as well, if we choose to go with a simpler
      representation, since we are assuming CNF form for inputs. Stuff like "any clause
      is true if at least one literal (under assignment) is true"
    - How are we representing assignments? Saturn works off of an injective function,
      I believe, and MiniSAT uses a "CMap", mapping clauses to values via hashtable
  - Clause Database: a DB for learned clauses, I wonder how scalable this needs to be?
  - Seen set for other procedures
  - Algorithms for decision procedures, like VSIDS or LRB?
  - Other lazy data structures where possible?, I presume
-/

