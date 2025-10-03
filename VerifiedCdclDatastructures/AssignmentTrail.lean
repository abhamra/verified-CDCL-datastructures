/- This file defines the Assignment Trail structure, which is a stack-based storage for Literals
and their corresponding decision levels, for use in branching and conflict analysis decisions
-/
-- Stacks for generic types α
inductive Stack (α : Type) where
  | empty : Stack α
  | push : α → Stack α → Stack α
  deriving Repr

def Stack.top {α : Type} : Stack α → Option α
  | empty => none
  | push x _ => some x

def Stack.pop {α : Type} : Stack α → Option (Stack α)
  | empty => none
  | push _ xs => some xs

def Stack.isEmpty {α : Type} : Stack α → Bool
  | empty => true
  | _ => false

/- The assignment trail holds a stack of literals for use in the Solver process -/
structure AssignmentTrail where
  stack : Stack Lit
  -- deriving Repr

namespace AssignmentTrail

-- TODO: Add helper/wrapper functions around the internal stack

end AssignmentTrail

-- TODO: Prove the functionality of the stack, and then semantics of the AssignmentTrail
