/- This file defines the Assignment Trail structure, which is a stack-based storage for Literals
and their corresponding decision levels, for use in branching and conflict analysis decisions
-/

import VerifiedCdclDatastructures.Basic

-- Stacks for generic types α
inductive Stack (α : Type) where
  | empty : Stack α
  | push : α → Stack α → Stack α
  deriving Repr

def push {α : Type} (x : α) (s : Stack α) : Stack α :=
  Stack.push x s

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
  stack : Stack (CDCL.Lit × Nat) := Stack.empty
  -- deriving Repr

namespace AssignmentTrail

-- TODO: Add helper/wrapper functions around the internal stack

def push (t : AssignmentTrail) (lit : CDCL.Lit) (dl : Nat) : AssignmentTrail :=
  { t with stack := Stack.push (lit, dl) t.stack }

def pop (t : AssignmentTrail) : Option AssignmentTrail :=
  match Stack.pop t.stack with
  | none => none
  | some newS => some { t with stack := newS }

def top (t : AssignmentTrail) : Option (CDCL.Lit × Nat) :=
  Stack.top t.stack

def isEmpty (t : AssignmentTrail) : Bool :=
  Stack.isEmpty t.stack

end AssignmentTrail

-- TODO: Prove the functionality of the stack, and then semantics of the AssignmentTrail
/- When removing literals from the assignment trail, we want the invariant for
   the 2WL to be preserved without requiring any real updates (lazy)
-/
