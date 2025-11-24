/- This file defines the Assignment Trail structure, which is a stack-based storage for Literals
and their corresponding decision levels, for use in branching and conflict analysis decisions

   NOTE: We should have an invariant that shows monotonically increasing stack
   only, for our use cases
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

def popUntilLevel : Stack (CDCL.Lit × Nat) → Nat → Stack (CDCL.Lit × Nat)
  | Stack.empty, _ => Stack.empty
  | Stack.push (lit, dl) rest, lvl =>
    if dl > lvl then
      popUntilLevel rest lvl
    else Stack.push (lit, dl) rest

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

-- converts AT to a list, helper
def toList (t : AssignmentTrail) : List (CDCL.Lit × Nat) :=
  let rec go : Stack (CDCL.Lit × Nat) -> List (CDCL.Lit × Nat)
  | Stack.empty => []
  | Stack.push x s' => x :: go s'
  go t.stack

def litsToSet (t : AssignmentTrail) : Std.HashSet CDCL.Lit :=
  Std.HashSet.ofList ((toList t).map (fun (l, _) => l))

def decisionLevels (t : AssignmentTrail) : List Nat :=
  toList t |>.map (·.2)

def varsAtLevel (t : AssignmentTrail) (dl : Nat) : List CDCL.Var :=
  toList t |>.filterMap (fun (l, lvl) => if lvl = dl then some l.natAbs else none)

-- helper for finding decision level of a given variable
def dlOfVar (t : AssignmentTrail) (v : CDCL.Var) : Option Nat :=
  (t.toList.find? (·.1.natAbs = v)).map (·.2)

-- finds the last assigned literal, literal with the highest DL in clause
-- Assumes monotonicity of the trail stack w.r.t decision level (highest DL @ top)
def findLastAssigned (t : AssignmentTrail) (c : CDCL.Clause) : CDCL.Lit :=
  let litSet := Std.HashSet.ofList c.lits.toList
  let rec go : List (CDCL.Lit × Nat) -> CDCL.Lit
  | [] => 0
  | (l, _) :: rest =>
    if litSet.contains l then
      l
    else
      go rest

  go (toList t)

def trimToLevel (t : AssignmentTrail) (lvl : Nat) : AssignmentTrail :=
  { t with stack := popUntilLevel t.stack lvl }

end AssignmentTrail

-- TODO: Prove the functionality of the stack, and then semantics of the AssignmentTrail
/- When removing literals from the assignment trail, we want the invariant for
   the 2WL to be preserved without requiring any real updates (lazy)
-/
