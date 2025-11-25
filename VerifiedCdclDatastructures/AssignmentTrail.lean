/- This file defines the Assignment Trail structure, which is a stack-based storage for Literals
and their corresponding decision levels, for use in branching and conflict analysis decisions

   NOTE: We should have an invariant that shows monotonically increasing stack
   only, for our use cases
-/

import VerifiedCdclDatastructures.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linarith
import Init.Data.Array.Lemmas

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

def Stack.size {α : Type} : Stack α → Nat
  | empty => 0
  | push _ xs => 1 + size xs

-- a helper predicate that tells whether a var is in the stack
def containsVar (v : CDCL.Var) : Stack (CDCL.Lit × Nat) → Bool
  | Stack.empty => false
  | Stack.push (l, _) xs => l.var == v || containsVar v xs

-- if containsVar true, then stack nonempty
lemma containsVar_true_nonempty (v : CDCL.Var) (s : Stack (CDCL.Lit × Nat)) :
    containsVar v s = true → 0 < s.size := by
      intro h
      cases s with
      | empty => simp [containsVar] at h
      | push l rest => simp [Stack.size]

-- pushes all elts from one stack onto to another
def Stack.pushAll {α : Type} (s onto : Stack α) : Stack α :=
  match s with
  | Stack.empty => onto
  | Stack.push x rest => pushAll rest (Stack.push x onto)

-- small theorem about size of stack with pushAll, total size = s.size + acc.size
lemma size_pushAll : ∀ (s acc : Stack α), (Stack.pushAll s acc).size = s.size + acc.size
  | Stack.empty, acc => by simp [Stack.pushAll, Stack.size]
  | Stack.push x xs, acc => 
  by simp [Stack.pushAll, Stack.size, size_pushAll xs (Stack.push x acc), ←Nat.add_assoc, Nat.add_comm]

-- pops until a DL
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

def size (t : AssignmentTrail) : Nat := t.stack.size

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

-- takes stack and var (nat), pops literal referred to by nat
def popVar (t : AssignmentTrail) (v : CDCL.Var) : AssignmentTrail :=
  let rec loop (s acc : Stack (CDCL.Lit × Nat)) : Stack (CDCL.Lit × Nat) :=
  match s with
  | Stack.empty => acc -- didn't find var, return accumulated
  | Stack.push (lit, dl) rest =>
    if lit.var == v then
      Stack.pushAll acc rest
    else
      loop rest (Stack.push (lit, dl) acc)
  { t with stack := loop t.stack Stack.empty }

-- popVar's loop size <= the input loop size (either -1 or stays same)
lemma loop_size (v : CDCL.Var) : ∀ (s acc : Stack (CDCL.Lit × Nat)),
  if containsVar v s then
    (popVar.loop v s acc).size = s.size + acc.size - 1
  else (popVar.loop v s acc).size = s.size + acc.size
  | Stack.empty, acc =>
    by simp [AssignmentTrail.popVar.loop, containsVar, Stack.size]
  | Stack.push (l, dl) rest, acc =>
    by
      by_cases h : l.var == v
      · simp[AssignmentTrail.popVar.loop, containsVar, h, Stack.size, size_pushAll, Nat.add_comm]
        omega -- simplify arithmetic shenaniganery
      · simp only [containsVar, popVar.loop, h, Stack.size] -- then do IH
        have ih := loop_size v rest (Stack.push (l, dl) acc)
        simp only [Stack.size] at ih
        convert ih using 2 <;> omega -- applies omega to all things gen by convert

lemma popVar_size_leq (t : AssignmentTrail) (v : CDCL.Var) :
    (t.popVar v).size <= t.size := by
      unfold popVar
      have h := loop_size v t.stack Stack.empty -- empty acc to start
      simp only [Stack.size, size] at h ⊢
      split_ifs at h with hc
      · have hpos := containsVar_true_nonempty v t.stack hc
        omega
      · omega

lemma popVar_size_lt_or_eq (t : AssignmentTrail) (v : CDCL.Var) :
    (t.popVar v).size == t.size ∨ (t.popVar v).size < t.size := by
      unfold popVar
      have h := loop_size v t.stack Stack.empty -- empty acc to start
      simp only [Stack.size, size] at h ⊢
      split_ifs at h with hc
      · right
        rw [Nat.add_zero] at h
        rw [h]
        apply Nat.sub_lt
        · have hpos := containsVar_true_nonempty v t.stack hc
          apply hpos
        · exact Nat.zero_lt_one
      · left
        rw [Nat.add_zero] at h
        rw [←h]
        simp

end AssignmentTrail

-- TODO: Prove the functionality of the stack, and then semantics of the AssignmentTrail
/- When removing literals from the assignment trail, we want the invariant for
   the 2WL to be preserved without requiring any real updates (lazy)
-/
