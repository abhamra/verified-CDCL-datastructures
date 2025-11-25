import VerifiedCdclDatastructures.AssignmentTrail
import VerifiedCdclDatastructures.Basic

import Mathlib.Tactic.Lemma
import Init.Data.Array.Lemmas

namespace CDCL.Solver
/-- Solver state. -/
structure Solver (nv nc : Nat) where
  clauses       : ClauseDB nc
  assignment    : Assignment nv
  decision_lvl  : Nat := 0
  trail         : AssignmentTrail
  -- Stores _indices_ to clauses in ClauseDB
  is_satisfied  : Vector Bool nc := Vector.replicate nc false
  -- How many clauses are still in the "unknown" state?
  contingent_ct : Nat := nc
  -- Stores clause whose unit status led to propagation. prop_reason[n] = m → n is forced to ⊤/⊥ because of clause m.
  prop_reason   : Vector (Option Nat) nv := Vector.replicate nv none 
  activity      : VsidsActivity
  -- TODO: Add resolution tree here?
  -- deriving Repr

def Solver.num_vars (_: Solver nv nc) : Nat := nv
def Solver.num_clauses (_ : Solver nv nc) : Nat := nc

/- A function that takes in a given formula and initializes
   the solver's state!
-/
def Solver.init {num_clauses : Nat} (f : Formula num_clauses) : Solver f.num_vars num_clauses :=
  let num_vars := f.num_vars
  let init_clauses := f.clauses
  let db := { clauses := init_clauses }
  let trail : AssignmentTrail := { stack := Stack.empty }
  let activity : VsidsActivity := { activities := Array.replicate num_vars 0.0,
                                    heap := Batteries.BinomialHeap.empty }
  { clauses := db, assignment := Assignment.ofNumVars num_vars
    decision_lvl := 0, trail := trail, activity := activity }

/- Decision heuristics (VSIDS, LRB, etc.) can be plugged in. -/
class Heuristic {nv nc : Nat} (α : Type) where
  pickVar : Solver nv nc → Option Var

/- Finds the first unassigned variable and pics it.
   A bad decision heuristic!
-/
def naivePickVar {nv nc : Nat} (s : Solver nv nc) : Option Var :=
  let vars := List.range s.num_vars
  vars.findSome? (fun v =>
    if s.assignment.isAssigned v 
    then none
    else some v)

/- Uses the Variable State Independent Decaying Sum
   (VSIDS) Decision Heuristic!

   TODO:
   - What invariants do we care about?
   - Need to show that this function terminates (we eventually get through all vars)
   - We "exhuast all variables" when...
-/
partial def vsidsPickVar {nv nc : Nat} (s : Solver nv nc) : Option Var :=
  match VsidsActivity.popMax s.activity with
  | none => none
  | some (var, activity') =>
    -- care only about unassigned vars
    if s.assignment.isAssigned var
    then vsidsPickVar (nv := nv) { s with activity := activity' } -- skip assigned vars, try again
    else some var

variable (Naive : Type)
instance : Heuristic (nv := nv) (nc := nc) Naive where
  pickVar := naivePickVar

variable (VSIDS : Type)
instance : Heuristic (nv := nv) (nc := nc) VSIDS where
  pickVar := vsidsPickVar

abbrev BCPResult (nv nc : Nat) := Except (Solver nv nc × Clause) (Solver nv nc)

-- NOTE:
-- DPLL + VSIDS proof
-- Understand and extend SATurn
-- Discover invariants on the behavior of VSIDS and formalize & prove them.
-- Cover all invariants in the presentation, including those Siddartha discovered.

def f1 : Formula 2 := { 
    num_vars := 2
    clauses := #[
      { lits := #[1, 2] },
      { lits := #[-2] }
      ].toVector
  }

def bcpTest1 : Solver f1.num_vars f1.clauses.size × BCPResult f1.num_vars f1.clauses.size := 
  let s1 := Solver.init f1
  (s1, Except.ok {
    s1 with 
    clauses := {
      s1.clauses with
      num_unassigned := #[1, 0].toVector
    }
    assignment := s1.assignment.assign 3 false
    is_satisfied := Vector.set s1.is_satisfied 1 true
  })


-- NOTE: Let's whip up some lemmas to make the proof manageable.
-- Start by showing `propNonUnit` at least does not increase `contingent_ct`.
-- Then show propOne decreases `contingent_ct` (should be easier)
-- Then just by transitivity, you have it!

abbrev PropTriple (nv nc : Nat) := Solver nv nc × Array (Fin nc) × Array (Fin nc)
def propNonUnit (lit : Lit) (in_prop : PropTriple nv nc) (i : Fin nc) : PropTriple nv nc :=
  let (s', units', non_uc) := in_prop
  -- Maybe we could pass proof values around in the solver :)
  -- These clauses are just my attempt at exploring what would satisfy
  -- Lean's bound-checking requirements.
  let prop_clause := s'.clauses.clauses[i]
  if ¬(s'.is_satisfied[i])
  then if prop_clause.lits.contains lit
    then ({ s' with is_satisfied := s'.is_satisfied.set i true
                    contingent_ct := s'.contingent_ct - 1
    }, units', non_uc.push i)
    else if prop_clause.lits.contains (-lit)
      then 
        let s' : Solver nv nc := { s' with clauses := s'.clauses.propLit i }
        let (units', non_uc) := if s'.clauses.num_unassigned[i] = 1 
          then (units'.push i, non_uc)
          else (units', non_uc.push i)
        (s', units', non_uc)
      else (s', units', non_uc.push i)
  -- Skip the next non-unit
  else (s', units', non_uc)

-- I feel like this proof could be much terser, but throwing dynamite is a martial art as long as it works :)
-- We want to show that `contingent_ct` always decreases in each call of `bcp`.
-- This is the ground floor of the proof: show `propNonUnit` doesn't increase contingent_ct.
lemma propNonUnit_leq (pt : PropTriple nv nc) :
    ∀ lit i, (propNonUnit lit pt i).fst.contingent_ct ≤ pt.fst.contingent_ct := by
  intros
  unfold propNonUnit
  split -- destruct match
  · simp
    split -- destruct if
    · split -- destruct if
      · simp
      · split -- destruct if
        all_goals simp -- Just simplify both cases thx
    · simp

lemma propNonUnit_leq_foldl_induction (pt : PropTriple nv nc) :
    ∀ lit (non_uc : Array (Fin nc)), (non_uc.foldl (propNonUnit lit) pt).fst.contingent_ct ≤ pt.fst.contingent_ct := by
  sorry

def propOne (in_prop : PropTriple nv nc) (uci : Fin nc) : PropTriple nv nc :=
  let (s, units', non_uc') := in_prop
  -- god this is slow
  let uc := s.clauses.clauses[uci]
  let lit := (uc.lits.find? (λ (l : Lit) => ¬(s.assignment.isAssigned l.var))).get!
  let s := { s with 
    assignment := s.assignment.assign lit.var (lit > 0)
    is_satisfied := s.is_satisfied.set uci true -- It's a unit clause, so it's saitsfied!
    contingent_ct := s.contingent_ct - 1
    clauses := s.clauses.propLit uci
    prop_reason := s.prop_reason.set! lit.var (some uci)
  }
  -- Now we can just scan over the clauses that we know aren't unit.
  non_uc'.foldl (propNonUnit lit) (s, #[], #[])

-- Next, we show that `propOne` strictly decreases `contingent_ct`.
-- We observe that its body before calling `propNonUnit` does this, and we know that applying `propNonUnit`
-- any number of times won't increase `contingent_ct`, so by transitivity `propOne` upholds this invariant.
lemma propOne_lt (pt : PropTriple nv nc) {hcz : pt.fst.contingent_ct > 0} :
    ∀ uci, (propOne pt uci).fst.contingent_ct < pt.fst.contingent_ct := by
  intros uci
  unfold propOne
  split
  next s' units' non_uc' =>
    extract_lets uc lit s
    simp at hcz
    dsimp
    have hcm : s.contingent_ct = s'.contingent_ct - 1 := rfl
    have hc : s.contingent_ct < s'.contingent_ct := by omega
    let s'' := (Array.foldl (propNonUnit lit) (s, #[], #[]) non_uc').fst
    have hleq : s''.contingent_ct ≤ s.contingent_ct := propNonUnit_leq_foldl_induction (s, #[], #[]) lit non_uc'
    subst s'' s
    omega

def propUnits (in_prop : PropTriple nv nc) (hc : in_prop.fst.contingent_ct > 0) : BCPResult nv nc :=
  let s := in_prop.fst
  let (uc_inds, non_uc) := in_prop.snd
  let (s', uc_inds, non_uc) := uc_inds.foldl propOne (s, #[], #[])

  -- Once again, `foldl` induction. Still wrapping my head around exactly what a "motive" is
  have hcc : s'.contingent_ct < s.contingent_ct := by admit
    -- subst s
    -- apply propOne_lt after_prop hc

  -- If we don't discover any more unit clauses, we are done propagating. Now to pass judgment.
  if uc_inds.isEmpty
    then if hcz : s.contingent_ct = 0
      then .ok s
      else match s.clauses.num_unassigned.findFinIdx? (· == 0) with
        | some idx => if ¬(s.is_satisfied[idx])
                        then .error (s, sorry)
                        else .ok s
        | _ => .ok s
    else 
      -- This is implied by uc_inds != empty.
      have hcz : s'.contingent_ct > 0 := sorry
      propUnits (s', uc_inds, non_uc) hcz
  termination_by (in_prop.fst.contingent_ct)

/- If satisfied or unknown, returns (ok s), otherwise returns (error (s, conflict))
  BCP can be implemented naively by doing the following:
  Where there are unassigned unit clauses in the formula...
  Find any unit clause. Assign its variable `v` to the approriate value. (pos -> ⊤, neg → ⊥)
  Scan the non-unit clauses for instances of `v` and `¬v`.
  If you find `v`, mark the clause as satisfied.
  If you find `¬v`, prune the variable from the clause (e.g. decrease "unassigned" count)
-/
def bcp {nv nc : Nat} (s : Solver nv nc) (hc : s.contingent_ct > 0) : BCPResult nv nc :=
  -- NOTE: No 2WL -- too difficult to prove.
  -- Get the indices of the current unit clauses.
  let (uc_inds, non_uc) := (Array.finRange nc).partition
    (λ i => s.clauses.num_unassigned[i] = 1)
  propUnits (s, uc_inds, non_uc) hc

-- TODO: This should be straightforward once I've got `propUnits` proved.
theorem bcp_decreases_ct (s : Solver nv nc) (hc : s.contingent_ct > 0) :
    s.contingent_ct < (match bcp s hc with | .ok s' => s'.contingent_ct | .error (s', _) => s'.contingent_ct) :=
  sorry

def decide {α : Type} {nv nc : Nat} [h : Heuristic (nv := nv) (nc := nc) α] (s : Solver nv nc) : Solver nv nc :=
  match h.pickVar s with
  | none   => s  -- no unassigned variable left
  | some v =>
    -- increment decision level and assign the variable
    let l : Lit := v
    let dl := s.decision_lvl + 1
    { s with
      decision_lvl := dl,
      assignment   := Assignment.assign s.assignment v true  -- for now, just pick True
      trail        := s.trail.push l dl -- we add to the assignment trail @ decision time!
    }

theorem decide_preserves_ct {α : Type} [h : Heuristic (nv := nv) (nc := nc) α] (s : Solver nv nc) :
    s.contingent_ct = (decide (α := α) (h := h) s).contingent_ct := by
  unfold decide
  split
  all_goals simp

-- (Helper) look at all the clauses and pick unseen clauses that contain l,
-- then return the unseen clause containing l
def pickIncomingEdge {nv nc : Nat} (s : Solver nv nc) (l : CDCL.Lit) (seenClauses : Std.HashSet Nat) : (Clause × Nat) :=
  -- first we filter to select over ONLY unseen clauses THAT contain l
  let candidate_idx_clauses := (List.zip (List.range nc) s.clauses.clauses.toList)|>.filter (fun (i, _) => !seenClauses.contains i)
  -- then for each unseen clause, if there is an unseen literal (literal not in trail OR
  -- literal not assigned in solver.assignments) then we have that clause
  let seen_lits := AssignmentTrail.litsToSet s.trail

  let opt_idx_c2r := candidate_idx_clauses.find? (fun (_, c) => c.lits.any (fun lit => !seen_lits.contains lit))
  let (idx, c2r) := opt_idx_c2r.get! -- FIXME: THIS IS UNSAFE

  -- NOTE: In order to accurately satisfy 1-UIP, we need to:
  -- 1. Negate all literals in that clause and then
  let c2r' := { c2r with lits := c2r.lits.map (λ lit => -lit) }
  -- 2. OR-concat l to the end of the clause, so curr (which contains -l) can resolve with
  --    this new clause
  let c2r'' := { c2r' with lits := c2r.lits.push l }
  (c2r'', idx)


-- add intermediary assignments to res tree, bookkeeping?
def resolveOnVar (c1 c2 : Clause) (piv : CDCL.Var) : Clause :=
  let keepFrom (c : Clause) : Array Lit :=
    c.lits.foldl (fun acc l => if l.var == piv then acc else if acc.elem l then acc else acc.push l) #[]

  -- NOTE: Need to make sure there are no duplicates
  let merged := Array.mergeDedup (keepFrom c1) (keepFrom c2)
  { lits := merged, learnt := true }
  


-- Goal: Want to show that the trail size after popVar <= trail size before popVar
theorem popVar_trail_size_decreases (s : Solver nv nc) (v : Var) :
  (s.trail.popVar v).size < s.trail.size := by
    -- use popVar_size_lt_or_eq instead?
    -- likely need to assert something about containing var v
    apply AssignmentTrail.popVar_size_leq s.trail v
    sorry

/- Stub for clause learning. Use this for 1-UIP, it takes
   in the current solver state and a conflict clause, and
   generates a learnt conflict clause via the first unique
   implication point formulation
-/
def learn {nv nc : Nat} (s : Solver nv nc) (conflict : Clause) : (Solver nv nc × Clause) :=
  /-
    1. Start from conflict clause, set the "curr" clause to be the
       negation of all literals in the clause. For example, with
       conflict = (¬x1 ∨ x2), curr becomes (x1 ∨ ¬x2)
    2. In the current clause c, find the last assigned literal l
    3. Pick an incoming edge to l (a clause c' that contains literal l)
       and pick an unseen literal in that clause that points to it
    4. Resolve curr and c'
    5. set curr = resolve curr c'
    6. repeat until only one literal in curr @ s.dl
    7. set clause to learnt = True
    8. ya termine
  -/
  let seenClauses : Std.HashSet Nat := Std.HashSet.emptyWithCapacity
  let dl := s.decision_lvl

  -- We want to show that loop terminates. How do we do this?
  -- prove that lits_at_dl's size eventually decreases, reaching the `curr` termination case
  -- 
  let rec loop (s : Solver nv nc) (curr : Clause) (seen : Std.HashSet Nat) : (Solver nv nc × Clause) :=
    let lits_at_dl :=
      curr.lits.filter (fun (l : Lit) =>
        let var_dl := AssignmentTrail.dlOfVar s.trail l.var |>.getD 0 -- default 0 else var_dl
        var_dl = dl)
    if lits_at_dl.size == 1 then (s, curr) else 
      -- find last assigned literal l, then get ¬l
      let last_assigned_lit := -AssignmentTrail.findLastAssigned s.trail curr
      -- pick incoming edge
      let (clause_that_implied, clause_idx) := pickIncomingEdge s last_assigned_lit seenClauses
      -- resolve clause_that_implied and curr
      -- NOTE: we know that last_assigned_lit's sign in curr is the opposite of its sign in
      -- clause_that_implied

      -- TODO: Figure out if this correctly shadows
      let curr := resolveOnVar curr clause_that_implied last_assigned_lit.var
      -- update seen clauses
      let seenClauses := seenClauses.insert clause_idx

      -- update trail
      let s' : Solver nv nc := { s with trail := s.trail.popVar last_assigned_lit.var }
      have : s'.trail.size < s.trail.size := by
        simp [s']
        apply popVar_trail_size_decreases

      loop s' curr seen -- FIXME: Need to prove this recurses correctly, show termination!
  termination_by s.trail.size

  let curr := { conflict with lits := conflict.lits.map (λ l => -l) }

  loop s curr seenClauses

def secondMax (xs : Array Nat) : Option Nat :=
  if xs.size < 2 then none
  else
    let (_, max2) := 
      xs.foldl
      (init := (0, 0))
      fun (m1, m2) x => 
      if x > m1 then (x, m1)
      else if x >= m2 then (m1, x)
      else (m1, m2)
  some max2

#eval secondMax #[1, 5, 3, 4, 5]  -- some 5
#eval secondMax #[7]              -- none

-- want 2nd highest dl
def computeBackjumpLevel {nv nc : Nat} (s : Solver nv nc) (conflict : Clause) : Nat :=
  -- get list of dls of all vars
  let dls : Array Nat := conflict.lits.map (fun l => (AssignmentTrail.dlOfVar s.trail l.var |>.getD 0))
  -- get 2nd highest value
  (secondMax dls).getD 0 -- NOTE: Is this safe to do? because 0 is a "dangerous" val for backjumping

  -- let secondHighest? : Option Nat :=
  --   let uniq := dls.toList.eraseDups |>.qsort (· > ·)
  --   match uniq with
  --   | _ :: second :: _ => some second
  --   | _ => none
  -- secondHighest?.getD 0 

/- Stub for conflict analysis. This should, given some solver and
   initial conflict clause, use the 1-UIP scheme to find new conflict
   clauses and add them to the solver's ClauseDB. Then, it will
   return the backjump level.

  -- TODO: implement 1-UIP as a *stretch* goal, but goal for now
     is to just use the assignment trail and create a conflict clause from there.
-/
def analyzeConflict {nv nc : Nat} (s : Solver nv nc) (conflict : Clause) : (Solver nv (nc + 1)) × Nat :=
  -- get all vars from clause, then
  let conflict_vars := conflict.lits.map (·.var) -- ignores sign
  -- bump and decay all, then
  let updated_activity := s.activity.bumpAndDecayAll conflict_vars
  -- update solver activity, then
  let s' := { s with activity := updated_activity };


  -- find a new conflict clause and
  let (s_learn, new_conflict) := learn s' conflict
  -- add it to the clausedb, then
  let new_db := s.clauses.addLearnt s.assignment conflict
  let s'' := { s_learn with clauses := new_db, is_satisfied := s_learn.is_satisfied.push false, contingent_ct := s_learn.contingent_ct + 1 }
  -- NOTE: s_learn (from `learn`) UPDATES the trail, which is why we return a new solver state from it

  -- figure out backjump level. We do this by selecting the variable
  -- with the 2nd highest decision level.
  -- NOTE: The highest deicision level is the level of our conflict, so we
  -- want at least one before that, to prevent that same conflict from arising
  -- NOTE: If we don't do clause learning, then backjump level is always
  --       the curr level - 1

  -- get max dl from new_conflict
  let backjumpLvl := computeBackjumpLevel s' new_conflict

  (s'', backjumpLvl)


-- Uses the kept variables from the trail to update the assignment!
def assignmentFromTrail {nv nc : Nat} (s : Solver nv nc) (keepVars : Std.HashSet Var) : Assignment nv :=
  let a := s.assignment
  Nat.fold s.num_vars (fun v _ acc => if keepVars.contains v then acc else acc.unassign v) a

/- Stub for backjumping/backtracking. -/
def backjump {nv nc : Nat} (s : Solver nv nc) (lvl : Nat) : Solver nv nc :=
  -- NOTE: `learn` already updates the trail in place, so we do not need to trim here
  -- let trimmedTrail := AssignmentTrail.trimToLevel s.trail lvl
  let keepVars : Std.HashSet Var :=
    (AssignmentTrail.toList s.trail).map (fun (lit, _) => lit.var) |> Std.HashSet.ofList
  let newAssign := assignmentFromTrail s keepVars
  let newPropReason := s.prop_reason.mapIdx (fun v old => if keepVars.contains v then old else none)

  -- TODO: Fix the resolution tree as well, if we add it to the Solver? 
  { s with assignment := newAssign, prop_reason := newPropReason, decision_lvl := lvl }

/- A function that does all of the actual solving, and returns
   either a satisfying assignment to the literals, or none

   We only allow you to call this function on a solver with

   NOTE: We currently mark this `partial`, since we have to figure out a way to
   prove some sort of measure for "decreasing" or termination that Lean can abide by!
-/
def solve? {nv nc : Nat} [heur : Heuristic (nv := nv) (nc := nc) α] (s : Solver nv nc) {hc : s.contingent_ct > 0} : Except ResolutionTree (Assignment nv) :=
  match bcp s hc with
  | Except.ok s' =>
    -- This assignment satisfies all clauses!
    if hc : s'.contingent_ct = 0 then
       Except.ok s'.assignment
    else
      -- branching!
      have hbcp : s'.contingent_ct < s.contingent_ct := bcp_decreases_ct s hc
      let s_w_decide := decide (α := α) s'
      have hd : s'.contingent_ct = s_w_decide.contingent_ct := by
        simp_all
        have hsw : s_w_decide = decide (α := α) s' := rfl
        rw [hsw]
        apply decide_preserves_ct s'
      have hc : s_w_decide.contingent_ct > 0 := by
        simp_all
        omega

      solve? (α := α) s_w_decide (hc := hc)
  | Except.error (s', conflict) =>
    let (s'', backjumpLvl) := analyzeConflict s' conflict
    -- top level conflict => UNSAT
    if backjumpLvl == 0 then
      -- TODO: Return a proof.
      Except.error (ResolutionTree.leaf 0)
    else
      -- backjump!
      let s''' := backjump s'' backjumpLvl
      -- TODO: Backjumping will, by defintion, make 
      have hb : s'''.contingent_ct > 0 := sorry
      solve? (α := α) s''' (hc := hb)
  termination_by (s.contingent_ct)

end CDCL.Solver

-- TODO: Theorems about solver functions!

/- /// NOTES FOR NO RELEARNING THEOREM IDEAS ///
   Proof from slides is as follows:
   - Assume state is (M, N, U, D) for M = trail, N = multiset of *initial* clauses, 
     U = multiset of *learned* clauses, D = a conflict clause ∨ T(rue), this is how the
     CDCL_W calculus was defined in the paper "A Verified SAT Solver Framework with [...] Incrementality"
   - Assume we initialize CDCL_W in the state (ε, N, ∅, T)
   - Theorem says we can't have D ∈ N ∪ U, otherwise we'd have reached the same solver state;
     intuitively this is impossible because creating the conflict clause should ideally ensure that
     the same conflict is never reached at the same solver state, it would have been caught earlier
     by unit propagation.
   - NOTE: Need to correctly reason about the *trail* and perhaps the current state of the resolution tree?
   - Other note: We don't have the state of the resolution tree currently stored in the solver

     Proof: https://pmc.ncbi.nlm.nih.gov/articles/PMC6044257/pdf/10817_2018_Article_9455.pdf
     on page 17. Theorem 10.
   - AFC that CDCL learns the same clause twice, i.e. it reaches the same internal state
     with the same learned clause D, state (M, N, U, D ∨ L) where a backjump is possible
     and D ∨ L ∈ N ∪ U (multiset union) and D ∨ L is a "derived or learned clause"
   - Need to do some sort of layer-by-layer analysis
   - The trail M can be decomposed as Kₙ...K₂K₁† M₂K† M₁
     Decision literals (†) from propagated literals
   - there's more, obviously, will finish later?

   - Invariant we can try instead: the existence of a literal with the highest level in any conflict
     i.e. for every conflict clause, there must be a literal with the highest DL (?)
   - I assume this means the 1-UIP learned clause, and not the immediate conflict clause
-/
