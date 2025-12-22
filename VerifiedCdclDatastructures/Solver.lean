import VerifiedCdclDatastructures.Basic
import VerifiedCdclDatastructures.AssignmentTrail

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

structure PropInfo (nv nc : Nat) where
  s : Solver nv nc
  unsat : Array (Fin nc)
  units : Array (Fin nc)
  two_plus : Array (Fin nc)

def PropInfo.empty (s : Solver nv nc) : PropInfo nv nc :=
  { s := s
    unsat := Array.empty
    units := Array.empty
    two_plus := Array.empty
  }

def satisfyUnit {nv nc : Nat} (s : Solver nv nc) (uci : Fin nc) : Solver nv nc :=
  let uc := s.clauses.clauses[uci]
  let lit := (uc.lits.find? (λ (l : Lit) => ¬(s.assignment.isAssigned l.var))).get!
  { s with 
    assignment := s.assignment.assign lit.var (lit > 0)
    is_satisfied := s.is_satisfied.set uci true -- It's a unit clause, so it's saitsfied!
    contingent_ct := s.contingent_ct - 1
    clauses := s.clauses.propLit uci
    prop_reason := s.prop_reason.set! lit.var (some uci)
    trail := s.trail.push lit s.decision_lvl
  }

lemma satisfyUnit_decr_contingent_ct (s : Solver nv nc) (uci : Fin nc) {hc : s.contingent_ct > 0} :
    (satisfyUnit s uci).contingent_ct < s.contingent_ct
  := by
    have hm1 : (satisfyUnit s uci).contingent_ct = s.contingent_ct - 1 := rfl
    omega

def categorizeClauses (s : Solver nv nc) : Array (Fin nc) × Array (Fin nc) × Array (Fin nc) :=
  let sans_satisfied := (Array.finRange nc).filter (λ i => !s.is_satisfied[i])
  let (unsat, one_plus) := sans_satisfied.partition (λ i => s.clauses.num_unassigned[i] = 0)
  let (units, two_plus) := one_plus.partition (λ i => s.clauses.num_unassigned[i] = 1)
  (unsat, units, two_plus)

def propOne2InnerHaveCt {nv nc : Nat} (uci : Fin nc) (pi : PropInfo nv nc) (hc0 : pi.s.contingent_ct > 0) : PropInfo nv nc :=
    -- This implementation is much slower than the foldl one
    -- but has some macro-level properties that make it much nicer to prove.
    let lit := (pi.s.clauses.clauses[uci].lits.find? (λ (l : Lit) => ¬(pi.s.assignment.isAssigned l.var))).get!
    let s := satisfyUnit pi.s uci
    have hs : s.contingent_ct < pi.s.contingent_ct := satisfyUnit_decr_contingent_ct pi.s uci (hc := hc0)

    -- Folds are not helping me here.
    -- Reframing the problem -- find all clauses that contain this literal.
    -- Two passes over the array isn't fantastic but its behavior is at least understood.
    let pos_props := pi.two_plus.filter (λ tpi => !s.is_satisfied[tpi] ∧ s.clauses.clauses[tpi].lits.contains lit)
    let is_satisfied' := pos_props.foldl (λ acc sat_i => acc.set sat_i true) s.is_satisfied
    let contingent_ct' := s.contingent_ct - pos_props.size

    -- You might get to here and have a bunch of clauses with three literals after propagating negatively.
    -- So the number of two_plus clauses may not decrease after a call to this.
    -- Maybe it is still worth trying to rewrite the old `propOne` s.t. it does not depend on foldl induction.
    let neg_props := pi.two_plus.filter (λ tpi => s.clauses.clauses[tpi].lits.contains (-lit))
    let s' := neg_props.foldl (λ acc prop_i => { acc with clauses := acc.clauses.propLit prop_i }) s
    let (unsat', units', two_plus') := categorizeClauses s'
    let contingent_ct'' := contingent_ct' - unsat'.size

    have hct : contingent_ct'' < pi.s.contingent_ct := by omega
    { s := { s' with 
                is_satisfied := is_satisfied'
                contingent_ct := contingent_ct''
           }
      unsat := unsat'
      units := units'
      two_plus := two_plus'
    }

def propOne2Inner {nv nc : Nat} (pi : PropInfo nv nc) (uci : Fin nc) : PropInfo nv nc :=
    let lit := (pi.s.clauses.clauses[uci].lits.find? (λ (l : Lit) => ¬(pi.s.assignment.isAssigned l.var))).get!
    let s := satisfyUnit pi.s uci
    have : s.contingent_ct ≤ pi.s.contingent_ct := by 
      have : s.contingent_ct = pi.s.contingent_ct - 1 := rfl
      omega

    -- Folds are not helping me here.
    -- Reframing the problem -- find all clauses that contain this literal.
    -- Two passes over the array isn't fantastic but its behavior is at least understood.
    let pos_props := pi.two_plus.filter (λ tpi => !s.is_satisfied[tpi] ∧ s.clauses.clauses[tpi].lits.contains lit)
    let is_satisfied' := pos_props.foldl (λ acc sat_i => acc.set sat_i true) s.is_satisfied
    let contingent_ct' := s.contingent_ct - pos_props.size

    -- You might get to here and have a bunch of clauses with three literals after propagating negatively.
    -- So the number of two_plus clauses may not decrease after a call to this.
    -- Maybe it is still worth trying to rewrite the old `propOne` s.t. it does not depend on foldl induction.
    let neg_props := pi.two_plus.filter (λ tpi => s.clauses.clauses[tpi].lits.contains (-lit))
    let s' := neg_props.foldl (λ acc prop_i => { acc with clauses := acc.clauses.propLit prop_i }) s
    let (unsat', units', two_plus') := categorizeClauses s'
    let contingent_ct'' := contingent_ct' - unsat'.size

    have hct : contingent_ct'' ≤ pi.s.contingent_ct := by omega

    { s := { s' with 
                is_satisfied := is_satisfied'
                contingent_ct := contingent_ct''
           }
      unsat := unsat'
      units := units'
      two_plus := two_plus'
    }

lemma propOne2InnerHaveCt_decr {nv nc : Nat} (uci : Fin nc) (pi : PropInfo nv nc) (hc0 : pi.s.contingent_ct > 0) :
    (propOne2InnerHaveCt uci pi hc0).s.contingent_ct < pi.s.contingent_ct := by
  unfold propOne2InnerHaveCt
  extract_lets
  split
  next =>
    extract_lets
    omega

lemma propOne2Inner_monotone {nv nc : Nat} (pi : PropInfo nv nc) (uci : Fin nc) :
    (propOne2Inner pi uci).s.contingent_ct ≤ pi.s.contingent_ct := by
  unfold propOne2Inner
  extract_lets
  split
  next =>
    extract_lets
    omega

def propOne2 {nv nc : Nat} (s : Solver nv nc) (units : Array (Fin nc)) (hsz : units.size > 0) (hc : s.contingent_ct > 0) : PropInfo nv nc :=
  have hnempty : units.toList ≠ [] := by
    simp
    apply Array.ne_empty_of_size_pos
    exact hsz
  let units := units.toList
  let hd := units.head hnempty
  let tl := units.tail
  let pi' := propOne2InnerHaveCt hd (PropInfo.empty s) hc
  -- NOTE: Didn't have the time to prove a monotonicity thm for lists, you could easily fix this!
  tl.toArray.foldl propOne2Inner pi'

lemma propOne2_decr {nv nc : Nat} (s : Solver nv nc) (units : Array (Fin nc)) (hsz : units.size > 0) (hc : s.contingent_ct > 0) :
    (propOne2 s units hsz hc).s.contingent_ct < s.contingent_ct := by
  unfold propOne2
  extract_lets hnempty units' hd tl pi'
  have h1 : pi'.s.contingent_ct < s.contingent_ct := by
    subst pi'
    let pi := (PropInfo.empty s)
    have hpi : pi.s.contingent_ct > 0 := by
      subst pi
      unfold PropInfo.empty
      omega
    apply propOne2InnerHaveCt_decr hd pi hpi
  have hmono : (tl.toArray.foldl propOne2Inner pi').s.contingent_ct ≤ pi'.s.contingent_ct := Array.foldl_leq_monotone tl.toArray propOne2Inner pi' (·.s.contingent_ct) propOne2Inner_monotone
  omega

def propUnits2 (s : Solver nv nc) (unsat : Array (Fin nc)) (units : Array (Fin nc)) (two_plus : Array (Fin nc)) : BCPResult nv nc :=
  if hs : s.contingent_ct = 0
    then .ok s -- Successfully propagated through every clause -> you are done.
    else if have_unsat : unsat.size > 0
    then .error (s, s.clauses.clauses[unsat[0]])
    else if only_units : two_plus.size = 0
      then
        let s := units.foldl satisfyUnit s
        .ok s
      else if no_units : units.size = 0
        then .ok s -- Done, no unit clauses to propagate.
        else
          have hs : s.contingent_ct > 0 := (Nat.ne_zero_iff_zero_lt.mp hs)
          let pi' := propOne2 s units (Nat.ne_zero_iff_zero_lt.mp no_units) hs
          have : pi'.s.contingent_ct < s.contingent_ct := propOne2_decr s units (Nat.ne_zero_iff_zero_lt.mp no_units) hs
          propUnits2 pi'.s pi'.unsat pi'.units pi'.two_plus
  termination_by (s.contingent_ct)

def bcp {nv nc : Nat} (s : Solver nv nc) : BCPResult nv nc :=
  let (unsat, units, two_plus) := categorizeClauses s
  propUnits2 s unsat units two_plus

-- TODO: This should be straightforward once I've got `propUnits` proved.
theorem bcp_decreases_ct (s : Solver nv nc) (hc : s.contingent_ct > 0) :
    s.contingent_ct < (match bcp s with | .ok s' => s'.contingent_ct | .error (s', _) => s'.contingent_ct) 
  := sorry

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
  -- FIXME: Can we prove that this is non-empty? and that c.lits.contains l?
  let candidate_idx_clauses := (List.zip (List.range nc) s.clauses.clauses.toList)|>.filter (fun (i, _) => !seenClauses.contains i)
  let opt_idx_c2r := candidate_idx_clauses.find? (fun (_, c) => c.lits.contains l)
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
    apply AssignmentTrail.popVar_size_lt_containsVar s.trail v
    sorry

lemma last_assigned_lit_in_trail
  (s : Solver nv nc) (curr : CDCL.Clause)
  (h_curr_assigned : ∀ l ∈ curr.lits, containsVar l.var s.trail.stack = true)
  (h_last': AssignmentTrail.findLastAssigned s.trail curr = some optional_last_lit) :
    containsVar optional_last_lit.var s.trail.stack = true := by
      have h_found_in_curr : optional_last_lit ∈ curr.lits := by
        apply AssignmentTrail.findLastAssigned_returns_lit_in_clause s.trail
        rw [h_last']
        -- rfl
      have h_found_var_in_trail : containsVar optional_last_lit.var s.trail.stack = true := by
        apply h_curr_assigned
        exact h_found_in_curr
      simp only [Lit.var]
      rw [AssignmentTrail.lit_neg_same_var]
      simp
      exact h_found_var_in_trail

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
    4. Resolve curr and c'
    5. set curr = resolve curr c'
    6. repeat until only one literal in curr @ s.dl
    7. set clause to learnt = True
    8. ya termine
  -/
  let seenClauses : Std.HashSet Nat := Std.HashSet.emptyWithCapacity
  let dl := s.decision_lvl

  -- We want to show that loop terminates. How do we do this?
  -- prove that the trail's size continually decreases
  let rec loop (s : Solver nv nc) (curr : Clause) (seen : Std.HashSet Nat) : (Solver nv nc × Clause) :=
    let lits_at_dl :=
      curr.lits.filter (fun (l : Lit) =>
        let var_dl := AssignmentTrail.dlOfVar s.trail l.var |>.getD 0 -- default 0 else var_dl
        var_dl = dl)
    if lits_at_dl.size == 1 then (s, curr) else 
      -- find last assigned literal l, then get ¬l
      -- NOTE: Can we guarantee that last_assigned_lit is never 0? That we always find last_assigned_lit?
      -- need to show that for all clauses found by pickIncomingEdge, last assigned variable is in trail
      -- and last assigned in curr\{last_assigned_lit} is also in trail
      let last_assigned_lit := (AssignmentTrail.findLastAssigned s.trail curr).get!
      -- pick incoming edge
      let (clause_that_implied, clause_idx) := pickIncomingEdge s (-last_assigned_lit) seenClauses
      -- resolve clause_that_implied and curr
      -- NOTE: we know that last_assigned_lit's sign in curr is the opposite of its sign in
      -- clause_that_implied

      -- TODO: Figure out if this correctly shadows
      let curr' := resolveOnVar curr clause_that_implied last_assigned_lit.var
      -- update seen clauses
      let seenClauses := seenClauses.insert clause_idx

      -- update trail
      -- NOTE: Do we know that last_assigned_lit is in s.trail before the pop?
      let s' : Solver nv nc := { s with trail := s.trail.popVar last_assigned_lit.var }



      -- TODO: Use last_assigned_lit_in_trail

      loop s' curr' seen
  partial_fixpoint

  let curr : Clause := { conflict with lits := conflict.lits.map (λ l => -l) }

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
  match bcp s with
  | Except.ok s' =>
    -- This assignment satisfies all clauses!
    if hc : s'.contingent_ct = 0 then
       Except.ok s'.assignment
    else
      -- branching!
      -- TODO: BCP Decreases Count
      have hbcp : s'.contingent_ct < s.contingent_ct := sorry
      let s_w_decide := decide (α := α) s'
      have hd : s'.contingent_ct = s_w_decide.contingent_ct := by
        simp_all
        have hsw : s_w_decide = decide (α := α) s' := rfl
        rw [hsw]
        apply decide_preserves_ct s'
      have hc : s_w_decide.contingent_ct > 0 := by
        simp_all
        omega
      have hd : s_w_decide.contingent_ct < s.contingent_ct := by omega

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
      have hd : s'''.contingent_ct < s.contingent_ct := by admit
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
