/- Automatically generated Lean file for Hamilton cycle IPC formula -/
import Mathlib.Tactic.ITauto

variable (v_1_1 : Prop)
variable (v_1_not_1 : Prop)
variable (v_1_2 : Prop)
variable (v_1_not_2 : Prop)
variable (v_1_3 : Prop)
variable (v_1_not_3 : Prop)
variable (v_1_prime_1 : Prop)
variable (goal0 : Prop)
variable (v_2_1 : Prop)
variable (v_2_not_1 : Prop)
variable (v_2_2 : Prop)
variable (v_2_not_2 : Prop)
variable (v_2_3 : Prop)
variable (v_2_not_3 : Prop)
variable (v_2_prime_1 : Prop)
variable (goal1 : Prop)
variable (v_3_1 : Prop)
variable (v_3_not_1 : Prop)
variable (v_3_2 : Prop)
variable (v_3_not_2 : Prop)
variable (v_3_3 : Prop)
variable (v_3_not_3 : Prop)
variable (v_3_prime_1 : Prop)
variable (goal2 : Prop)
variable (goal3 : Prop)

theorem ipc_formula :
  goal3 → ((v_1_1 → v_2_not_1 → v_3_not_1 → goal1) → goal0) → ((v_2_1 → v_1_not_1 → v_3_not_1 → goal1) → goal0) → ((v_3_1 → v_1_not_1 → v_2_not_1 → goal1) → goal0) → (v_1_not_1 → v_3_1 → (v_1_2 → v_2_not_2 → v_3_not_2 → goal2) → goal1) → (v_2_not_1 → v_1_1 → (v_2_2 → v_1_not_2 → v_3_not_2 → goal2) → goal1) → (v_3_not_1 → v_2_1 → (v_3_2 → v_1_not_2 → v_2_not_2 → goal2) → goal1) → (v_1_not_1 → v_1_not_2 → v_3_2 → (v_1_3 → v_2_not_3 → v_3_not_3 → goal3) → goal2) → (v_2_not_1 → v_2_not_2 → v_1_2 → (v_2_3 → v_1_not_3 → v_3_not_3 → goal3) → goal2) → (v_3_not_1 → v_3_not_2 → v_2_2 → (v_3_3 → v_1_not_3 → v_2_not_3 → goal3) → goal2) → goal0 :=
by itauto

#print ipc_formula

-- here, you can extract the Hamilton cycle by examining the function body
-- to which ipc_formula evaluates to.
-- specifically, you take a look which assumptions (h0, h1, h7, ...) are called  with some arguments
-- in the body, there are also  new premises h1662 etc. used as arguments, but these are
-- not important. But when you see e.g. => h7

-- example for above:
-- fun v_1_1 v_1_not_1 v_1_2 v_1_not_2 v_1_3 v_1_not_3 goal0 v_2_1 v_2_not_1 v_2_2 v_2_not_2 v_2_3 v_2_not_3 goal1 v_3_1
  --   v_3_not_1 v_3_2 v_3_not_2 v_3_3 v_3_not_3 goal2 goal3 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
  -- h1 fun h10 h11 h12 => h5 h11 h10 fun h7696 h7697 h7698 => h9 h12 h7698 h7696 fun h7708 h7709 h7710 => h0

  -- here, after all the main fun args, you have => and then h1 fun h10 h11, ...
  -- it means that you call h1 with some function as argument. So you call h1 with something,
  -- which means you use premise h1 = ((v_1_1 → v_2_not_1 → v_3_not_1 → goal1) → goal0)
  -- so you prove goal0 using v_1_1, so v_1 is the node chosen in first step!
