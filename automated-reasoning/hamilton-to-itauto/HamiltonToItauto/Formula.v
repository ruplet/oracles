(* this is very slow! it doesn't segfault or anything,
   but this is probably exponential in number of premises,
   which is ~100?

   here, we solve hamilton using a general PSPACE-complete IPL
   proof searching. but we can also do better, by reducing
   Hamilton even further, to BCK logic, and using NP-complete
   BCK logic proof search!
*)
Section Formula.

Variable (v_1_1 : Prop).
Variable (v_1_not_1 : Prop).
Variable (v_1_2 : Prop).
Variable (v_1_not_2 : Prop).
Variable (v_1_3 : Prop).
Variable (v_1_not_3 : Prop).
Variable (v_1_4 : Prop).
Variable (v_1_not_4 : Prop).
Variable (v_1_5 : Prop).
Variable (v_1_not_5 : Prop).
Variable (v_1_prime_1 : Prop).
Variable (goal0 : Prop).
Variable (v_2_1 : Prop).
Variable (v_2_not_1 : Prop).
Variable (v_2_2 : Prop).
Variable (v_2_not_2 : Prop).
Variable (v_2_3 : Prop).
Variable (v_2_not_3 : Prop).
Variable (v_2_4 : Prop).
Variable (v_2_not_4 : Prop).
Variable (v_2_5 : Prop).
Variable (v_2_not_5 : Prop).
Variable (v_2_prime_1 : Prop).
Variable (goal1 : Prop).
Variable (v_3_1 : Prop).
Variable (v_3_not_1 : Prop).
Variable (v_3_2 : Prop).
Variable (v_3_not_2 : Prop).
Variable (v_3_3 : Prop).
Variable (v_3_not_3 : Prop).
Variable (v_3_4 : Prop).
Variable (v_3_not_4 : Prop).
Variable (v_3_5 : Prop).
Variable (v_3_not_5 : Prop).
Variable (v_3_prime_1 : Prop).
Variable (goal2 : Prop).
Variable (v_4_1 : Prop).
Variable (v_4_not_1 : Prop).
Variable (v_4_2 : Prop).
Variable (v_4_not_2 : Prop).
Variable (v_4_3 : Prop).
Variable (v_4_not_3 : Prop).
Variable (v_4_4 : Prop).
Variable (v_4_not_4 : Prop).
Variable (v_4_5 : Prop).
Variable (v_4_not_5 : Prop).
Variable (v_4_prime_1 : Prop).
Variable (goal3 : Prop).
Variable (v_5_1 : Prop).
Variable (v_5_not_1 : Prop).
Variable (v_5_2 : Prop).
Variable (v_5_not_2 : Prop).
Variable (v_5_3 : Prop).
Variable (v_5_not_3 : Prop).
Variable (v_5_4 : Prop).
Variable (v_5_not_4 : Prop).
Variable (v_5_5 : Prop).
Variable (v_5_not_5 : Prop).
Variable (v_5_prime_1 : Prop).
Variable (goal4 : Prop).
Variable (goal5 : Prop).

Theorem ipc_formula : 
  goal5 -> ((v_1_1 -> v_2_not_1 -> v_3_not_1 -> v_4_not_1 -> v_5_not_1 -> goal1) -> goal0) -> ((v_2_1 -> v_1_not_1 -> v_3_not_1 -> v_4_not_1 -> v_5_not_1 -> goal1) -> goal0) -> ((v_3_1 -> v_1_not_1 -> v_2_not_1 -> v_4_not_1 -> v_5_not_1 -> goal1) -> goal0) -> ((v_4_1 -> v_1_not_1 -> v_2_not_1 -> v_3_not_1 -> v_5_not_1 -> goal1) -> goal0) -> ((v_5_1 -> v_1_not_1 -> v_2_not_1 -> v_3_not_1 -> v_4_not_1 -> goal1) -> goal0) -> (v_1_not_1 -> v_2_1 -> (v_1_2 -> v_2_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_1_not_1 -> v_4_1 -> (v_1_2 -> v_2_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_2_not_1 -> v_1_1 -> (v_2_2 -> v_1_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_2_not_1 -> v_3_1 -> (v_2_2 -> v_1_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_2_not_1 -> v_4_1 -> (v_2_2 -> v_1_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_2_not_1 -> v_5_1 -> (v_2_2 -> v_1_not_2 -> v_3_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_3_not_1 -> v_2_1 -> (v_3_2 -> v_1_not_2 -> v_2_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_3_not_1 -> v_5_1 -> (v_3_2 -> v_1_not_2 -> v_2_not_2 -> v_4_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_4_not_1 -> v_1_1 -> (v_4_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_4_not_1 -> v_2_1 -> (v_4_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_4_not_1 -> v_5_1 -> (v_4_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_5_not_2 -> goal2) -> goal1) -> (v_5_not_1 -> v_2_1 -> (v_5_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_4_not_2 -> goal2) -> goal1) -> (v_5_not_1 -> v_3_1 -> (v_5_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_4_not_2 -> goal2) -> goal1) -> (v_5_not_1 -> v_4_1 -> (v_5_2 -> v_1_not_2 -> v_2_not_2 -> v_3_not_2 -> v_4_not_2 -> goal2) -> goal1) -> (v_1_not_1 -> v_1_not_2 -> v_2_2 -> (v_1_3 -> v_2_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_1_not_1 -> v_1_not_2 -> v_4_2 -> (v_1_3 -> v_2_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_2_not_1 -> v_2_not_2 -> v_1_2 -> (v_2_3 -> v_1_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_2_not_1 -> v_2_not_2 -> v_3_2 -> (v_2_3 -> v_1_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_2_not_1 -> v_2_not_2 -> v_4_2 -> (v_2_3 -> v_1_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_2_not_1 -> v_2_not_2 -> v_5_2 -> (v_2_3 -> v_1_not_3 -> v_3_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_3_not_1 -> v_3_not_2 -> v_2_2 -> (v_3_3 -> v_1_not_3 -> v_2_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_3_not_1 -> v_3_not_2 -> v_5_2 -> (v_3_3 -> v_1_not_3 -> v_2_not_3 -> v_4_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_4_not_1 -> v_4_not_2 -> v_1_2 -> (v_4_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_4_not_1 -> v_4_not_2 -> v_2_2 -> (v_4_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_4_not_1 -> v_4_not_2 -> v_5_2 -> (v_4_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_5_not_3 -> goal3) -> goal2) -> (v_5_not_1 -> v_5_not_2 -> v_2_2 -> (v_5_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_4_not_3 -> goal3) -> goal2) -> (v_5_not_1 -> v_5_not_2 -> v_3_2 -> (v_5_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_4_not_3 -> goal3) -> goal2) -> (v_5_not_1 -> v_5_not_2 -> v_4_2 -> (v_5_3 -> v_1_not_3 -> v_2_not_3 -> v_3_not_3 -> v_4_not_3 -> goal3) -> goal2) -> (v_1_not_1 -> v_1_not_2 -> v_1_not_3 -> v_2_3 -> (v_1_4 -> v_2_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_1_not_1 -> v_1_not_2 -> v_1_not_3 -> v_4_3 -> (v_1_4 -> v_2_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_1_3 -> (v_2_4 -> v_1_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_3_3 -> (v_2_4 -> v_1_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_4_3 -> (v_2_4 -> v_1_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_5_3 -> (v_2_4 -> v_1_not_4 -> v_3_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_3_not_1 -> v_3_not_2 -> v_3_not_3 -> v_2_3 -> (v_3_4 -> v_1_not_4 -> v_2_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_3_not_1 -> v_3_not_2 -> v_3_not_3 -> v_5_3 -> (v_3_4 -> v_1_not_4 -> v_2_not_4 -> v_4_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_1_3 -> (v_4_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_2_3 -> (v_4_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_5_3 -> (v_4_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_5_not_4 -> goal4) -> goal3) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_2_3 -> (v_5_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_4_not_4 -> goal4) -> goal3) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_3_3 -> (v_5_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_4_not_4 -> goal4) -> goal3) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_4_3 -> (v_5_4 -> v_1_not_4 -> v_2_not_4 -> v_3_not_4 -> v_4_not_4 -> goal4) -> goal3) -> (v_1_not_1 -> v_1_not_2 -> v_1_not_3 -> v_1_not_4 -> v_2_4 -> (v_1_5 -> v_2_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_1_not_1 -> v_1_not_2 -> v_1_not_3 -> v_1_not_4 -> v_4_4 -> (v_1_5 -> v_2_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_2_not_4 -> v_1_4 -> (v_2_5 -> v_1_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_2_not_4 -> v_3_4 -> (v_2_5 -> v_1_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_2_not_4 -> v_4_4 -> (v_2_5 -> v_1_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_2_not_1 -> v_2_not_2 -> v_2_not_3 -> v_2_not_4 -> v_5_4 -> (v_2_5 -> v_1_not_5 -> v_3_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_3_not_1 -> v_3_not_2 -> v_3_not_3 -> v_3_not_4 -> v_2_4 -> (v_3_5 -> v_1_not_5 -> v_2_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_3_not_1 -> v_3_not_2 -> v_3_not_3 -> v_3_not_4 -> v_5_4 -> (v_3_5 -> v_1_not_5 -> v_2_not_5 -> v_4_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_4_not_4 -> v_1_4 -> (v_4_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_4_not_4 -> v_2_4 -> (v_4_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_4_not_1 -> v_4_not_2 -> v_4_not_3 -> v_4_not_4 -> v_5_4 -> (v_4_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_5_not_5 -> goal5) -> goal4) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_5_not_4 -> v_2_4 -> (v_5_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_4_not_5 -> goal5) -> goal4) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_5_not_4 -> v_3_4 -> (v_5_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_4_not_5 -> goal5) -> goal4) -> (v_5_not_1 -> v_5_not_2 -> v_5_not_3 -> v_5_not_4 -> v_4_4 -> (v_5_5 -> v_1_not_5 -> v_2_not_5 -> v_3_not_5 -> v_4_not_5 -> goal5) -> goal4) -> goal0.
Proof.
  tauto.

Qed.

Print ipc_formula.

End Formula.