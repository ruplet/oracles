theory hilbert_bck
  imports Pure
begin

typedecl bck_prop

judgment Trueprop :: "bck_prop => prop" ("(_)" 5)

axiomatization 
  implies :: "bck_prop => bck_prop => bck_prop" (infixr "->" 6)
where
  B: "(B -> C) -> (A -> B) -> A -> C" and
  C: "(A -> B -> C) -> B -> A -> C" and
  K: "A -> (B -> A)" and
  mp: "[|A -> B; A|] ==> B"

(* Theorem idea: I = CKK, and type of I = x -> x
   Ix = x
   CKKx = (((C K) K) x) 
   realizer of K is function K x y -> x
   realizer of C is C f g x = f x g
   C K K x = K x K
   K x K = x

   you need to solve unification problem to convert such a statement to
   an actual Hilbert-style proof
   *)
theorem identity_theorem: "a -> a"
proof -
  have k: "a -> (a -> a -> a) -> a" by (rule K)
  have c: "(a -> (a -> a -> a) -> a) -> (a -> a -> a) -> a -> a" by (rule C)
  from mp c k have ck: "(a -> a -> a) -> a -> a" .
  have k2: "a -> a -> a" by (rule K)
  from ck and k2 have "a -> a" by (rule mp)
  thus ?thesis .
qed



(* Define the combinators C and K in Isabelle/Pure *)
definition C :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
  "C f g x = f x (g x)"
end