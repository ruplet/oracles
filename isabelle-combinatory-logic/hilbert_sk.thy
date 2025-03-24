theory hilbert_sk
  imports Pure
begin

typedecl sk_prop

judgment Trueprop :: "sk_prop => prop" ("(_)" 5)

axiomatization 
  implies :: "sk_prop => sk_prop => sk_prop" (infixr "->" 6)
where
  K: "A -> (B -> A)" and
  S: "(A -> (B -> C)) -> ((A -> B) -> (A -> C))" and

mp: "[|A -> B; A|] ==> B"

theorem identity_theorem: "A -> A"
proof -
  have step1: "A -> (A -> A)" by (rule K)
  have step2: "A -> ((A -> A) -> A)" by (rule K)
  have step3: "(A -> ((A -> A) -> A)) -> ((A -> (A -> A)) -> (A -> A))" by (rule S)
  from mp step3 step2 have step4: "(A -> (A -> A)) -> (A -> A)" .
  from mp step4 step1 have step5: "A -> A" .
  thus ?thesis .
qed

end