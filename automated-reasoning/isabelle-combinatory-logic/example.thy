theory example
  imports Main
begin

definition C :: "('a => 'b => 'c) => 'b => 'a => 'c" where
  "C f g x = f x g"

print_theorems

definition K :: "'a => 'b => 'a" where
  "K x y = x"

definition I where
  "I = C K K"

(* cannot get it to work *)
definition I :: "'a => 'a" where
  "I = (C :: _ => ('a => 'a => 'a ) => ('a => 'a)) K K"

ML {*
  case @term{\<open>C K\<close>} of
    Const(_,_) $ s => s>
*}
end