(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME.
    $Id: LogspaceEvaluatorFunc.sml,v 1.4 2004/06/04 23:38:39 turtle Exp $

    Copyright 2003 Peter M�ller Neergaard (e-mail: turtle@achilles.linearity.org)
    and Harry Mairson.

    This file is part of BC Evaluator.

    BC Evaluator is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public Licnese as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    BC Evaluator is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with BC Evaluator; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*)

(* This file contains an evaluator for the extended affine fragment
of BC functions (as originally defined by Murawski and Ong and
extended by M�ller Neergaard).  The interpreter illustrates that the
extended linear fragment can be evaluated in logarithmic space as
described by M�ller Neergaard. 

The evaluator works by querying one bit at a time.  In this we need
only store a fixed number of bits for each operator along with a
record of which bit we are storing.

We realize the evaluator by representing each syntactic constructor as
a higher-order function taking the following arguments:

- the normal arguments: a vector of functions which given a bit index returns the bit
- the safe arguments: a vector of functions which given a bit index returns the bit
- the bit of the constructor's result we want.
We represent the bits with an option type so we can recognize when we
``run out of bits'' in the recursion.  This is captured in the type
program below.
The constructors for safe composition and safe recursion becomes
higher-order functions over the type program.  

The complexity bound is realized by observing the following facts:

- the call graph is without cycles; consequently the program stack is
  of fixed sized for a given program and we need only keep one
  environment for each function.

- the function arguments are either 

  - a reference to a function: this is a closure referencing to a
    fixed site; as we only have one environment for each function, the
    variables bound in the closure can be looked up in a fixed place.

  - a bit index: since all intermediate values are bound by a
    polynomial of the input, this is representable in logarithmic
    space.

*)

structure LogspaceEvaluatorFunc :> Evaluator =
(*structure LogspaceEvaluatorFunc  =*)
struct

(* The type for a constructor as described above *)
type bit = Bit.bit
type input = (int -> bit) Vector.vector
type program = input -> input -> int -> bit

(* and parentesize an optional string.  The latter is used in safe
composition and recursion where we optionally can provide a string for
debugging purposes *)
fun desc_toString NONE = ""
  | desc_toString (SOME s) = "(" ^ s ^ ") "
			 
(* The empty parameter list; used in safe composition and recursion *)
val (empty : input) = Vector.fromList [] 

(* The following are the functions corresponding to each of the operators*)
fun zero normal safe bit = 
    ( Debug.condPrint false  ("zero: bit=" ^ Int.toString bit ^ "\n");
      Bit.none ) : bit;

fun succ b normal safe bit = 
    ( Debug.condPrint false  ("succ" ^ Int.toString b ^": bit=" ^ Int.toString bit ^ "\n");
    if bit = 0 then if b=1 then Bit.one else Bit.zero
    else Vector.sub (safe,0) (bit -1)) : bit

fun pred normal safe bit = 
    ( Debug.condPrint false  ("pred: bit=" ^ Int.toString bit ^ "\n");
    Vector.sub (safe,0) (bit + 1) ) : bit

fun cond normal safe bit = 
    let val b = (Vector.sub (safe,0)) 0
    in
	Debug.condPrint false  ("cond: bit=" ^ Int.toString bit ^ "\n");
	( if Bit.is_none b orelse (not o Bit.boolean) b
	  then Vector.sub (safe,1) bit
	  else Vector.sub (safe,2) bit ) : bit
    end

fun proj (m, m', j) normal safe bit = 
    ( Debug.condPrint false  ("proj (" ^ Int.toString m 
		   ^"," ^ Int.toString m' 
		   ^"," ^ Int.toString j ^ 
		   "): bit=" ^ Int.toString bit ^ "\n");
    if j <= m 
    then Vector.sub (normal, j - 1)  bit
    else Vector.sub (safe, j - m -1) bit ) : bit


fun compDesc (desc : string option)
	 (f : program)
	 (gs : program Vector.vector)
	 (hs  : program Vector.vector)
	 (normal : input) 
	 (safe : input)
	 (bit : int) =
    let val _ = Debug.condPrint false  ("comp " ^ desc_toString desc
			     ^ ": bit=" ^ Int.toString bit ^ "\n")
	fun input_normal (i, g) bit = 
	    ( Debug.condPrint false  ("comp " 
			   ^ desc_toString desc 
			   ^ "normal #"^ Int.toString (i + 1) 
			   ^ ", bit=" ^ Int.toString bit ^ "\n");
	      g normal empty bit)
	fun input_safe (i, h) bit= 
	    ( Debug.condPrint false  ("comp " 
			   ^ desc_toString desc 
			   ^ "safe #"^ Int.toString (i + 1) 
			   ^ ", bit=" ^ Int.toString bit ^ "\n");
	      h normal safe bit)
	val normal = Vector.mapi input_normal gs
	val safe = Vector.mapi  input_safe hs
    in
	f normal safe bit : bit
    end
val comp = compDesc NONE


(* The non-trivial evaluation of safe recursion.  We exploit the fact
that there is at most one reference to the recursive call in the step
function.  This makes it sufficient to store just one bit of recursive
call: We start evaluating the function for the bit requested; if it
turns out that we need the bit of the recursive call we replace the
request with a request for the bit from the recusive call and restart
the computation.  This can again lead to a new request and a restarted
computation, but eventually we will ``run out of bits'' as we reach
the base case.  We store the bit we find in the base case and the
depth we found it at.  We can then restart the whole recursion once
more, but this time stop one step from the base case because we have
cached the result from the base case.  Restarting again, we can stop
two steps from the base case.  Continuning in this fashion we will
eventually have the requested bit. *)

(* An exception used to mark that the recursion should be restarted;
as recursions we assign a unique number to each recursion so we can
distinguish them *)
val recursionCount = Counter.new ()
exception Restart of int 

(* A looping construct: keeps evaluating body until it retuns true. *)
fun loop body = if body () then () else loop body

(* The cache of results contain the depth and the bit value *)
val NORESULT = { depth = ~1, res = Bit.none }

(* Helper function to slice a vector *)
fun vector_slice (vec, start, len_opt) =
    let
        val len = case len_opt of
                      NONE => Vector.length vec - start
                    | SOME l => l
    in
        Vector.tabulate (len, fn i => Vector.sub (vec, start + i))
    end

fun saferecDesc (debug: bool)
		(desc : string option)
		(g : program)
		(h0 : program)
		(d0 : program)
		(h1 : program)
		(d1 : program)
		(normal : input)
		(safe : input)
		(bit : int) =
    let val loopwatch = Debug.loopwatch_new 1.0
	val recursion = Counter.step recursionCount
	val _ = Debug.condPrint debug ("\nStarting safe recursion #"^Int.toString recursion ^ " "
			     ^ desc_toString desc 
			     ^"for bit "^ Int.toString bit^"\n")
	val result = ref NORESULT
	val goal = ref ({ bit=bit, depth=0 })
	(* The normal parameters used in the recursion; as we descend
	in the recursion the recursive parameter is effectively
	shifted right *)
	fun lsb () = Vector.sub (normal,0) (#depth (!goal))
	fun input_recVar bit = 
	    ( Debug.condPrint debug ("saferec: request for rec var" 
			   ^ ", depth=" ^ Int.toString (#depth (!goal))
			   ^ ", bit=" ^ Int.toString bit  ^"\n");
			Vector.sub (normal,0) (1 + bit + #depth (!goal)))
	val normal = Vector.concat [Vector.fromList [input_recVar], 
				    vector_slice (normal, 1, NONE)]
	fun recursiveCall (d : program) (bit : int) =
	    (* Compute the displacement by querying the bits of the delta function *)
	    let val _ = Debug.condPrint debug ("saferec: request for rec call ("
				     ^ Int.toString recursion
				     ^ "), depth=" ^  Int.toString (#depth (!goal))
				     ^ ", bit=" ^ Int.toString bit ^ "\n")
		fun find_length i = 
		    ( Debug.condPrint debug ("find_length: i=" ^ Int.toString i ^ "\n");
		      if Bit.is_none (d normal empty i) then i else find_length (i+1))
		val delta = 1 + find_length 0
		val _ = Debug.condPrint debug ("saferec: request for rec call"
				     ^ ", depth=" ^  Int.toString (#depth (!goal))
				     ^ ", bit=" ^ Int.toString bit
				     ^ ", delta=" ^ Int.toString delta )
	    in 
		(* If the requested bit is cached, return it; otherwise restart *)
		if #depth (!goal) + delta = #depth (!result) 
		then ( Debug.condPrint debug "---found in cache\n"; 
		       #res (!result) )
		else 
		    ( Debug.condPrint debug ("---restarting "^ Int.toString recursion ^"\n") ; 
		     goal := { bit=bit, depth = #depth (!goal) + delta };
		     raise ( Restart recursion ) )
	    end
    in 
	(* The double loop described above: the outermost loop starts
	the computation from the top; the innter loop takes care of
	restarting whenever we replace the query by. *)
	( loop 
	     (fn () =>
		 ( goal := { bit=bit, depth=0 };
		   loop (fn () => 
			    let val _ = Debug.loopwatch_step loopwatch
				val lsb = lsb ()
				val _ = Debug.condPrint debug ("saferec (" ^ Int.toString recursion 
						     ^"): goal: bit=" ^ Int.toString (#bit (!goal))
						     ^ ", depth=" ^ Int.toString (#depth (!goal))
						     ^ "; cached: depth=" 
						     ^ Int.toString (#depth (!result))
						     ^ ", res=" ^ Bit.toString (#res (!result))
						     ^ "; lsb=" ^ Bit.toString lsb ^"\n")
				val res = case Bit.bool_option lsb of
					      NONE => g (vector_slice (normal, 1, NONE)) safe
							(#bit (!goal))
					    | SOME b => 
					      let val (h, d) = if b then (h1,d1) else (h0,d0)
					      in 
						  h normal 
						    (Vector.fromList [recursiveCall d]) 
						    (#bit (!goal)) 
					      end
			    in ( result := { depth = #depth (!goal), res=res };
				 Debug.condPrint debug ( "saferec: caching result, " 
					       ^ "depth=" ^ Int.toString (#depth (!goal)) 
					       ^", res=" ^ Bit.toString res ^"\n") ;
				 true )
			    end handle (exn as (Restart r)) => 
				       if r=recursion then false else raise exn);
		   0 = #depth (!result) ));
	     #res (!result)) 
    end
val saferec = saferecDesc false NONE
val Dsaferec = saferecDesc true NONE

(* Converting a syntax tree of the function to the internal computation *)
fun fromSyntax (Syntax.Zero _) = zero
  | fromSyntax (Syntax.Succ0 _) = succ 0
  | fromSyntax (Syntax.Succ1 _) = succ 1
  | fromSyntax (Syntax.Pred _) = pred
  | fromSyntax (Syntax.Cond _) = cond
  | fromSyntax (Syntax.Proj (m, m', j, _)) = proj (m, m', j)
  | fromSyntax (s as Syntax.Comp (f, gs, hs, _)) =
    let val desc = Syntax.toString s
	val F = fromSyntax f
	val GS = (Vector.fromList o (List.map fromSyntax)) gs
	val HS = (Vector.fromList o (List.map fromSyntax)) hs
    in compDesc (SOME desc) F GS HS end
  | fromSyntax (s as Syntax.Rec ((debug,desc), g, h0, d0, h1, d1, _)) =
    let val G = fromSyntax g
	val H0 = fromSyntax h0
	val D0 = fromSyntax d0
	val H1 = fromSyntax h1
	val D1 = fromSyntax d1
    in saferecDesc debug desc  G H0 D0 H1 D1 end

(* Obtaining the result by querying bit by bit. *)
local open Numbers in
fun evaluate p normal safe =
    let fun bit_nth n j =
	    ( Debug.print ("global input (" ^ toString n ^ "): bit=" ^ Int.toString j ^ "\n");
	      Numbers.bit_nth n j )
	val normal = ((Vector.map bit_nth) o Vector.fromList) normal
	val safe = ((Vector.map bit_nth) o Vector.fromList) safe
	fun iter_eval_bit acc bit =
	    ( Debug.print ("\nOuter loop, finding bit #" ^ Int.toString bit ^ "\n");
	      case Bit.bool_option (p normal safe bit) of
		  NONE => acc
		| SOME b => iter_eval_bit (if b then set_nth acc bit else acc) (bit + 1))
    in 
	iter_eval_bit ((binary o fromInt) 0) 0 
    end
end

fun eval t = evaluate (fromSyntax t) 
(* The type checking evaluator. *)
fun eval_bc b = raise Types.TypeFailure ;
fun eval_bcm b = eval ( Types.verify_linear_bc b )
fun eval_bcmeps b = eval ( Types.verify_linear_bc_epsilon b )

end