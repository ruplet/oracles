(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME.
    $Id: LogspaceEvaluatorFunctional.sml,v 1.3 2004/06/07 22:52:18 turtle Exp $

    Copyright 2003,2004 Peter Møller Neergaard (e-mail: turtle@achilles.linearity.org)
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

(* This file contains an evaluator for BC-_epsilon: the extended
affine fragment of BC functions (as originally defined by Murawski and
Ong and extended by Møller Neergaard).  The interpreter illustrates
that the extended linear fragment can be evaluated in logarithmic
space as described by Møller Neergaard in ``A Functional Language for
Logspace''.

The overall idea behind the evaluator is that we need only store a
fixed numbers of bits (along with the recursion depth they were found
at) for each subterm to produce one bit of the ouput.  This
fundamentally hinges on the observation that we, due to the linearity,
at each level of a recursion, only need one bit from each safe
argument.

In the end, we can evaluate recursion without storing a call stack;
instead we need to repeat part of the computation; thus trading time
for space.  We find the number produced by the function by querying
one bit at a time.  The evaluator can then find the result by querying
one bit at time.

We realize the evaluator by representing each syntactic constructor as
two higher-order functions: 

- one computes which bit of the safe argument is needed to find a
  given bit.  
- the other computes the bit we are looking for from the normal and
  safe arguments

The complexity bound is realized by observing the following facts:

- the function is tail recursive in the sense defined by Jones in
  ``Life without Cons'': the call graph is without cycles except for
  calls in tail position. Consequently the program stack is of fixed
  sized for a given program and we need only keep one environment for
  each function.

- the function arguments are either 

  - a reference to a function: this is a closure referencing to a
    fixed site; as we only have one environment for each function, the
    variables bound in the closure can be looked up in a fixed place.

  - a bit index: since all intermediate values are bound by a
    polynomial of the input, this is representable in logarithmic
    space.

On the technical level, we represent the inputs to a function as two
vectors: one with the normal arguments and one with the safe argument
(the type inputs below).  This allows us to dynamically build the
simulating function from the syntax tree as we have a uniform type for
all syntactic constructors.  A more correct implementaion would use
dependent types which are not available in SML. *)

structure LogspaceEvaluatorFunctional :> Evaluator =
(*structure LogspaceEvaluatorFunctioanal  =*)
struct

val recursionCount = Counter.new ()

(* The type for a constructor as described above *)
type bit = Bit.bit
type usage = int option
type usages = usage Vector.vector
type input = int -> bit
type inputs =  input Vector.vector
(* program is the central type which we use to represent each syntactic 
   constructor.
   safe_usage tells, given the normal arguments, what bit of each safe
     argument is needed to compute a given bit of the output;
   eval finds a given bit of the output from the inputs.   *)
type program = { safe_usage: inputs ->  int -> usages,
	          eval: inputs -> inputs -> int -> bit}

(* For debugging: pretty printing the usage information *)
fun usage_toString NONE = "X"
  | usage_toString (SOME i) = Int.toString i
fun debug_print_safe_usage_value procedure i  =
    let val safe_usage_string = (Syntax.map_comma_string usage_toString) o
				(Vector.foldr (fn (use,uses) => use::uses) [])
    in
(*	Debug.print_value (fn usage_vector => (procedure ^" (safe_usage): i="^ Int.toString i ^": [" ^ safe_usage_string usage_vector ^ "]\n"))*)
	fn x => x
    end			 

(* and parentesizing of an optional string.  The latter is used in
safe composition and recursion where we optionally can provide a
string for debugging purposes *)
fun desc_toString NONE = ""
  | desc_toString (SOME s) = "(" ^ s ^ ") "
			 
(* The empty parameter list; used in safe composition and recursion *)
val (empty : inputs) = Vector.fromList [] 

(* The following are the functions corresponding to each of the operators*)
fun zero () =
    let fun safe_usage normal i = 
	    debug_print_safe_usage_value "zero" i 
					 (Vector.fromList [])
	fun eval normal safe bt = 
	    ( Debug.condPrint false ("zero (eval): bt=" ^ Int.toString bt ^ "\n");
	      Bit.none );
    in
	{ eval=eval, safe_usage=safe_usage} : program
    end

fun succ b =
    let fun safe_usage normal i = 
	    debug_print_safe_usage_value ("succ" ^ Int.toString b) i
		(Vector.fromList [if i>0 then SOME (i-1) else NONE])
	fun eval normal safe bt = 
	    ( Debug.condPrint false ("succ" ^ Int.toString b ^" (eval): bt=" ^ Int.toString bt ^ "\n");
	      if bt = 0 then if b=0 then Bit.zero else Bit.one
	      else Vector.sub (safe,0) (bt -1))
    in
	{ eval=eval, safe_usage=safe_usage } : program
    end

fun pred () =
    let fun safe_usage normal i = 
	    debug_print_safe_usage_value "pred" i 
					 (Vector.fromList [SOME (i+1)])
	fun eval normal safe bt = 
	    ( Debug.condPrint false ("pred (eval): bt=" ^ Int.toString bt ^ "\n");
	      Vector.sub (safe,0) (bt + 1) )
    in
	{ eval=eval, safe_usage=safe_usage} : program
    end

fun cond () =
    let fun safe_usage normal i = 
	    debug_print_safe_usage_value "cond" i
		(Vector.fromList [SOME 0,SOME i,SOME i])
	fun eval normal safe bt = 
	    let val b = Vector.sub (safe,0) 0 
	    in 
		Debug.condPrint false ("cond (eval): bt=" ^ Int.toString bt ^ "\n");
		if  Bit.is_none b orelse (not o Bit.boolean) b
		then Vector.sub (safe,1) bt
		else Vector.sub (safe,2) bt 
	    end
    in
	{ eval=eval, safe_usage=safe_usage} : program
    end

fun proj (m, m', j) =
    let fun safe_usage normal i = 
	    debug_print_safe_usage_value ("proj (" ^ Int.toString m ^"," ^ Int.toString m' ^"," ^ Int.toString j ^ ")") i
	    (Vector.tabulate (m', fn j'=>if j'=j-m-1 then SOME i else NONE))
	fun eval normal safe bt = 
	    ( Debug.condPrint false ("proj (" ^ Int.toString m ^"," ^ Int.toString m' ^"," ^ Int.toString j ^ ") (eval): bt=" ^ Int.toString bt ^ "\n");
	      if j <= m 
	      then Vector.sub (normal, j - 1)  bt
	      else Vector.sub (safe, j - m -1) bt )
    in
	{ eval=eval, safe_usage=safe_usage} : program
    end

(* For the formula to compute safe usage of safe affine composition,
   recall that

      f o < g_1, ..., g_M : h_1, ..., h_N > ( x_1,...,x_m : y_1, ..., y_n )

   is 

      f( g_1 ( x_1,...,x_m :), 
	 ..., 
	 g_M ( x_1,...,x_m :) :
         h_1 ( x_1,...,x_m : y_1,1, ..., y_1,n1 ),				         ...
         h_N ( x_1,...,x_m : y_N,1, ..., y_N,nN ),				    
   where y_1,1, ..., y_1,n1, ..., y_N,1, ..., y_N,nN affinely splits
   y_1, ..., y_n.

   Due to the linearity f will request only one bit from each h_1,
   ..., h_N; this is computed by f's safe_usage function.  Similar,
   each h function, say h_i, will request only one bit from each of
   y_i,1,..., y_i,ni.  Due to the affine split y_1, ..., y_n, we find
   the bit that is requested from a given y_k, by feeding the jth
   element of f's safe_usage into h_j.  Subsequently, we rearrange the
   outputs from the h's according to how the y's are split.

   This approach is approximated below.  We first compose f with the hs.
   However, due to the representation, do not know which h function will use
   which safe arguments.  We scan through all the usage vectors to find the 
   non-NONE element to return.
 *)
fun compDesc (desc : string option)
	 (f : program)
	 (gs : program Vector.vector)
	 (hs  : program Vector.vector) 
         (nsafe : int option) =
	 let val nsafe' = case nsafe of
			      NONE => 0
			    | SOME n => n
	fun make_normal normal = 
	    let fun input_normal normal (i, g : program) bt = 
		    ( Debug.condPrint false ("comp " ^ desc_toString desc ^ "normal #"^ Int.toString (i + 1) ^ ", bt=" ^ Int.toString bt ^ "\n");
		      (#eval g) normal empty bt)
	    in 
		Vector.mapi (input_normal normal) (gs, 0, NONE)
	    end
	    
	fun safe_usage normal i = 
	    let fun empty_recq n = Vector.tabulate ((if n>=0 then n else 0), (fn _ => NONE))
	        (* Find the usage vector formed by composing one of f's request with the corresponding 
  		   h function. *) 
		fun compose recq h_safe_usage =
		    case recq of
			NONE => empty_recq nsafe'
		      | SOME j =>
			let val h_recq=h_safe_usage (make_normal normal) j
			in Vector.concat [h_recq,
					  empty_recq (nsafe'-Vector.length h_recq)]
			end
		(* Compute f's usage and the composition of f with h *)
		val f_safe_recq = (#safe_usage f) (make_normal normal) i
      		val comp_f_h_recq = Vector.mapi (fn (i,h)=> 
						    compose
							(Vector.sub (f_safe_recq, i))
							(#safe_usage (Vector.sub (hs, i))))
						(f_safe_recq,0,NONE)
	    in
		(* Scan through the composed usaged to produce the usage vector *)
		Vector.tabulate (nsafe',
	 	  fn i => 
		     Vector.foldl 
			 (fn (h_recq, prev)=>
			     let val recq=Vector.sub (h_recq, i) 
			     in
				 if recq=NONE then prev
				 else if prev=NONE then recq
				 else raise (General.Fail "This should not happen: two functions in a composition request a bit from the same safe argument")
			     end)
			 NONE
			 comp_f_h_recq)
	    end
	fun eval (normal : inputs) 
		 (safe : inputs)
		 (bt : int) =
	    let val _ = Debug.condPrint false ("comp " ^ desc_toString desc
						^ ": bt=" ^ Int.toString bt ^ "\n")
		fun input_safe (i, h:program) bt= 
			       ( Debug.condPrint false ("comp " ^ desc_toString desc ^ "safe #"^ Int.toString (i + 1) ^ ", bt=" ^ Int.toString bt ^ "\n");
				 (#eval h) normal safe bt)
		val safe = Vector.mapi input_safe (hs, 0, NONE)
	    in
		(#eval f) (make_normal normal) safe bt
	    end
    in
	{ eval=eval, safe_usage=safe_usage} : program
    end
fun comp f gs hs nsafe = compDesc NONE f gs hs nsafe

(* The non-trivial evaluation of safe affine course-of-value recursion.

   It is for this syntactic constructor we need to compute which bits
   will be needed.  We first iterate the safe_usage of the step
   functions to find the maximum recursion depth and the number of
   recursive calls needed to reach that depth.  We then loop over the 
   recursive depth each time going one recursive step shorter.
   *)

fun saferecDesc (debug: bool)
		(desc : string option)
		(h0syn : Types.T)
		(h1syn : Types.T)
		(g : program)
		(h0 : program)
		(d0 : program)
		(h1 : program)
		(d1 : program) =
    (* Iteratively find the lenght of an argument by querying from right to left *) 		
    let fun find_length (z : int -> bit) = 
	    let val _ = Debug.condPrint true ("saferec "^ desc_toString desc ^"(find_length): starting search\n")
		fun search i = if Bit.is_none (z i) then i else search (i+1)
	    in 
		Debug.print_value (fn l => "saferec "^ desc_toString desc ^"(find_length): found " ^ Int.toString l ^ "\n")
		(search 0) 
	    end
	(* Return the function representing the recursive variable at a given depth *)	
	fun input_rec_var normal depth bt = 
	    let val b = Vector.sub (normal,0) (bt + depth)
	    in
		Debug.condPrint false ("saferec: request for rec var "^ desc_toString desc ^", depth=" ^ Int.toString depth^ ", bit=" ^ Int.toString bt ^ ": " ^ Bit.toString b ^"\n");
		b
	    end
	(* Return the vector corresponding to the normal arguments at a given recursive depth *)
	fun make_normal normal depth =
	    Vector.concat [Vector.fromList [input_rec_var normal depth], 
			   Vector.extract (normal, 1, NONE)]
        (* Find the bit request and depth for a given index; if idx is NONE, it finds the deepest bit depth;
	 otherwise it stops at latest at the depth defined by idx*)
	fun bit_depth topnormal topbit maxidx =
	    let val loopwatch = Debug.loopwatch_new 1.0
		val _ = Debug.condPrint debug ("\nsaferec "^ desc_toString desc ^"(bit_depth): topbit="^ Int.toString topbit ^ ", maxidx="^ (case maxidx of NONE =>"unlimited" | SOME idx => Int.toString idx) ^"\n")
		fun search idx bt dp =
		    if (SOME idx) = maxidx then 
			( Debug.condPrint debug ( "saferec "^ desc_toString desc ^"(bit_depth): reached max index at " ^ "index=" ^ (Int.toString idx) ^"\n") ;
			{idx=idx, bt=bt, depth=dp}) 
		    else case Bit.bool_option (input_rec_var topnormal dp 0) of
			     NONE => let val depth = find_length (input_rec_var topnormal 0)
				     in 
					 {idx=idx, bt=bt, depth=depth}
				     end
			   | SOME b => 
			     let val _ = Debug.loopwatch_step loopwatch
				 val (h,d,hsyn) = if b then (h1,d1,h1syn) else (h0,d0,h0syn)

			     in
				 case 
				     Vector.sub 
					  (debug_print_safe_usage_value ("saferec "^ desc_toString desc ^"(bit_depth, search,safe_usage"^Syntax.toString hsyn^")") bt 
				         ((#safe_usage h) (make_normal topnormal (1 + dp)) bt)
					 ,0) of
				     NONE => ( Debug.condPrint debug ( "saferec "^ desc_toString desc ^"(bit_depth, search): h"^ (if b then "1" else "0") ^" bit=X, " ^ "depth=" ^ (Int.toString dp) ^ " index=" ^ (Int.toString idx) ^", bit=" ^ (Int.toString bt) ^"\n") ;
					       {idx=idx, bt=bt, depth=dp})
				   | SOME bt' =>
				     ( Debug.condPrint debug ( "saferec "^ desc_toString desc ^"(bit_depth, search): h"^ (if b then "1" else "0") ^" bit="^ Int.toString bt' ^", " ^ "depth=" ^ (Int.toString dp) ^ " index=" ^ (Int.toString idx) ^", bt=" ^ (Int.toString bt) ^"\n") ;
				       search (idx + 1) 
					    bt'
					    (dp + 1 + find_length ((#eval d) (make_normal topnormal (1 + dp)) empty)))
			     end
		val {idx=idx, bt=bt, depth=dp} = search 0 topbit 0
	    in
		Debug.condPrint debug ("saferec "^ desc_toString desc ^"(bit_depth): returning, idx="^ Int.toString idx ^ ", bt="^ Int.toString bt ^ ", depth="^ Int.toString dp ^"\n");
		{idx=idx, bt=bt, depth=dp}
	    end
	fun safe_usage normal i =
	    (* Find the deepest recursion depth: if it is the base case, we might need bits from the  
               safe arguments, otherwise none will be requested. *)
	    case bit_depth normal i NONE of
		{bt=bt, depth=dp,...} => 
		let val g_recq = (#safe_usage g) (Vector.extract (normal, 1, NONE)) bt
		in
		    (* We cheat a little for proof-of-concept; and always compute the recquest to g; 
		       if we do not call g, we overwrite it afterwards *)
		    if dp <> find_length (input_rec_var normal 0)
		    then Vector.map (fn _ => NONE) g_recq 
		    else g_recq
		end
        (* Evaluate the recursion as outlined above: compute the number of recursion and then iterate
           up to the top of the recursion *)
	fun eval (topnormal : inputs) (safe : inputs) (topbit : int) =
	    let val recursion = Counter.step recursionCount
		val _ = Debug.condPrint debug ("saferec "^ desc_toString desc ^"(eval) (rec recursion #"^Int.toString recursion ^ "): starting topbit="^ Int.toString topbit^"\n")
		val max_depth = find_length (input_rec_var topnormal 0)
		val {idx=idx,depth=depth,bt=bt} = bit_depth topnormal topbit NONE
		val _ = Debug.condPrint debug ("saferec "^ desc_toString desc ^"(eval) (rec recursion #"^Int.toString recursion ^ "): max_depth= " ^ Int.toString max_depth ^ ", depth=" ^ Int.toString depth^"\n")
		val (iterations, init) = if depth=max_depth 
					 then (idx-1,(#eval g) (Vector.extract (topnormal, 1, NONE)) safe bt)
					 else (idx, Bit.none)
		fun loop (idx, cache : bit) =
		    if idx>=0 
		    then let val {depth=depth,bt=bt,...} = bit_depth topnormal topbit (SOME idx)
			     val b = Bit.boolean (input_rec_var  topnormal depth 0)
			     val _ = Debug.condPrint false ( "saferec: loop, " ^ "depth=" ^ (Int.toString depth) ^ ", b=" ^ (if b then "1" else "0") ^", bt=" ^ (Int.toString bt) ^"\n")
			     val h = if  b then h1 else h0
			 in
			     loop (idx -1,(#eval h) (make_normal topnormal depth) 
						    (Vector.fromList [fn _ => cache]) bt)
			 end
		    else cache
	    in
		loop (iterations, init)
	    end
    in
	{ safe_usage=safe_usage, eval=eval} : program
    end
val saferec = saferecDesc false NONE
val Dsaferec = saferecDesc true NONE

(* Converting a syntax tree of the function to the internal computation *)
fun fromTypedSyntax (Syntax.Zero _) = zero ()
  | fromTypedSyntax (Syntax.Succ0 _) = succ 0
  | fromTypedSyntax (Syntax.Succ1 _) = succ 1
  | fromTypedSyntax (Syntax.Pred _) = pred () 
  | fromTypedSyntax (Syntax.Cond _) = cond ()
  | fromTypedSyntax (Syntax.Proj (m, m', j, _)) = proj (m, m', j)
  | fromTypedSyntax (s as Syntax.Comp (f, gs, hs, _)) =
    let val desc = Syntax.toString s
	val F = fromTypedSyntax f
	val GS = (Vector.fromList o (List.map fromTypedSyntax)) gs
	val HS = (Vector.fromList o (List.map fromTypedSyntax)) hs
    in compDesc (SOME desc) F GS HS (Types.root_safe s) end
  | fromTypedSyntax (s as Syntax.Rec ((debug,desc), g, h0, d0, h1, d1, _)) =
    let val G = fromTypedSyntax g
	val H0 = fromTypedSyntax h0
	val D0 = fromTypedSyntax d0
	val H1 = fromTypedSyntax h1
	val D1 = fromTypedSyntax d1
    in saferecDesc debug desc h0 h1 G H0 D0 H1 D1 end

(* Obtaining the result by querying bit by bit. *)
local open Numbers in
fun evaluate p normal safe =
    let fun bit_nth n j =
	    ( (* Debug.print ("global input (" ^ toString n ^ "): bt=" ^ Int.toString j ^ ": " ^ "\n"); *)
	      Numbers.bit_nth n j )
	val normal = ((Vector.map bit_nth) o Vector.fromList) normal
	val safe = ((Vector.map bit_nth) o Vector.fromList) safe
	fun iter_eval_bit acc bt =
	    ( Debug.print ("\nOuter loop, finding bit #" ^ Int.toString bt ^ "\n");
	      case Bit.bool_option (p normal safe bt) of
		  NONE => acc
		| SOME b => iter_eval_bit (if b then set_nth acc bt else acc) (bt + 1))
    in 
	iter_eval_bit ((binary o fromInt) 0) 0 
    end
end

fun eval T = evaluate (#eval (fromTypedSyntax T)) 
(* The type checking evaluator. *)
fun eval_bc b = raise Types.TypeFailure ;
fun eval_bcm b = eval ( Types.verify_linear_bc b )
fun eval_bcmeps b = eval ( Types.verify_linear_bc_epsilon b )

end