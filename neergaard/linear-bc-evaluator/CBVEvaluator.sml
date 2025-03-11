(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME.
    $Id: CBVEvaluator.sml,v 1.18 2004/06/07 22:52:18 turtle Exp $

    Copyright 2003 Peter M�ller Neergaard (e-mail: turtle@achilles.linearity.org)
    and Harry Mairson.

    This file is part of BC Evaluator.

    BC Evaluator is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
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

(* This file contains an interpreter BC functions.  The evaluator is
call-by-value except for recursive calls.  Note in particular that
both branches of a conditional are evaluated.  Recursive calls are
evaluated lazily, i.e., using call-by-need.  A function call is thus
evaluated at most once. *)

structure CBVEvaluator : Evaluator =
struct 

exception DummyReferenced;

(* The data structure for arguments.  We use thunks to postpone the
evaluation of a recursive argument.  The normal and safe arguments
are stored as two vector lists. *)
datatype 'a Thunk = Dummy
	       | Evaluated of Numbers.int
	       | Delayed of { debug : bool,
			      b: 'a Syntax.AS, 
			      normal: 'a Argument Vector.vector,
			      safe: 'a Argument Vector.vector,
			      no: int }
and 'a Argument = Value of Numbers.int
  | Thunk of ('a Thunk) ref 
type 'a arguments = 'a Argument Vector.vector * 'a Argument Vector.vector

(* For the sake of debugging we number each thunk used through out the evaueuation. *)
val thunk_count = ref 0;

(* A debugging function constructing the string representation of a value. *)
fun thunk_toString Dummy = "Dummy"
  | thunk_toString (Evaluated n) = Numbers.toString n
  | thunk_toString (Delayed thk) = "Thunk #" ^ Int.toString (#no thk)

fun argument_toString (Value n) = Numbers.toString n
  | argument_toString (Thunk thunk_ref) = thunk_toString (!thunk_ref)

(* Build an argument list from a list of integers *)
fun vector_toList vec = Vector.foldr (op ::) [] vec
(*: 'a Argument Vector.vector -> 'a Argument list)  *)
fun make_arguments arg_list = 
    (Vector.fromList o (List.map (fn v => Value v))) arg_list
fun arguments_toString arg_list = 
    (( Syntax.map_comma_string argument_toString ) o vector_toList) arg_list
fun empty () = Vector.fromList []

(* Helper function to slice a vector *)
fun vector_slice (vec, start, len_opt) =
    let
        val len = case len_opt of
                      NONE => Vector.length vec - start
                    | SOME l => l
    in
        Vector.tabulate (len, fn i => Vector.sub (vec, start + i))
    end

local open Syntax in
local open Numbers in 
val toBinary =  binary o fromInt			   
fun evaluate (linear: bool)  =
    (* Auxiliary functions to pick out an argument; they use an
    internal function defined below *)
let fun evaluate'  ((args as (normal, safe)): 'a arguments) b =
	let fun normal_only (normal, safe) = (normal, empty ())
	    fun nth args n  =
	    let val arg = Vector.sub (args, n - 1) 
		    handle Subscript => 
			   if n >= 0 then 
			       raise General.Fail ("Argument mismatch: indexed "
						   ^ " #" ^ (Int.toString n) ^ "; only "
	   					   ^ Int.toString (Vector.length args) ^ " given. " )
			   else raise Subscript
	    in case arg of
		   Value n => n
		 | Thunk thk_ref => thunkref_value thk_ref
	    end
	    val _ = Debug.condPrint true  
				    ((apply_toString argument_toString 
						     b 
						     (vector_toList normal, vector_toList safe))^"\n") ; 
	in
	    case b of
		(Syntax.Zero _) => toBinary 0 
	      | (Syntax.Succ0 _) => lshift 1 (nth safe 1, toBinary 0)
	      | (Syntax.Succ1 _) => lshift 1 (nth safe 1, toBinary 1)
	      | (Syntax.Pred _) => rshift 1 ( nth safe 1) 
	      | (Syntax.Cond _) => let val b = bit_nth (nth safe 1) 0
				   in 
				       (nth safe 
					    (if Bit.is_none b orelse (not o Bit.boolean) b then 2 else 3))
				   end
	      | (Syntax.Proj (m,m',j,_)) => if j <= m then nth normal j 
				   else  nth safe (j - m) 
	      | (Syntax.Comp (f, gs_normal, gs_safe,_)) =>
		let fun eval_arguments eval = make_arguments o (List.map eval)
		in evaluate' ((eval_arguments (evaluate' (normal_only args) ) gs_normal),
			      (eval_arguments (evaluate' args) gs_safe))
			     f
		end
	      | (Syntax.Rec ((debug,desc), g, h0, d0, h1, d1,_) ) =>
		let val n = nth normal 1
		in if zero n
		   then evaluate' ((vector_slice (normal, 1, NONE)),safe) g
		   else
		       let val n' = rshift 1 n
			   val (h, delta) = if Bit.boolean ( bit_nth n 0)
		  			    then (h1, d1)
		  			    else (h0, d0)
			   val updated_normal = 
		  	       Vector.concat [Vector.fromList [Value n'], 
		  			      vector_slice (normal, 1, 
		  					      SOME (Vector.length normal - 1))]
			   val dVal = (evaluate' (updated_normal, empty ()) delta)
			   val d = 1 + log dVal
			   val recursive_normal = 
		  	       Vector.concat [Vector.fromList 
		  				  [Value (rshift d n')], 
		  				  vector_slice (normal, 1, 
		  						  SOME (Vector.length normal - 1))]
			   val thunk_ref = ref ( Dummy )
			   val _ = thunk_count := !thunk_count + 1
			   val _ = Debug.condPrint debug ("dVal=" ^ toString dVal 
		  					  ^ ", d=" ^ Int.toString d 
		  					  ^ "; thunk #"^ Int.toString (!thunk_count)
		  					  ^ " created : " ^ Syntax.toString b 
		  					  ^", normal=["
		  					  ^ arguments_toString normal
		  					  ^ "], rec_normal=["
		  					  ^ arguments_toString recursive_normal ^"]\n")
			   val _ = thunk_ref := (Delayed {b=b, 
		  					  debug=debug,
		  					  normal=recursive_normal,
		  					  safe=safe,
		  					  no= !thunk_count} )
			   val updated_safe =
		  	       Vector.concat [if linear then empty () else safe,
		  			      Vector.fromList [Thunk thunk_ref]]
		       in 
			   evaluate' (updated_normal, updated_safe) h
		   end
		end
		    end
    (* The internal function to pick out an argument of an argument
       list.  If the argument is an unevaluated thunk we evaluate the
       thunk and updates the value.  *)
    and thunkref_value thk_ref =
	case !thk_ref of 
	    Dummy => raise DummyReferenced
	  | ( Evaluated n ) => n
	  | ( Delayed thk ) => 
	    (* Note that due to the syntactic restrictions of BC we do
	      not run the usual risks of thunks referencing themselves
	      (check the creation of thunks above in the evaluation of
	      a recursive function). *)
	    let val v = evaluate' (#normal thk, #safe thk) (#b thk)
	    in 
		Debug.condPrint (#debug thk) 
				("Thunk " ^ Int.toString (#no thk)
				 ^ " evaluated to " ^ toString v ^ "\n" );
		thk_ref := Evaluated v ; 
		v
	    end
in 
	evaluate' 
end

end (* open Syntax *)		
end (* open Numbers *)		


(* The evaluator functions *)
fun eval linear b normal safe =
    evaluate linear ((make_arguments normal), (make_arguments safe)) b
fun eval_bc b = eval false (Types.verify_bc b)
fun eval_bcm b = eval true (Types.verify_linear_bc b)
fun eval_bcmeps b = eval true ( Types.verify_linear_bc_epsilon b )

end 

							      