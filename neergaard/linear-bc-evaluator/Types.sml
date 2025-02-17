(* (Linear) BC (epsilon) evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Types.sml,v 1.3 2004/06/03 20:17:22 turtle Exp $

    Copyright 2003 Peter Møller Neergaard (e-mail: turtle@achilles.linearity.org) 
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

(* This file implements the signature for handling of types on the syntax 
   trees.  It has the basic type definition as well as type annotated syntax 
   trees and type checking. *)

structure Types :> Types =
struct 

(* A type is a tuple descriping the number of normal and safe arguments,
   and a list of which safe arguments are used (if this part is NONE, 
   there is no information on the usage *)
type typing= (int * int * (int list option)) option
type T = typing Syntax.AS

(* Create a typing from its normal, safe and usage lise *)
fun create n s use =
    if n = 0 andalso s=0 then (NONE : typing)
    else (SOME (n, s, SOME use):typing)

(* Like create, except that the arguments can be optional as results of 
   unification. *) 
fun create_optional n s use =
    let val n = case n of
	    	    NONE => 0
		  | SOME n => n
	val s = case s of
	    	    NONE => 0
		  | SOME s => s
	val use = case use of
		      NONE => []
		    | SOME use => use
				
    in
	create n s use
    end
 		     

(* Type checking, i.e., checking that safe composition and safe
recursion fulfills the requirements put down for the number of
arguments. *)

(* Types are represented as an optional tuple consisting of the number
of normal arguments, the number of safe arguments, and a synthesized
list of safe arguments being used.  The latter is used to check the
affinity of the safe arguments in safe linear composition.  If the
type is NONE, it means any type. *)

(* Debugging: pretty print a type *)
fun toString (NONE : typing) = "ANY"
  | toString (SOME (n, s, _))  = "(" ^ (Int.toString n) 
	       			 ^ ":" ^  (Int.toString s) ^ ")"
val type_toString = toString (* Aliasing when Syntax is opened below *)

fun arg_toString NONE = "ANY"
  | arg_toString (SOME n)  = Int.toString n

(* Indication of a type error. *)
exception TypeFailure

(* In the internals of the type checking, we represent the individual
arguments in the same fashion: as an optional argument.  The following
functions access the individual arguments of a type. *)
fun normal (NONE:typing) = NONE
  | normal (SOME (n, s, us)) = SOME n
fun safe (NONE:typing) = NONE
  | safe (SOME (n, s, us)) = SOME s
fun safe_usage (NONE:typing) = []
  | safe_usage (SOME (n, s, NONE)) = raise TypeFailure
  | safe_usage (SOME (n, s, SOME us)) = us

val root_normal = normal o Syntax.annotation
val root_safe = safe o Syntax.annotation
val root_safe_usage = safe_usage o Syntax.annotation

(* Lift a value to an argument type. *)
fun lift a = SOME a

(* Apply a function to an argument. *)
fun arg_apply f NONE = NONE
  | arg_apply f (SOME a) = SOME (f a)

(* Unification of safe or normal arguments; they have to be equal. *)
fun unify_equal (n1: int, n2: int) = if n1 = n2 then n1 else raise TypeFailure
(* Unification of two usage lists: they must not contain the same argument. *) 
fun unify_usage (us1, us2) =
    let fun member xs x = List.exists (fn x' => x=x') xs 
    in
	if (List.null o List.filter (member us1)) us2
	then us1 @ us2
	else raise TypeFailure
    end

(* Auxiliary function that unifies two type arguments; the unification
procedure to be used if none of the arguments are ANY is supplied as a
function and is expected to raise the exception typeFailure if two
elements cannot be unified. *)
fun arg_unify unifier (SOME a, SOME b) = SOME (unifier (a, b))
  | arg_unify unifier (a, NONE ) = a
  | arg_unify unifier (NONE, b ) = b

(* Unify one of the arguments from a list of types; we can supply a base case or not. *) 
fun unify_list_base pick_arg unifier base types =
    List.foldl unifier base (List.map pick_arg types)
fun unify_arg_list_base pick_arg unifier base types =
    unify_list_base pick_arg (arg_unify unifier) base types
fun unify_arg_list pick_arg unifier types =
    unify_arg_list_base pick_arg unifier NONE types

(* Verify containment in the class of linear BC functions. It embodies
a very primitive form of type inference: a nulary function fits into
any context.  This is encoded through the marker NONE. *)
local open Syntax in 
fun verify_syntax displacement_allowed safe_linear b =
    let fun verify_syntax' b =
	    case b of 
		(Zero _)=> (Zero (create 0 0 []):T)
	      | (Succ0 _) => Succ0 (create 0 1 [1])
	      | (Succ1 _) => Succ1 (create 0 1 [1])
	      | (Pred _) => Pred (create 0 1 [1])
	      | (Cond _) => Cond (create 0 3 [1,2,3])
	      | (Proj (m, m', j, _)) => 
		Proj (m, m', j, create m m' (if j <= m then [] else [j-m]))
	      |  (Comp (f, gs, hs, _)) =>
		 let val f' = (verify_syntax' f : T)
		     val gs' = List.map verify_syntax' gs
		     val hs' = List.map verify_syntax' hs
		     val f_type = annotation f'
		     val gs_types = List.map annotation gs'
		     val hs_types = List.map annotation hs'
		     val _ = Debug.print ("verify_syntax': " 
					  ^ toString b 
					  ^ ", f=" ^ (type_toString f_type)
					  ^ ", gs=" ^ (Syntax.map_comma_string type_toString gs_types)
					  ^ ", hs=" ^ (Syntax.map_comma_string type_toString hs_types)
					  ^ "\n" );
			 val norm = unify_arg_list normal 
						   unify_equal
						   (gs_types @ hs_types)
		 	 val _ = Debug.print ("               normal = " ^ (arg_toString norm))
			 val saf = unify_arg_list safe unify_equal hs_types
			 val _ = Debug.print (", safe = " ^ (arg_toString saf))
			 val usage = if safe_linear 
				     then SOME (unify_list_base safe_usage unify_usage [] hs_types)
				     else NONE
			 val _ = Debug.print ", usage = OK"
			 (* The following is only done for debugging *)
			 val nosafe = unify_arg_list_base safe unify_equal (lift 0) gs_types
			 val fnorm = (arg_unify unify_equal) ((normal f_type), ((lift o List.length) gs_types))
			 val fsaf = (arg_unify unify_equal) ((safe f_type), ((lift o List.length) hs_types))
			 val _ = Debug.print (", fnormal = " ^ (arg_toString fnorm) 
					      ^ ", fsafe = " ^ (arg_toString fsaf) 
					      ^ ", nosafe = " ^ (arg_toString nosafe) ^ "\n")
		 in
		     Comp (f', gs', hs', create_optional norm saf usage)		 
		 end
	      | (Rec (flag, g, h0, d0, h1, d1, _)) =>
		let val g' = verify_syntax' g
		    val h0' = verify_syntax' h0
		    val d0' = verify_syntax' d0
		    val h1' = verify_syntax' h1
		    val d1' = verify_syntax' d1
		    val g_type = annotation g'
		    val h0_type = annotation h0'
		    val d0_type = annotation d0'
		    val h1_type = annotation h1'
		    val d1_type = annotation d1'
		    val _ = Debug.print ( "Verify_syntax: rec, " ^ toString b
					  ^ ", g="  ^ type_toString g_type
					  ^ ", h0=" ^ type_toString h0_type
					  ^ ", d0=" ^ type_toString d0_type
					  ^ ", h1=" ^ type_toString h1_type
					  ^ ", d0=" ^ type_toString d1_type
					  ^ "\n" )
		    val norm = unify_arg_list_base normal 
		     				     unify_equal
						     (arg_apply (fn n => n+1) (normal g_type))
						     [h0_type,d0_type,h1_type,d1_type]
		    val _ = Debug.print ("               normal = " ^ (arg_toString norm))
		    val c_step = unify_arg_list_base safe 
		     				     unify_equal
		     				     (lift 1)
		     				     [h0_type,h1_type]
		    val _ = Debug.print (", step = " ^ (arg_toString c_step))
		    val c_disp = unify_arg_list_base safe
		     				     unify_equal
		     				     (lift 0)
		     				     [d0_type,d1_type]
		    val _ = Debug.print (", disp = " ^ (arg_toString c_disp) ^ "\n")
		in
		    if displacement_allowed
		       orelse (is_zero d0 andalso is_zero d1)
		    then 
			Rec (flag, g', h0', d0', h1', d1', create_optional norm (safe g_type) (SOME (safe_usage g_type)))
		    else raise TypeFailure
		end
    in
	verify_syntax' b
    end
end

fun verify_bc s = verify_syntax false false s
fun verify_linear_bc s = verify_syntax false true s
fun verify_linear_bc_epsilon s = verify_syntax true true s

end;