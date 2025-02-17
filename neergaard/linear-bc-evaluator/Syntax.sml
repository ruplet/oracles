(* (Linear) BC (epsilon) evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Syntax.sml,v 1.14 2004/06/04 23:38:39 turtle Exp $

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

(* This file implements handling of the syntax of functions expressed
in function algebra for polynomial time by Bellantoni and Cook.  It
contains a data type for syntax trees, pretty printing, and type
checking (i.e., whether a syntax tree represents a valid BC function.)

As for linear BC we do not provide an explicit split of the safe
arguments as in the description by Ong and Murawski.  Rather we use
the regular BC syntax and check that each safe input is used exactly
once. *)

structure Syntax :> Syntax =
struct 

(* An annotated  syntax tree *)
datatype 'a AS = Zero of 'a
	       | Succ0 of 'a
	       | Succ1 of 'a
	       | Pred of 'a
	       | Cond of 'a
	       | Proj of (int * int * int * 'a)
	       | Comp of (('a AS) * ('a AS) list * ('a AS) list * 'a)
	       | Rec of ((bool * string option) * ('a AS) * ('a AS) * ('a AS) * ('a AS) * ('a AS) * 'a)
fun annotation (Zero ann) = ann
  | annotation (Succ0 ann) = ann
  | annotation (Succ1 ann) = ann
  | annotation (Pred ann) = ann
  | annotation (Cond ann) = ann
  | annotation (Proj (_,_,_, ann)) = ann
  | annotation (Comp (_,_,_, ann)) = ann
  | annotation (Rec (_,_,_,_,_,_,ann)) = ann

type S = unit AS
 		     
(* Constructors to build raw syntax tree *)
val zero = Zero ()
val s0 = Succ0 ()
val s1 = Succ1 ()
val p = Pred ()
val c = Cond ()
fun proj (m, m', j) = Proj (m, m', j,())
fun scomp (f, gs_normal, gs_safe) = Comp (f, gs_normal, gs_safe,())
val ZERO = scomp(zero, [],[])
fun is_zero (Comp (Zero _, [],[], _)) = true
  | is_zero _ = false

fun DDSrec (desc, g, h0, d0, h1, d1) = Rec ((true,SOME desc) , g, h0, d0, h1, d1,())
fun DSrec (g, h0, d0, h1, d1) = Rec ((true,NONE) , g, h0, d0, h1, d1,())
fun Srec (g, h0, d0, h1, d1) = Rec ((false,NONE), g, h0, d0, h1, d1,())
fun Dsrec (g, h0, h1) = DSrec (g, h0, ZERO, h1, ZERO)
fun srec (g, h0, h1) = Srec (g, h0, ZERO, h1, ZERO)

(* Maps a list in to string of comma separated elements using the
provided formatter funcition *)
fun map_comma_string (f : 'a -> string) (es: 'a list)  = 
    if List.null es then " "
    else ( String.concat o List.concat )
	 [ [ " " ], 
	   ( List.tl o List.concat o List.map (fn e => [",  ", f e])) es,
	   [" "] ]

(* A pretty printing function for annotated syntax trees *)
fun toString (Zero _) = "0"
  | toString (Succ0 _) = "s_0"
  | toString (Succ1 _) = "s_1"
  | toString (Pred _) = "p"
  | toString (Cond _)= "c"
  | toString (Proj (m, m', j, _)) = "p^{" ^ Int.toString m
				     ^ "," ^ Int.toString m' 
				     ^ "}_" ^ Int.toString j
  | toString (Comp (f, gs_normal, gs_safe, _)) =
	      "(" ^ toString f ^ " o " 
	      ^ ( if ( List.length gs_normal ) + ( List.length gs_safe) = 1  
		  then ( toString o List.hd o List.@ ) (gs_normal, gs_safe)
		  else "<" ^ map_comma_string toString gs_normal ^ ";"
		       ^ map_comma_string toString gs_safe ^ ">" )
	      ^ ")"
  | toString (Rec (_, g, h0, d0, h1, d1, _)) =
    if is_zero d0 andalso is_zero d1
    then "rec" ^ "(" ^ (toString g) ^ ", " ^ (toString h0) ^ ", " ^ (toString h1) ^")"
    else "rec"  ^ "(" ^ (toString g) ^ ", " ^ (toString h0) ^ ", " ^ (toString d0) ^ ", " ^ (toString h1) ^ ", " ^ (toString d1) ^")";
    
(* A pretty printing funcion for testing *)
fun apply_toString format_arg s (normal, safe) =
	String.concat 
	    [ toString s, "(", 
	      map_comma_string format_arg normal ,";", 
	      map_comma_string format_arg safe, " )"]

end;