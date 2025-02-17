(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME.
    $Id: Examples.sml,v 1.15 2004/06/07 22:52:18 turtle Exp $

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

(* This file contains various examples that can be used to test the evaluators. *)

structure Examples =
struct

(* The most primive syntax trees. *)
val zero = Syntax.zero
val ZERO = Syntax.ZERO
val s0 = Syntax.s0
val s1 = Syntax.s1
val p = Syntax.p
val c = Syntax.c

local open Syntax in

val one = scomp (s1, [], [zero])
val two = scomp (s0, [], [scomp (s1, [],[zero])])
val three = scomp (s1, [], [scomp (s1, [],[zero])])

val ONE = one
val TWO = scomp (s1, [], [ONE])
val THREE = scomp (s1, [], [TWO])
val FOUR = scomp (s1, [], [THREE])
val FIVE = scomp (s1, [], [FOUR])
val SIX = scomp (s1, [], [FIVE])
val SEVEN = scomp (s1, [], [SIX])
val EIGHT = scomp (s1, [], [SEVEN])
val NINE = scomp (s1, [], [EIGHT])
val TEN = scomp (s1, [], [NINE])
val ELEVEN = scomp (s1, [], [TEN])
val TWELVE = scomp (s1, [], [ELEVEN])
val THIRTEEN = scomp (s1, [], [TWELVE])
val FOURTEEN = scomp (s1, [], [THIRTEEN])
val FIFTEEN = scomp (s1, [], [FOURTEEN])

(* Test of composition *)
val s001 = scomp (s1, [], [scomp (s0, [], [s0])])
val c_normal = scomp (c, [], [proj (3,0,1), proj (3,0,2), proj (3,0,3)])
val double = scomp(c, [], [proj (1,1,2), proj (1,1,2), proj (1,1,2)])

(* Test of recursion *)
val invert = Dsrec ( zero, scomp (s1, [], [proj(1,1,2)]), scomp (s0, [], [proj(1,1,2)]) )
val invert_double = srec ( zero, 
			   scomp (s1, [], [scomp (s1, [], [proj(1,1,2)])]),
			   scomp (s0, [], [scomp (s0, [], [proj(1,1,2)])]))

(* The example function that would take exponential time using call by name. *)
val cbv_show = srec ( two, double, double )

(* Some functions taken from the paper on bc-minus epsilon *)
(* Subtraction *)
val minus = DSrec( proj(0,1,1), 
		  ZERO, 
		  ZERO, 
		  scomp ( p, [], [proj (1,1,2)]),
		  ZERO)

(* Division *)
val pdiv = 
    scomp (p, 
	   [],
	   [ scomp (DDSrec ("div",
			    ZERO, 
			    ZERO, 
			    ZERO,
			    scomp (s1, [], [proj (2,1,3)]),
			    proj(2,0,2)),
		    [scomp (s1, [], [proj(2,0,1)]),
		     scomp (p, [], [proj (2,0,2)])],[])])

val plog = DDSrec ("log",
		   ZERO, 
		  ZERO, 
		  ZERO,
		  scomp (s1, [], [proj(1,1,2)]),
		  scomp (pdiv, 
			 [ proj(1,0,1), TWO ],
			 []))

end (* open Syntax *)

(* Print the result of an evaluation. *)
fun print_eval eval (exp, name, e : 'a Syntax.AS, normal, safe) = 
    let val value = eval e normal safe
    in 
	( print o String.concat )
	    ( [ if Numbers.equal value exp then "   " else "!! ", 
		name, " (",
		Syntax.apply_toString Numbers.toString e (normal, safe),
		" ) = ", Numbers.toString value,
		" (Expected: ", Numbers.toString  exp,
		")\n" ] )
    end 
handle Types.TypeFailure => print ( "!! " ^ name ^ ": Not type correct input.\n")

(* A test suite of functions. *)
val b = Numbers.binary
val u = Numbers.unary
fun test_suite eval = 
    ( List.map ( print_eval eval) ( 
				   (b 0, "zero", zero, [], []) ::
				   (b 1, "one", one, [], []) ::
				   (b 2, "two", two, [], []) ::
				   (b 3, "three", three, [], []) ::
				   (b 0, "ZERO", ZERO, [], []) ::
				   (b 1, "ONE", ONE, [], []) ::
				   (b 3, "TWO", TWO, [], []) ::
				   (b 7, "THREE", THREE, [], []) ::
				   (b 6, "succ0", s0, [], [b 3]) ::
				   (b 7, "succ1", s1, [], [b 3]) ::
				   (b 0, "pred", p, [], [b 0]) ::
				   (b 1, "pred", p, [], [b 3]) ::
				   (b 1, "cond", c, [], [b 3,b 2,b 1]) ::
				   (b 2, "cond", c, [], [b 4,b 2,b 1]) ::
				   (b 1, "2", s001, [], [b 0]) ::
				   (b 9, "2", s001, [], [b 1]) ::
				   (b 1, "condNormal", c_normal, [b 3,b 2,b 1], [])  ::
				   (b 2, "condNormal", c_normal, [b 4,b 2,b 1], []) ::
				   (b 2, "two", two, [], []) ::
				   (b 3, "double", double, [b 1], [b 3]) ::
				   (b 4, "double", double, [b 42], [b 4]) ::
				   (b 3, "invert", invert, [b 4], []) ::
				   (b 15,"invert_double",  invert_double, [b 4], []) ::
				   (b 2, "cbv_show", cbv_show, [b 1], []) ::
				   (b 2, "cbv_show", cbv_show, [b 2], []) ::
				   (b 2, "cbv_show", cbv_show, [b 100], []) ::
				   (u 7, "minus (linear only)", minus, [ u 5], [u 12] ) ::
				   (u 0, "minus (linear only)", minus, [ u 12], [u 5] ) ::
				   (u 7, "div", pdiv, [u 23, u 3], []) ::  
				   (u 4, "log", plog, [u 13], []) ::  
				   nil);
      ())


end