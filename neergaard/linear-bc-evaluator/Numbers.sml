(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Numbers.sml,v 1.8 2004/06/04 23:38:39 turtle Exp $

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

(* This file implements various utilities for manipulation of numbers. *)

structure Numbers :> Numbers =
struct

(* We specify the implementation's name for a large integer here:*)
(* This is for SML/NJ *)
type LargeInt = LargeInt.int  
fun binary n = n
val fromInt = LargeInt.fromInt
val toString = LargeInt.toString
val compare = LargeInt.compare 


(* This is for  Moscow ML *)
(*type LargeInt = Int.int 
fun binary n = n
val fromInt = binary
val toString = Int.toString
val compare = Int.compare *)

type int = LargeInt

fun equal m n = (compare (m,n)) = EQUAL
val zero = equal 0

(* unary n Makes the unary representation of the number n, i.e., a number with n 1's *)


fun exp k (n : LargeInt)  = 
    (* An iterative (tail-recursive) exponentation:
       It is easiliest understood by recalling that as

         k = 2^m b_m + ... + 2^0 b_0

       we have

         n^k = n^{2^m b_m + ... + 2^0 b_0}
             = n^{2^m b_m} * ... * n^{2^0 b_0} .

       Now, n^{2^i b_i} is either n^{2^i} (if b_i = 1) or 1.
       The implementation below lets m go through the values of 
       n^{2^i} while acc keeps the product. *) 
    let fun exp' 0 m acc = acc
	  | exp' 1 m acc = acc * m
	  | exp' k m acc = exp' (k div 2) 
		    (m * m)
		    ( if k mod 2 = 0 then acc
		      else acc * m )
    in 
	exp' k n 1
    end handle Overflow => raise General.Fail ( "Overflow in exp, n=" ^ (toString n) ^ ", k=" ^ (Int.toString k))

fun unary (n : LargeInt) = exp (Int.fromLarge n) 2 - 1

fun lshift j (n, b) = n * (exp j 2) + (b mod (exp j 2))
    handle Overflow => raise General.Fail ( "Overflow in lshift, n=" ^ (toString n) ^ ", j=" ^ (Int.toString j))
fun rshift j n = n div (exp j 2)
    handle Overflow => raise General.Fail ( "Overflow in rshift, n=" ^ (toString n) ^ ", j=" ^ (Int.toString j))
fun log (n : int) = 
    let fun loop 0 l = l
	  | loop n l = loop (n div 2) (l + 1)
    in
	loop n ~1
    end handle Overflow => raise General.Fail ( "Overflow in log, n=" ^ (toString n))

fun fromBinary n = n
fun fromUnary n = fromInt ( 1 + log n)

(* Picking bit j of the number n. *)
fun bit_nth n j = let val shifted = rshift j n
		  in
		      if shifted = 0 then Bit.fromBoolOption NONE
		      else if Int.fromLarge ( shifted mod 2 ) = 0 then Bit.fromBoolOption (SOME false)
		      else Bit.fromBoolOption (SOME true)
		  end 
		      handle Overflow => 
			     raise General.Fail ( "Overflow in rshift, n=" ^ (toString n) 
						  ^ ", j=" ^ (Int.toString j))

(* Setting bit j of the number n. *)
fun set_nth n j = 
    let val b = bit_nth n j
    in
	if Bit.is_none b orelse (not o Bit.boolean) b
	then n + (exp j 2)
	else n
    end

end;