(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Numbers.sig,v 1.6 2004/06/03 20:17:22 turtle Exp $

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

(* This file implements the interface for various utilities for
manipulation of numbers. It is implemented with a hidden type so we
can change the implementation without worrying about the rest of the
interpreter, e.g., we can implement very large integers *)

signature Numbers =
sig

    (* We specify the implementation's name for a large integer here:*)
    type LargeInt = LargeInt.int  (* SML/NJ*)
    (*type LargeInt = Int.int (* Moscow ML *)*)
    (* This is a little misplaced here, but it is for historical reasons:
       exp k n = n^k *)
    val fromInt : Int.int -> LargeInt

    (* This hides the concrete type of integer from the implementation *)
    type int 

    (* Lifting into the domain and pretty print the number *)
    val binary : LargeInt -> int
    val unary : LargeInt -> int
    val toString : int -> string
    val fromBinary :  int -> LargeInt
    val fromUnary :  int -> LargeInt

    (* Comparisons *)			  
    val compare : int * int -> order
    val equal : int -> int -> bool
    val zero : int -> bool

    (* shift j (k,b) = left shift k by j adding b as the bottom bits *)				
    val lshift : Int.int -> (int * int) -> int

    (* shift j k = right shift n by j *)				
    val rshift : Int.int -> int -> int

    (* log n = logarithm of n *)
    val log : int -> Int.int
			    
    (* bit_nth n j = bit j of the number n *)
    val bit_nth : int -> Int.int -> Bit.bit

    (* set_nth n j = set the bit j of the number n *)
    val set_nth : int -> Int.int -> int


end

