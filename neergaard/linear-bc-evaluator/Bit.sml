(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Bit.sml,v 1.2 2004/06/04 23:38:39 turtle Exp $

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

(* This file implements various utilities for the  manipulation of a bit. *)

structure Bit :> Bit =
struct

type bit = bool option

val none = NONE
val zero = SOME false
val one = SOME true

fun is_none b = b=NONE

fun fromBoolOption (b : bool option) = b : bit

fun boolean NONE = raise General.Domain
  | boolean (SOME b) = b

fun bool_option (b : bit) = b

(* Turns a bit into a string *)
fun toString NONE = "X"
  | toString (SOME false) = "0"
  | toString (SOME true) = "1"				 

end;