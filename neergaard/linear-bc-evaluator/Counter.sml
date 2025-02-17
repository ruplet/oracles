(*  (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Counter.sml,v 1.1 2003/12/23 06:55:32 turtle Exp $

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

(* This file implements handling of optional debugging information. *)

structure Counter :> Counter =
struct

type counter = (int * (int option)) ref  (* (count, limit) *)

val (value : counter -> int)  = #1 o !
val toString = Int.toString o value

fun newWithMax max = ref (0, SOME max)
fun new () = ref (0, NONE)
fun step c =
    ( c := (case !c of
	       ( v, NONE) => (v+1, NONE)
	     | ( v, SOME l) =>
	       if v <= l then (v+1, SOME l)
	       else raise Overflow );
      value c)


end