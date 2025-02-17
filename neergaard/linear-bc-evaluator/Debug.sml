(*  (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Debug.sml,v 1.6 2004/06/03 20:17:22 turtle Exp $

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

structure Debug :> Debug =
struct

(* Status on whether we want debugging information. *)
val debug_ref = ref false

(* Functions to alter or check the status of debugging information *)
fun on () = debug_ref := true
fun off () = debug_ref := false
fun debug () = !debug_ref

(* Functions to limit looping *)
val limit = ref 10
type loopwatch = Counter.counter
fun loopwatch_new factor = Counter.newWithMax (Real.round ( factor * Real.fromInt (! limit)))
fun loopwatch_step watch =
    if !debug_ref then (Counter.step watch ; ()) else ()
fun looplimit newLimit = limit := newLimit

(* Print debugging information if it is requested. *)
fun print s = if debug () then TextIO.print s else ()
fun condPrint flag = if flag then print else (fn _ => ())
fun print_value formatter value = ((print o formatter) value ; value )
end