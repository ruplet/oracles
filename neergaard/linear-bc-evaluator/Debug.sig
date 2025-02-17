(*  (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Debug.sig,v 1.5 2004/06/03 20:17:22 turtle Exp $

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

signature Debug =
sig
    (* Functions to alter or check the status of debugging information *)
    val debug : unit -> bool
    val off : unit -> unit
    val on : unit -> unit

    (* Functions to limit looping *)
    type loopwatch
    val loopwatch_new : real -> loopwatch
    val loopwatch_step : loopwatch -> unit  (* Raises overflow *)
    val looplimit : int -> unit

    (* Print debugging information if it is requested. *)
    val print : string -> unit
    val condPrint : bool -> string -> unit
    val print_value : ('a -> string) -> 'a -> 'a				      
end
