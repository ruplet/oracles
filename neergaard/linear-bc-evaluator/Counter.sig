(*  (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Counter.sig,v 1.1 2003/12/23 06:55:32 turtle Exp $

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

signature Counter =
sig
    
    type counter

    (* Functions to manipulate a counter *)
    val new : unit -> counter
    val newWithMax : int -> counter
    val step : counter -> int
    val value : counter -> int

    val toString : counter -> string
end
