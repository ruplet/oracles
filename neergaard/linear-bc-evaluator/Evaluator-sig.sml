(*  (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Evaluator-sig.sml,v 1.10 2004/06/02 23:23:12 turtle Exp $

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

(* This file contains the common signature for the two evaluator structures. *)

signature Evaluator =
sig

    (* BC function evaluator that also checks that the input is a
    valid function.  If not the exception Syntax.TypeFailure is
    raised. *)
    val eval_bc : 'a Syntax.AS -> Numbers.int list -> Numbers.int list -> Numbers.int
    val eval_bcm : 'a Syntax.AS -> Numbers.int list -> Numbers.int list -> Numbers.int
    val eval_bcmeps : 'a Syntax.AS -> Numbers.int list -> Numbers.int list -> Numbers.int

end
