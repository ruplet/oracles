(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Types.sig,v 1.1 2004/06/02 23:10:53 turtle Exp $

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

(* This file implements the signature for handling of types on the syntax 
   trees.  It has the basic type definition as well as type annotated syntax 
   trees and type checking. *)

signature Types =
sig 

exception TypeFailure ;

type typing
type T = typing Syntax.AS

val toString : typing -> string

(* Return the typing information for the root *)
val root_normal: T -> int option
val root_safe: T -> int option
val root_safe_usage: T -> int list
(* raises TypeFailure if safe variables do not have linearity condition *)


(* Functions to verify the correctness of a program; it returns the
type in the form of the number of safe and normal arguments.  In the
case of linear_bc verifies it also verifies that safe composition can
be linearized.  The more options allows my additinonal primitives. *)
val verify_bc : 'a Syntax.AS -> T
val verify_linear_bc : 'a Syntax.AS -> T
val verify_linear_bc_epsilon : 'a Syntax.AS -> T

end