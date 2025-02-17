(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME
    $Id: Syntax.sig,v 1.13 2004/06/04 23:38:39 turtle Exp $

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

(* This file implements the signature for handling of the syntax of
functions expressed in function algebra for polynomial time by
Bellantoni and Cook.  It contains a data type for syntax tree, pretty
printing, and type checking (i.e., whether a syntax tree represents a
valid BC function.)  *)

signature Syntax =
sig 

(* An annotated  syntax tree *)
datatype 'a AS = Zero of 'a
	       | Succ0 of 'a
	       | Succ1 of 'a
	       | Pred of 'a
	       | Cond of 'a
	       | Proj of (int * int * int * 'a)
	       | Comp of (('a AS) * ('a AS) list * ('a AS) list * 'a)
	       | Rec of ((bool * string option) * ('a AS) * ('a AS) * ('a AS) * ('a AS) * ('a AS) * 'a)

(* Return the annotation of the root node of the syntax tree *)
val annotation : 'a AS -> 'a

type S = unit AS

(* Constructors to build the raw syntax tree *)
val is_zero: 'a AS -> bool
val zero : S
val ZERO : S
val s0 : S
val s1 : S
val p : S
val c : S
val proj : int * int * int -> S
val scomp : S *S list *S list -> S
val DSrec : S * S * S * S * S-> S
val DDSrec : string * S * S * S * S * S-> S
val Srec : S * S * S * S * S-> S
val Dsrec : S * S * S -> S
val srec : S * S * S -> S

(* Maps a list in to string of comma separated elements using the
provided formatter funcition *)
val map_comma_string : ('a -> string) -> 'a list -> string

(* Format syntax tree *)
val toString: 'a AS -> string

(* Format the application; the arguments of the application are turned 
into string with the format function. *)
val apply_toString: ('a -> string) -> ('b AS) -> ('a list * 'a list) -> string

end