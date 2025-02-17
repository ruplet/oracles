(* (Linear) BC evaluator: evaluator of Bellantoni-Cook's function algebra for PTIME.
    $Id: LogspaceEvaluator.sml,v 1.16 2004/06/04 23:38:39 turtle Exp $

    Copyright 2003 Peter Møller Neergaard (e-mail: turtle@achilles.linearity.org)
    and Harry Mairson.

    This file is part of BC Evaluator.

    BC Evaluator is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public Licnese as published by
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

(* This file contains an interpreter for the linear fragment of BC
functions (as defined by Murawski and Ong).  The interpreter
illustrates that the linear fragment can be evaluated in logarithmic
space as described by Møller Neergaard and Mairson. The complexity
bound is realized by observing the following facts:

- the only data structure used is an augmented syntax tree.  The
  number of nodes is thus fixed for a given program and it can be seen
  that it only takes logarithmic space to store a node.  

- the main loop of the program is a while loop and there is no
  recursive call.  The call stick is thus fixed in size.

The interpreter uses a rather involved data structure consisting of an
execution stack and and a computation window caching recently
evaluated values. *)

structure LogspaceEvaluator :> Evaluator =
struct

(* This is the rather involved data structure used to record the
information used in the logspace-evaluator.  Compared to the paper we
have chosen the solution of augmenting the syntax tree (we call this
the execution tree).  We have therefore removed the labels from the
stack entry and the computation window; they are only used to identify
the node in the syntax tree.  We have added a reference to the
previous stack entry to the stack record. 

Since we need a double linked data structure we cannot do with an
ordinary inductive data type, but have to build the whole structure
using explicit references.  

Furthermore, we have an extra node, Top, on the top of the execution
stack.  This is as placeholder for the whole computation when the
outermost constructor is a recursion: it holds the bit that we are
looking for at the top level. *)

(* The various types of nodes. *)
datatype S = Zero
	   | Succ0
	   | Succ1
	   | Pred 
	   | Cond 
	   | Proj of (int * int * int)
	   | Comp of ((ExecNode ref) * (ExecNode ref) list * (ExecNode ref) list)
	   | Rec of (bool * ExecNode ref * ExecNode ref * ExecNode ref * ExecNode ref * ExecNode ref * int)
	   | Top of ExecNode ref
(* The information stored in a node. *)
and ExecNode = N of S
		    * {parent: ExecNode ref, child_idx:int} option ref
		    * {pop: ExecNode ref option, n:int, r:int,
		       e:(SourceDesc * int) Array.array} option ref
		    * {bit:Bit.bit, n:int, r:int} option ref
(* A description of the source *)
and SourceDesc = SInput of int 
		(* An input to the program; 1-based *)
               | SComp of ExecNode ref
	       | SRec of ExecNode ref * int

(* Some useful type abbreviations. *)
type program_label = ExecNode ref 			 
type source = SourceDesc * int

(* Access the parts stored in a node *)
fun n_internal (f: ExecNode -> 'a) (label: program_label) = f (! label)
val (n_type : program_label -> S)  = n_internal (fn (N (s, parent, stack, window)) => s)
val n_parent_ref = n_internal (fn (N (s, parent, stack, window)) => parent)
val n_parent = ! o n_parent_ref
val n_stack_ref = n_internal (fn (N (s, parent,stack, window)) => stack)
val n_stack = ! o n_stack_ref
val n_window_ref = n_internal (fn (N (s, parent, stack, window)) => window)
val n_window = ! o n_window_ref



(* Auxiliary function to turn an array into a list. *)
fun array_toList (arr : 'a Array.array) = Array.foldr (op ::) [] arr

(* and an auxiliary function to create a subarray. *)
fun subarray slice = 
    let val vec = Array.extract slice
    in Array.tabulate (Vector.length vec,
		       fn i => Vector.sub (vec,i))
    end

(* Shift a source right *)
fun shift s' ((desc, s) : source) = ((desc, s + s') : source)

(* Function used in the debugging to turn an execution tree into a
standard syntax tree. *)
fun exec_toS (tree: program_label) =
    case n_type tree of
	Zero => Syntax.zero
      | Succ0 => Syntax.s0
      | Succ1 => Syntax.s1
      | Pred => Syntax.p
      | Cond => Syntax.c
      | Proj (m, m', j) => Syntax.proj (m,m',j)
      | Comp (f, gs_normal, gs_safe) => Syntax.scomp (exec_toS f,
						     List.map exec_toS gs_normal,
						     List.map exec_toS gs_safe)
      | Rec (debug, g, h0, d0, h1, d1, _) => 
	if debug then 
	    Syntax.DSrec(exec_toS g, exec_toS h0,exec_toS d0, exec_toS h1, exec_toS d1)
	else
	    Syntax.Srec(exec_toS g, exec_toS h0,exec_toS d0, exec_toS h1, exec_toS d1)

      | Top s => exec_toS s

fun exec_toString s =
    case n_type s of
	Top _ => "top"
      | _  => (Syntax.toString o exec_toS) s

(* Build the execution tree from the syntax tree.  We create a new
reference cell for each node in the syntax tree.

Note that we for each node with subtrees first process the subtrees
inserting an empty parent pointer.  Then after creating the cell for
the node, the node is inserted as parent in the subtrees. *)
fun exec_tree_build (b : Types.T)  =
    let fun exec_tree_build' b =
 	    let fun new_cell b' = ref (N ( b', ref NONE, ref NONE, ref NONE))
	    in case b of 
		   (Syntax.Zero _) => new_cell ( Zero)
		 | (Syntax.Succ0 _)	=> new_cell ( Succ0 )
		 | (Syntax.Succ1 _) => new_cell ( Succ1 )
		 | (Syntax.Pred _) => new_cell ( Pred )
		 | (Syntax.Cond _) => new_cell ( Cond )
		 | (Syntax.Proj (m,m',j,_)) => new_cell ( Proj(m,m',j) )
		 | (Syntax.Comp (f, gs_normal, gs_safe,_)) =>
		   let val f' = exec_tree_build' f
		       val gs_normal' = List.map exec_tree_build' gs_normal
		       val gs_safe' = List.map exec_tree_build' gs_safe
		       val comp' = new_cell ( Comp ( f', gs_normal', gs_safe') )
		       fun map_parent_upd subs =
			(* Update a list subtrees such that the parent link and the
			child index is inserted correctly. *)
			   List.map (fn (sub, n) => 
					n_parent_ref sub := SOME {parent=comp',
								  child_idx=n} )
				    (ListPair.zip (subs,
						   List.tabulate (List.length subs,
								  fn i=> i + 1)))
		   in 
		       n_parent_ref f' := SOME {parent=comp', child_idx=0};
		       map_parent_upd (gs_normal' @ gs_safe');
		       comp'
		   end
		 | (record as (Syntax.Rec  ((debug,desc), g, h0, d0, h1, d1, _))) =>
		   let val g' = exec_tree_build' g
		       val h0' = exec_tree_build' h0
		       val d0' = exec_tree_build' d0
		       val h1' = exec_tree_build' h1	
		       val d1' = exec_tree_build' d1
		       val nsafe =  case Types.root_safe record of 
					NONE => 0
				      | SOME s => s
		       val rec' = new_cell ( Rec ( debug, g', h0', d0', h1', d1', nsafe))
		   in 
		       n_parent_ref g' := SOME {parent=rec', child_idx=1};
		       n_parent_ref h0' := SOME {parent=rec', child_idx=2};
		       n_parent_ref h1' := SOME {parent=rec', child_idx=3};
		       n_parent_ref d0' := SOME {parent=rec', child_idx=4};
		       n_parent_ref d1' := SOME {parent=rec', child_idx=5};
		       rec'
		   end
	    end
	val tree = exec_tree_build' b
	val top = ref (N (Top tree, ref NONE, ref NONE, ref NONE))  
    in
	n_parent_ref tree := SOME {parent=top, child_idx=1};
	top 
    end

(* Auxiliary function clearing the execution window entries kept in
the subtrees of a node.  Note that the node itself is not cleared. *)
fun exec_tree_clear_windows (b: program_label) =
    let fun window_is_not_empty NONE = false
	  | window_is_not_empty _ = true
	fun exec_tree_clear_windows' clear b =
	    ( if clear andalso window_is_not_empty (n_window b)
	      then
		  let val SOME win = n_window b
		  in
		      Debug.print ("(" ^ Bit.toString (#bit win)
				   ^ "," ^ Int.toString (#n win)
				   ^ "," ^ Int.toString (#r win)
				   ^ ") @ " ^ exec_toString b ^" ");
		      n_window_ref b := NONE 
		  end else () ; 
	      case n_type b of
		  Comp (f, gs_normal, gs_safe) =>
		  ( List.map (exec_tree_clear_windows' true) gs_normal;
		    List.map (exec_tree_clear_windows' true) gs_safe ; 
		    exec_tree_clear_windows' true f )
		| Rec (_, g, h0, d0, h1, d1, _) =>
		  ( exec_tree_clear_windows' true g;
		    exec_tree_clear_windows' true h0;
		    exec_tree_clear_windows' true d0;
		    exec_tree_clear_windows' true h1;
		    exec_tree_clear_windows' true d1 )
		| Top f => exec_tree_clear_windows' true f
		| _ => () )
    in
	Debug.print ("exec_tree_clear_windows: clearing [ ");
	exec_tree_clear_windows' false b;
	Debug.print ("]\n")
    end

(* Debugging functions giving string representation of the various data structures. *)
fun src_toString (SInput n) = "inp " ^ Int.toString n
  | src_toString (SComp node) = "cmp " ^ exec_toString node
  | src_toString (SRec (node, r)) = "rec " ^ Int.toString r

val env_toString =
    Syntax.map_comma_string (fn (src, s) => "(" ^ src_toString src ^ "," 
					    ^ Int.toString s ^ ")")
    o array_toList


(* Here we start the implementation of the evaluator.  By nature 
the implementation is not written very functional as we update the fields 
in the annotated syntax tree. *)

(* We use the following exception to indicate that the evaluator loop
should be restarted. *)
exception Restart

(* Place holder for the inputs *)
val inputs = ref ( Array.fromList ([] : Numbers.int list ))

(* Place holder for the stack top.  An empty stack is indicated by NONE *)
val stack_top_ref = ref NONE : program_label option ref
fun stack_top () = ! stack_top_ref

(* and a debugging function providing a string representation of the stack. *)
fun stack_toString stack = 
    case stack of
	NONE => "none"
      | SOME node => exec_toString node 
		     

(* First the lookup function as described in the paper *)
local open Numbers in
fun lookup n ((src, s) : source) =
    ( Debug.print ("lookup: (?, " ^ Int.toString n ^", "
		   ^ Int.toString s ^"), src=" 
		   ^ src_toString src ^ ": ") ;
      case src of
	  SInput j => let val b = bit_nth ( Array.sub (!inputs, j-1)) (n+s)
		      in
			  Debug.print ("input " ^ Int.toString j 
				       ^ ", bit " ^ Int.toString (n+s) 
				       ^ " is " ^ Bit.toString b ^"\n");
			  b
		      end
				    
	| SComp lj => 
	  (* push a child of the current stack top onto the execution
	  stack.  Then restart the main loop with the updated stack.
	  The main concern is to create the correct execution stack
	  entry for the child.  The details are described in the
	  paper. *)
	  let fun push_restart (SOME {parent=l, child_idx=j}) = 
		  let val pop = case stack_top () of
				    SOME pop => pop
				  | NONE => raise General.Fail "push-restart on root"
		      fun push l' e' =
			  ( n_stack_ref l' := SOME {pop=SOME pop, r=0, n=n+s, e=e'};
			    stack_top_ref := SOME l' )
		      val (r,e) = case n_stack l of
				      SOME entry => (#r entry, #e entry)
				    | NONE => raise 
					  General.Fail "push-restart on uninitialized node"
		  in 
		      Debug.print ("push_restart: n=" ^ Int.toString n ^", s=" ^ Int.toString s ^", r=" ^ Int.toString r ^", l=" ^ exec_toString l ^"\n");
		      case n_type l of
			  Comp (f, normal, safe) =>
			  if j=0 then
			      push lj 
				   (( Array.fromList o List.map (fn l' => (SComp l',0)))
					( normal @ safe ))
			  else 
			      if j <= List.length normal then
				  push lj (subarray (e, 0, SOME (List.length normal)))
			      else push lj (subarray (e, 0, NONE))			   
			| Rec (debug, g, h0, d0, h1, d1, nsafe) =>
			  if j=1 then
			      push lj (subarray (e, 1, NONE))
			  else 
			      push lj (Array.fromList 
					   ((shift 1 (Array.sub (e,0))) 
					    :: Array.foldri (fn (_, e, l) => e::l)
							    [( SRec (l, 1 + r), 0)]
							    (e, 1, SOME ((Array.length e) - nsafe -1)) ))
			| Top f => push lj (subarray (e, 0, NONE))			  
			   (* The top node just passes the computation down one
			    level *)
			| _ => raise General.Fail "leaf node is parent" ;
		      raise Restart
		  end
		| push_restart NONE = raise General.Fail "push-restart on root."
	  in case n_window lj of
		 NONE => ( Debug.print ("no value, ");
			   push_restart (n_parent lj))
	       | SOME win => 
		 (Debug.print ("found ("^ Bit.toString (#bit win) ^", "^ Int.toString (#n win) ^" ,"^ Int.toString (#r win) ^ "),");
		 if (#r win)=0 andalso n+s = (#n win) 
		 then (Debug.print "\n"; #bit win) 
		 else push_restart (n_parent lj))
	  end
	| SRec (l, r) =>
	  (* Unwind the stack when we go from recursive depth r to
	  recursive depth r+1.  It updates the execution stack entry
	  for the recursion and clear the computation windows below
	  (since their parent execution environment has changed. *)
	  let fun unwind_restart () =
		  case n_stack l of
		      NONE => raise General.Fail "Recursion on non recursive-label"
		    | SOME {pop=pop, r=r', n=n', e=e'} =>
		      ( Debug.print ("unwind_restart: n=" ^ Int.toString (n+s)^ ", s=" ^ Int.toString s^ ", r=" ^ Int.toString r ^ ", l=" ^ exec_toString l ^ "\n");
			Array.update (e', 0, shift (r-r') ( Array.sub(e', 0)));
			n_stack_ref l := SOME {pop=pop, n=n+s, r=r, e=e'};
			stack_top_ref := SOME l ;
			exec_tree_clear_windows l;
			raise Restart ) 
	  in
	     case n_window l of
		 NONE => ( Debug.print ("no value, ");
			   unwind_restart ())
	       | SOME win => 
		 (Debug.print ("found (" ^ Bit.toString (#bit win) ^ ", " ^ Int.toString (#n win) ^" ," ^ Int.toString (#r win) ^ "), ");
		 if (#r win)=r andalso n+s = (#n win) then (#bit win) 
		 else unwind_restart ())
	  end)
end

(* main loop to evaluate a single bit.  It used the the function lookup which 
raises the exception Restart when the execution stack has changed. *)
fun eval_bit s n =
    ( n_stack_ref s := SOME {pop=NONE, n=n, r=0, 
			     e=Array.tabulate (Array.length (! inputs),
					       fn i => (SInput (i+1), 0))};
      stack_top_ref := SOME s;
      while (stack_top ()) <> NONE do
	  let val SOME top = stack_top ()
	      val (pop, n, r, e) = 
		  case n_stack top of
		      SOME top => (#pop top, #n top, #r top, #e top)
		    | NONE => raise General.Fail "Uninitialized stack top"
	      fun lookup_env (n, j) = (lookup n o Array.sub) (e, j-1) 
	      val _ = Debug.print ("main loop (" ^ exec_toString top ^ "): n=" ^ Int.toString n^ ", r=" ^ Int.toString r ^ ", pop=" ^ stack_toString pop^ ", e=[" ^ env_toString e ^ "]\n")
	      val b = case n_type top of
			  Zero => Bit.none
			| Succ0 => if n=0 then Bit.zero
				   else lookup_env (n - 1, 1)
			| Succ1 => if n=0 then Bit.one
				   else lookup_env (n - 1, 1)
			| Pred => lookup_env (n + 1, 1)
			| Cond => if Bit.boolean (lookup_env (0, 1))  
				  then lookup_env (n, 3)
				  else lookup_env (n, 2)
			| Proj (m,m',j) => lookup_env (n, j)
			| Comp (f, gs_normal, gs_safe) => lookup n (SComp f, 0)
			| Rec (debug, g, h0, d0, h1, d1, _) => 
			   ( case Bit.bool_option (lookup_env (0, 1)) of
				 NONE => lookup n (SComp g, 0)
			       | SOME b => 
				 lookup n (SComp (if b then h1 else h0), 0) )
			| Top f => lookup n (SComp f,0)
	  in	      
	      Debug.print ("main loop ("^ exec_toString top ^"): storing ("^ Bit.toString b ^", "^ Int.toString n ^" ,"^ Int.toString r ^") @ "^ exec_toString top ^"\n");
	      n_window_ref top := SOME {bit=b, n=n, r=r};
	      stack_top_ref := pop ;
	      Debug.print ("main loop (" ^ exec_toString top 
			   ^ "): stack_top() <> NONE = "
			   ^ Bool.toString ( stack_top() <> NONE ) ^"\n")     
	  end handle Restart => ();
      Debug.print "main loop: finished\n\n";
      case n_window s of
	  SOME entry =>
	  if #n entry = n then #bit entry 
	  else raise General.Fail "eval_bit returned wrong bit"
	| NONE => raise General.Fail "eval_bit didn't evaluate bit")
 
(* The evaluator which uses eval_bit to evaluate each of the bits
individually.  This is done from least significant to most significant
where we stop when there is no bit.  

For full correctness we should evaluate from most significant to least
significant bit and only start outputting bits after encountering the
first 1-bit.  This an optimization by not evaluating through all the
non-existing bits. *)
local open Numbers in
fun eval s normal safe =
    let val exec_tree = exec_tree_build s
        (* Iteratively evaluate the bit until there are no more bits. *)
	fun iter_eval_bit acc bit =
	    case Bit.bool_option (eval_bit exec_tree bit) of
		NONE => acc
	      | SOME b => iter_eval_bit (if b then set_nth acc  bit else acc) (bit + 1)
    in 
	inputs := Array.fromList (normal @ safe);
	iter_eval_bit ((binary o fromInt) 0) 0 
    end
end

(* The type checking evaluator. *)
fun eval_bc b = raise Types.TypeFailure ;
fun eval_bcm b = eval ( Types.verify_linear_bc b )
val eval_bcmeps = eval_bcm (* This evaluator cannot handle bc-_epsilon *)

end