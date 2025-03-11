structure LogspaceEvaluator =
struct

(* This is the rather involved data structure used to record the information 
   used in the logspace-evaluator.  Compared to the paper we have chosen the
   solution of augmenting the syntax tree.  We have therefore removed the labels
   from the stack entry and the computation window; they are only used to 
   identify the node in the syntax tree.  We have added a reference to the
   previous stack entry to the stack record *)


(* The following defines the augmented syntax tree, the execution tree
that we use as the data structure under the computation.  Since we
need a double- linked data structure we cannot do with an ordinary
inductive data type, but has to build the whole structure using
explicit references.  *)

datatype S = Zero
  | Succ0
  | Succ1
  | Pred 
  | Cond 
  | Proj of (int * int * int)
  | Comp of ((ExecNode ref) * (ExecNode ref) list * (ExecNode ref) list)
  | Rec of (ExecNode ref * ExecNode ref * ExecNode ref)
and ExecNode = N of S
		    * {parent: ExecNode ref, child_idx:int} option ref
		    * {pop: ExecNode ref option, n:int, r:int,
		       e:(SourceDesc * int) Array.array} option ref
		    * {b:int option, n:int, r:int} option ref		     

and SourceDesc = SInput of int 
		(* An input to the program; 1-based *)
               | SComp of ExecNode ref
	       | SRec of ExecNode ref * int

type program_label = ExecNode ref 			 
type source = SourceDesc * int


(* Access the parts stored in a node *)
fun n_internal (f: ExecNode -> 'a) (label: program_label) = f (! label)
val n_type = n_internal (fn (N (s, parent, stack, window)) => s)
val n_parent_ref = n_internal (fn (N (s, parent, stack, window)) => parent)
val n_parent = ! o n_parent_ref
val n_stack_ref = n_internal (fn (N (s, parent,stack, window)) => stack)
val n_stack = ! o n_stack_ref
val n_window_ref = n_internal (fn (N (s, parent, stack, window)) => window)
val n_window = ! o n_window_ref

fun array_toList (arr : 'a Array.array) = Array.foldr (op ::) [] arr

fun exec_toS (tree: program_label) =
    case n_type tree of
	Zero => Syntax.Zero
      | Succ0 => Syntax.Succ0
      | Succ1 => Syntax.Succ1
      | Pred => Syntax.Pred
      | Cond => Syntax.Cond
      | Proj (m, m', j) => Syntax.Proj (m,m',j)
      | Comp (f, normal, safe) => Syntax.Comp (exec_toS f,
					       List.map exec_toS normal,
					       List.map exec_toS safe)
      | Rec (g, h0, h1) => Syntax.Rec(exec_toS g, exec_toS h0, exec_toS h1)
val exec_toString = Syntax.toString o exec_toS

fun bit_toString NONE = "fail" 
  | bit_toString (SOME b) = Int.toString b

fun src_toString (SInput n) = "inp " ^ Int.toString n
  | src_toString (SComp node) = "cmp " ^ exec_toString node
  | src_toString (SRec (node, r)) = "rec " ^ Int.toString r

val env_toString =
    Syntax.map_comma_string (fn (src, s) => "(" ^ src_toString src ^ "," 
					    ^ Int.toString s ^ ")")
    o array_toList


(* Build the execution tree from the syntax tree.  We create a new reference cell 
for each node in the syntax tree. 
Note that we for each node with subtrees first process the subtrees inserting an
empty parent pointer and then after cretaing the cell for the node inserts the node
as parent in the subtreess *)
fun build_exec_tree (s : Syntax.S) =
    let fun new_cell s = ref (N ( s, ref NONE, ref NONE, ref NONE))
    in case s of 
	   Syntax.Zero => new_cell ( Zero)
	 | Syntax.Succ0 => new_cell ( Succ0 )
	 | Syntax.Succ1 => new_cell ( Succ1 )
	 | Syntax.Pred => new_cell ( Pred )
	 | Syntax.Cond => new_cell ( Cond )
	 | (Syntax.Proj (m,n,j)) => new_cell ( Proj(m,n,j) )
	 | (Syntax.Comp (f, normal, safe)) =>
	   let val f' = build_exec_tree f
	       val normal' = List.map build_exec_tree normal
	       val safe' = List.map build_exec_tree safe
	       val comp' = new_cell ( Comp ( f', normal', safe') )
	       fun map_parent_upd subs =
		   List.map (fn (sub, n) => 
				n_parent_ref sub := SOME {parent=comp',
							  child_idx=n} )
			    (ListPair.zip (subs,
					   List.tabulate (List.length subs,
							  fn i=>i + 1)))
	   in 
	       n_parent_ref f' := SOME {parent=comp', child_idx=0};
	       map_parent_upd (normal' @ safe');
	       comp'
	   end
	 | (Syntax.Rec (g, h0, h1)) =>
	   let val g' = build_exec_tree g
	       val h0' = build_exec_tree h0
	       val h1' = build_exec_tree h1
	       val rec' = new_cell ( Rec ( g', h0', h1'))
	   in 
	       n_parent_ref g' := SOME {parent=rec', child_idx=1};
	       n_parent_ref h0' := SOME {parent=rec', child_idx=2};
	       n_parent_ref h1' := SOME {parent=rec', child_idx=3};
	       rec'
	   end
    end
	
(* Shift the source right *)
fun shift s' ((desc, s) : source) = ((desc, s + s') : source)

fun exp k n = 
    (* An iterative (tail-recursive) exponentation:
       It is easiliest understood by recalling that as

         k = 2^m b_m + ... + 2^0 b_0

       we have

         n^k = n^{2^m b_m + ... + 2^0 b_0}
             = n^{2^m b_m} * ... * n^{2^0 b_0} .

       Now, n^{2^i b_i} is either n^{2^i} (if b_i = 1) or 1.
       The implementation below lets m go through the values of 
       n^{2^i} while acc keeps the product. *) 
    let fun exp' 0 m acc = acc
	  | exp' k m acc = exp' (k div 2) 
				(m * m )
				( if k mod 2 = 0 then acc
				  else acc * m )
    in 
	exp' k n 1
    end

fun bit n j = let val shifted = n div (exp j 2)
	      in
		  if shifted = 0 then NONE
		  else SOME ( shifted mod 2 )
	      end


(* Here we start the implementation of the evaluator.  By nature 
the implementation is not written very functional as we update the fields 
in the annotated syntax tree. *)

(* We use the following exception when to indicate that the evaluator
loop should be restarted. *)
exception Restart

(* Place holder for the inputs *)
val inputs = ref ( Array.fromList ([] : int list ))

(* Place holder for the stack top.  An empty stack is indicated by NONE *)
val stack_top_ref = ref NONE : program_label option ref
fun stack_top () = ! stack_top_ref

(* First the lookup function as described in the paper *)
fun lookup n ((src, s) : source) =
    ( Debug.print ("lookup: (?, " ^ Int.toString n ^", "
		   ^ Int.toString s ^"), src=" ^ src_toString src ^ "\n") ;
      case src of
	  SInput j => bit ( Array.sub (!inputs, j-1)) (n+s)
	| SComp lj => 
	  let fun push_restart (SOME {parent=l, child_idx=j}) = 
		  let fun subarray slice = 
			  let val vec = Array.extract slice
			  in Array.tabulate (Vector.length vec,
					     fn i => Vector.sub (vec,i))
			  end
		      val pop = case stack_top () of
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
		      Debug.print ("push_restart: n=" ^ Int.toString n
				   ^ ", s=" ^ Int.toString s
				   ^ ", j=" ^ Int.toString j 
				   ^ ", l=" ^ exec_toString l ^ "\n");
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
			| Rec (g, h0, h1) =>
			  if j=1 then
			      push lj (subarray (e, 1, NONE))
			  else 
			      push lj (Array.fromList 
					   ((shift 1 (Array.sub (e,0))) 
					    :: Array.foldri (fn (_, e, l) => e::l)
							    [( SRec (l, 1 + r), 0)]
							    (e, 1, NONE) ))
			| _ => raise General.Fail "leaf node is parent" ;
		      raise Restart
		  end
		| push_restart NONE = raise General.Fail "push-restart on root."
	  in case n_window lj of
		 NONE => ( Debug.print ("lookup: no value for "^ exec_toString lj ^"\n");
			   push_restart (n_parent lj))
	       | SOME win => 
		 (Debug.print ("lookup: found (" ^ bit_toString (#b win) ^ ", " 
			       ^ Int.toString (#n win) ^" ," 
			       ^ Int.toString (#r win) 
			       ^ ") for "^ exec_toString lj ^ "\n");
		 if (#r win)=0 andalso n+s = (#n win) then (#b win) 
		 else push_restart (n_parent lj))
	  end
	| SRec (l, r) =>
	  case n_stack l of
	      NONE => raise General.Fail "Recursion on non recursive-label"
	    | SOME {pop=pop, r=r', n=n', e=env'} =>
	      ( Array.update (env', 0, shift (r-r') ( Array.sub(env', 0)));
		n_stack_ref l := SOME {pop=pop, n=n+s, r=r, e=env'};
		stack_top_ref := SOME l ;
		raise Restart ) )

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
	      fun stack_toString stack = 
		  case stack of
	              NONE => "none"
		    | SOME node => exec_toString node 
	      val _ = Debug.print ("main loop: n=" ^ Int.toString n
				   ^ ", r=" ^ Int.toString r 
				   ^ ", top=" ^ exec_toString top
				   ^ ", pop=" ^ stack_toString pop
				   ^ ", e=[" ^ env_toString e ^ "]\n")
	      fun lookup_env (n, j) = 
		  ( Debug.print ("lookup_env: j=" ^ Int.toString j
				 ^ ", n=" ^ Int.toString n 
				 ^ ", e=[" ^ env_toString e ^ "]\n");
		    (lookup n o Array.sub) (e, j-1) )
	      val b = case n_type top of
			  Zero => NONE
			| Succ0 => if n=0 then SOME 0
				   else lookup_env (n - 1, 1)
			| Succ1 => if n=0 then SOME 1
				   else lookup_env (n - 1, 1)
			| Pred => lookup_env (n + 1, 1)
			| Cond => if lookup_env (0, 1) = SOME 1
				  then lookup_env (n, 3)
				  else lookup_env (n, 2)
			| Proj (m,m',j) => lookup_env (n, j)
			| Comp (f, normal, safe) => lookup n (SComp f, 0)
			| Rec (g, h0, h1) =>
			  case lookup_env (0, 1) of
			      NONE => lookup n (SComp g, 0)
			    | SOME b => 
			      lookup n (SComp (if b = 0 then h0 else h1), 0);
		  
	  in	      
	      Debug.print ("main loop: storing (" 
			   ^ bit_toString b ^ ", " ^ Int.toString n ^" ," 
			   ^ Int.toString r ^ "), l=" ^ exec_toString top ^"\n");
	      n_window_ref top := SOME {b=b, n=n, r=r};
	      if r=0 then stack_top_ref := pop 
	      else case n_stack l of
		       NONE => raise General.Fail "Recursion on non recursive-label"
		     | SOME {pop=pop, r=r', n=n', e=env'} =>
		       ( Array.update (env', 0, shift -1 ( Array.sub(env', 0)));
			 n_stack_ref l := SOME {pop=pop, n=n+s, r=r, e=env'};
			 stack_top_ref := SOME l ;

;
	      Debug.print ("main loop, end: stack_top() <> NONE = "
			   ^ Bool.toString ( stack_top() <> NONE ) ^"\n")     
	  end handle Restart => ();
      Debug.print "main loop: finished\n\n";
      case n_window s of
	  SOME entry =>
	  if #n entry = n then #b entry 
	  else raise General.Fail "eval_bit returned wrong bit"
	| NONE => raise General.Fail "eval_bit didn't evaluate bit"
 )

fun eval s normal safe =
    let val exec_tree = build_exec_tree s
        (* Iteratively evaluate the bit until there are no more bits. *)
	fun iter_eval_bit acc bit =
	    case eval_bit exec_tree bit of
		NONE => acc
	      | SOME b => iter_eval_bit (acc + b * (exp bit 2)) (bit + 1)
    in 
	inputs := Array.fromList (normal @ safe);
	iter_eval_bit 0 0 
    end

end