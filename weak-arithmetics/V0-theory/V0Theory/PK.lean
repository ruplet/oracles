import Lean
import Qq
open Lean Elab Tactic Term Meta Syntax PrettyPrinter Qq

namespace GentzenStyle -- Changed namespace

inductive Formula where
| top : Formula
| bot : Formula
| var : Name -> Formula
| not : Formula -> Formula
| or : Formula -> Formula -> Formula
| and : Formula -> Formula -> Formula
deriving Repr, DecidableEq

example {p q} : Formula.or p q = Formula.or p q := by simp
example {p q} : p != q -> Formula.or p q != Formula.or q p := by
  simp; intros a b; rw [b]; simp; apply a; exact b

def Formula.imp (a b : Formula) := Formula.or (Formula.not a) b
def Formula.iff (a b : Formula) := Formula.and (Formula.imp a b) (Formula.imp b a)

structure Sequent where
  antecedent : List Formula
  succedent : List Formula
  deriving Repr

-- Pretty printing for Sequent (optional, but nice for goals and errors)
-- instance : ToFormat Sequent where
--   format s :=
--     let antecedents := Format.joinSep (s.antecedent.map reprPrec) (toFormat ", ")
--     let succedents := Format.joinSep (s.succedent.map reprPrec) (toFormat ", ")
--     f!"{antecedents} ⊢ {succedents}"

-- instance : Repr Sequent where
--   reprPrec s _ := PrettyPrinter.format (toFormat s)

open Formula

inductive Derivable : Sequent -> Prop where
-- logical axioms
| trivial : Derivable $ Sequent.mk [] [top]
| explosion : Derivable $ Sequent.mk [bot] []
| identity {A} : Derivable $ Sequent.mk [A] [A]
-- structural rules
| weak_l {A} {G D} :
  Derivable (Sequent.mk G D) -> Derivable (Sequent.mk (A :: G) D)
| weak_r {A} {G D} :
  Derivable (Sequent.mk G D) -> Derivable (Sequent.mk G (D ++ [A]))
| exch_l {A B} {G1 G2 D} :
  Derivable (Sequent.mk (G1 ++ [A, B] ++ G2) D)
  -> Derivable (Sequent.mk (G1 ++ [B, A] ++ G2) D)
| exch_r {A B} {G D1 D2} :
  Derivable (Sequent.mk G (D1 ++ [A, B] ++ D2))
  -> Derivable (Sequent.mk G (D1 ++ [B, A] ++ D2))
| contr_l {A} {G D} :
  Derivable (Sequent.mk (G ++ [A, A]) D)
  -> Derivable (Sequent.mk (G ++ [A]) D)
| contr_r {A} {G D} :
  Derivable (Sequent.mk G (D ++ [A, A]))
  -> Derivable (Sequent.mk G (D ++ [A]))
-- introduction rules
| neg_l {A} {G D} :
  Derivable (Sequent.mk G (D ++ [A]))
  -> Derivable (Sequent.mk (Formula.not A :: G) D)
| neg_r {A} {G D} :
  Derivable (Sequent.mk (A :: G) D)
  -> Derivable (Sequent.mk G (D ++ [Formula.not A]) )
| and_l {A B} {G D} : -- Note: This is one specific form of AndL
  Derivable (Sequent.mk (A :: B :: G) D)
  -> Derivable (Sequent.mk ((Formula.and A B) :: G) D)
| and_r {A B} {G D} :
  Derivable (Sequent.mk G (D ++ [A]))
  -> Derivable (Sequent.mk G (D ++ [B]))
  -> Derivable (Sequent.mk G (D ++ [Formula.and A B]))
| or_l {A B} {G D} :
  Derivable (Sequent.mk (A :: G) D)
  -> Derivable (Sequent.mk (B :: G) D)
  -> Derivable (Sequent.mk ((Formula.or A B) :: G) D)
| or_r {A B} {G D} : -- Note: This is one specific form of OrR
  Derivable (Sequent.mk G (D ++ [A, B]))
  -> Derivable (Sequent.mk G (D ++ [Formula.or A B]))
| cut {A} {G D} :
  Derivable (Sequent.mk G (D ++ [A]))
  -> Derivable (Sequent.mk (A :: G) D)
  -> Derivable (Sequent.mk G D)


declare_syntax_cat logic_expr

syntax ident                                              : logic_expr
syntax "⊤"                                                 : logic_expr
syntax "⊥"                                                 : logic_expr
syntax:90 "¬" logic_expr:max                             : logic_expr -- negation
syntax:80 logic_expr:80 "∧" logic_expr:81                 : logic_expr -- conjunction (higher than ∨)
syntax:75 logic_expr:75 "∨" logic_expr:76                 : logic_expr -- disjunction (higher than ->)
syntax:70 logic_expr:70 " -> " logic_expr:69               : logic_expr -- implication
syntax:65 logic_expr:65 " ↔ " logic_expr:64                : logic_expr -- bi-implication
syntax "(" logic_expr ")"                                  : logic_expr
syntax "[Logic| " logic_expr "]"                           : term

set_option pp.rawOnError true -- Keep for debugging if needed

elab_rules : term
  | `([Logic| $i:ident]) => do
    let identSyn := i -- this is i
    -- Try to resolve i as a term directly.
    -- If it has type Formula, use it.
    -- If it has type Name, wrap it with Formula.var.
    try
      let elaboratedIdent ← elabTerm identSyn none
      let identType ← inferType elaboratedIdent
      if ← isDefEq identType (mkConst ``Formula) then
        return elaboratedIdent -- It's already a Formula
      else if ← isDefEq identType (mkConst ``Name) then
        return mkApp (mkConst ``Formula.var) elaboratedIdent -- It's a Name, so wrap it
      else
        throwError m!"Identifier '{i.getId}' in [Logic| ...] must be of type Formula or Name, but it resolved to an expression of type {identType}."
    catch e =>
      throwError m!"Error elaborating identifier '{i.getId}' in [Logic| ...]: {e.toMessageData}"

  | `([Logic| ⊤]) => return mkConst ``Formula.top
  | `([Logic| ⊥]) => return mkConst ``Formula.bot

  | `([Logic| ¬ $p:logic_expr]) => do
      let p' ← elabTerm (← `([Logic| $p])) none
      return mkApp (mkConst ``Formula.not) p'

  | `([Logic| $p:logic_expr ∧ $q:logic_expr]) => do
      let p' ← elabTerm (← `([Logic| $p])) none
      let q' ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.and) p' q'

  | `([Logic| $p:logic_expr ∨ $q:logic_expr]) => do
      let p' ← elabTerm (← `([Logic| $p])) none
      let q' ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.or) p' q'

  | `([Logic| $p:logic_expr -> $q:logic_expr]) => do
      let p' ← elabTerm (← `([Logic| $p])) none
      let q' ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.imp) p' q'

  | `([Logic| $p:logic_expr ↔ $q:logic_expr]) => do
      let p' ← elabTerm (← `([Logic| $p])) none
      let q' ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.iff) p' q'

  | `([Logic| ($p)]) => do elabTerm (← `([Logic| $p])) none


theorem List.wrap_nil_eq {a} {L : List a} : L = [] ++ L ++ [] := by
  simp

theorem Derivable.wrap_nil_eq {Pre Post} : Derivable (Sequent.mk Pre Post) = Derivable (Sequent.mk Pre ([] ++ Post ++ [])) := by
  simp

-- theorem Derivable.display_last_two_eq {Pre Post} : Derivable (Sequent.mk Pre Post) = Derivable (Sequent.mk Pre ([] ++ Post ++ [])) := by

theorem Derivable.nil_append {Pre} {Post} : Derivable (Sequent.mk Pre Post) = Derivable (Sequent.mk Pre ([] ++ Post)) := by
  simp

theorem Derivable.split2 {a} {A B : a} : [A, B] = [A] ++ [B] := by
  simp

theorem Derivable.display_last_eq2 {Pre Post} {A B} : Derivable (Sequent.mk Pre (Post ++ [A, B])) = Derivable (Sequent.mk Pre (Post ++ [A] ++ [B])) := by
  rw [Derivable.split2]
  rw [List.append_assoc]

theorem Derivable.display_last_eq3 {Pre Post} {A B C} : Derivable (Sequent.mk Pre (Post ++ [A, B, C])) = Derivable (Sequent.mk Pre (Post ++ [A, B] ++ [C])) := by
  simp

example {P Q} : Derivable (Sequent.mk [[Logic| ¬(P ∧ Q)]] [[Logic|(¬(P)) ∨ ¬(Q)]]) := by
  apply Derivable.neg_l
  simp
  rw [Derivable.wrap_nil_eq]
  apply Derivable.exch_r
  simp
  rw [Derivable.nil_append]
  rw [Derivable.display_last_eq2]
  apply Derivable.or_r
  simp
  apply @Derivable.exch_r _ _ _ []
  apply @Derivable.exch_r _ _ _ [_]
  simp
  rw [Derivable.nil_append]
  rw [Derivable.display_last_eq3]
  apply Derivable.and_r
  . apply @Derivable.exch_r _ _ _ []
    apply @Derivable.exch_r _ _ _ [_]
    simp
    rw [Derivable.nil_append]
    rw [Derivable.display_last_eq3]
    apply Derivable.neg_r
    simp
    rw [Derivable.wrap_nil_eq]
    apply Derivable.exch_r
    simp
    rw [Derivable.nil_append]
    rw [Derivable.display_last_eq2]
    apply Derivable.weak_r
    simp
    apply Derivable.identity
  . simp
    apply @Derivable.exch_r _ _ _ [_]
    rw [List.append_nil]
    rw [Derivable.display_last_eq2]
    apply Derivable.neg_r
    simp
    rw [Derivable.wrap_nil_eq]
    apply Derivable.exch_r
    simp
    rw [Derivable.nil_append]
    rw [Derivable.display_last_eq2]
    apply Derivable.weak_r
    simp
    apply Derivable.identity



-- Syntax category for Gentzen proof steps
declare_syntax_cat gentzen_tactic

syntax "let " ident " := " logic_expr                                       : gentzen_tactic

syntax "simp" "at" ident : gentzen_tactic
syntax "have " ident " := " "trivial"                                      : gentzen_tactic
syntax "have " ident " := " "explosion"                                    : gentzen_tactic
syntax "have " ident " := " "identity " logic_expr                         : gentzen_tactic
syntax "have " ident " := " "weak_l " logic_expr " from " ident            : gentzen_tactic
syntax "have " ident " := " "weak_r " logic_expr " from " ident            : gentzen_tactic
syntax "have " ident " := " "exch_l" "from" ident                           : gentzen_tactic
syntax "have " ident " := " "exch_r" "from" ident                           : gentzen_tactic
syntax "have " ident " := " "contr_l" "from" ident                          : gentzen_tactic
syntax "have " ident " := " "contr_r" "from" ident                          : gentzen_tactic
syntax "have " ident " := " "neg_l" "from" ident                            : gentzen_tactic
syntax "have " ident " := " "neg_r" "from" ident                            : gentzen_tactic
syntax "have " ident " := " "and_l" "from" ident                            : gentzen_tactic
syntax "have " ident " := " "and_r " logic_expr ", " logic_expr " from " ident ", " ident : gentzen_tactic
syntax "have " ident " := " "or_l " logic_expr ", " logic_expr " from " ident ", " ident  : gentzen_tactic
syntax "have " ident " := " "or_r" logic_expr ", " logic_expr "from" ident                             : gentzen_tactic
syntax "have " ident " := " "cut " logic_expr " from " ident ", " ident    : gentzen_tactic

syntax "conclude " ident                                                  : gentzen_tactic
syntax "begin_gentzen " (gentzen_tactic)* "end_gentzen"                   : tactic

elab_rules : tactic
  | `(tactic| begin_gentzen $[$tacs:gentzen_tactic]* end_gentzen) => do
    for tacNode in tacs do
      let tac ← match tacNode with
        | `(gentzen_tactic| let $name:ident := $e:logic_expr) => do
            let e_stx ← `([Logic| $e])
            let phi_expr ← Lean.Elab.Term.elabTerm e_stx none
            let phi_term ← delab phi_expr
            `(tactic| let $name : Formula := $phi_term)

        | `(gentzen_tactic| have $name:ident := trivial) =>
            `(tactic| have $name := Derivable.trivial)

        | `(gentzen_tactic| have $name:ident := explosion) =>
            `(tactic| have $name := Derivable.explosion)

        | `(gentzen_tactic| have $name:ident := identity $f:logic_expr) => do
            let f_stx ← `([Logic| $f])
            let f_expr ← Lean.Elab.Term.elabTerm f_stx none
            let f_term ← delab f_expr
            `(tactic| have $name := @Derivable.identity ($f_term)) -- Added parentheses

        | `(gentzen_tactic| have $name:ident := weak_l $f:logic_expr from $h:ident) => do
            let f_stx ← `([Logic| $f])
            let f_expr ← Lean.Elab.Term.elabTerm f_stx none
            let f_term ← delab f_expr
            `(tactic| have $name := @Derivable.weak_l ($f_term) _ _ $h) -- Added @ and parentheses

        | `(gentzen_tactic| have $name:ident := weak_r $f:logic_expr from $h:ident) => do
            let f_stx ← `([Logic| $f])
            let f_expr ← Lean.Elab.Term.elabTerm f_stx none
            let f_term ← delab f_expr
            `(tactic| have $name := @Derivable.weak_r ($f_term) _ _ $h) -- Added @ and parentheses

        | `(gentzen_tactic| have $name:ident := exch_l from $h:ident) =>
            `(tactic| have $name := Derivable.exch_l $h) -- A, B inferred

        | `(gentzen_tactic| have $name:ident := exch_r from $h:ident) =>
            `(tactic| have $name := Derivable.exch_r $h) -- A, B inferred

        | `(gentzen_tactic| have $name:ident := contr_l from $h:ident) =>
            `(tactic| have $name := Derivable.contr_l $h) -- A inferred

        | `(gentzen_tactic| have $name:ident := contr_r from $h:ident) =>
            `(tactic| have $name := Derivable.contr_r $h) -- A inferred

        | `(gentzen_tactic| have $name:ident := neg_l from $h:ident) =>
            `(tactic| have $name := Derivable.neg_l $h) -- A inferred from premise

        | `(gentzen_tactic| have $name:ident := neg_r from $h:ident) =>
            `(tactic| have $name := Derivable.neg_r $h) -- A inferred from premise

        | `(gentzen_tactic| have $name:ident := and_l from $h:ident) =>
            `(tactic| have $name := Derivable.and_l $h) -- A, B inferred from premise

        | `(gentzen_tactic| have $name:ident := and_r $a:logic_expr, $b:logic_expr from $h1:ident, $h2:ident) => do
            let a_stx ← `([Logic| $a]); let a_expr ← Lean.Elab.Term.elabTerm a_stx none; let a_term ← delab a_expr
            let b_stx ← `([Logic| $b]); let b_expr ← Lean.Elab.Term.elabTerm b_stx none; let b_term ← delab b_expr
            `(tactic| have $name := @Derivable.and_r ($a_term) ($b_term) _ _ $h1 $h2) -- Added @ for A, B

        | `(gentzen_tactic| have $name:ident := or_l $a:logic_expr, $b:logic_expr from $h1:ident, $h2:ident) => do
            let a_stx ← `([Logic| $a]); let a_expr ← Lean.Elab.Term.elabTerm a_stx none; let a_term ← delab a_expr
            let b_stx ← `([Logic| $b]); let b_expr ← Lean.Elab.Term.elabTerm b_stx none; let b_term ← delab b_expr
            `(tactic| have $name := @Derivable.or_l ($a_term) ($b_term) _ _ $h1 $h2) -- Added @ for A, B

        | `(gentzen_tactic| simp at $h:ident) =>
            `(tactic| simp (config := {failIfUnchanged := false, zetaDelta := true}) only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at $h:ident)

        | `(gentzen_tactic| have $name:ident := or_r $a_formula:logic_expr, $b_formula:logic_expr from $h:ident) => do
            let a_stx ← `([Logic| $a_formula]); let a_expr ← Lean.Elab.Term.elabTerm a_stx none; let a_term ← delab a_expr
            let b_stx ← `([Logic| $b_formula]); let b_expr ← Lean.Elab.Term.elabTerm b_stx none; let b_term ← delab b_expr
            `(tactic| have $name := @Derivable.or_r ($a_term) ($b_term) _ [] $h)

        | `(gentzen_tactic| have $name:ident := cut $f:logic_expr from $h1:ident, $h2:ident) => do
            let f_stx ← `([Logic| $f]); let f_expr ← Lean.Elab.Term.elabTerm f_stx none; let f_term ← delab f_expr
            `(tactic| have $name := @Derivable.cut ($f_term) _ _ $h1 $h2) -- Added @ and parentheses

        | `(gentzen_tactic| conclude $id:ident) =>
            `(tactic| exact $id)

        | _ => throwError m!"Unsupported Gentzen tactic: {tacNode}"
      withTacticInfoContext tacNode do
        evalTactic tac

-- Example usage
variable (p q r : Name)

-- Define Formula abbreviations (optional, can use [Logic| ...] directly in tactics)
def P : Formula := [Logic| p]
def Q : Formula := [Logic| q]
def R : Formula := [Logic| r]

elab (name := makeOrR) "makeOrR" name:ident "from" h:ident : tactic => do
  let hExpr <- Elab.Tactic.elabTerm h none
  let hType <- inferType hExpr
  match hType.getAppFnArgs with
  | (``Derivable, #[sequentExpr]) =>
    match sequentExpr.getAppFnArgs with
    | (``Sequent.mk, #[antecedentListExpr, succedentListExpr]) =>
      let (dExprList, aExpr, bExpr) ← Meta.matchFreshListLit? succedentListExpr matchSuffixLength := 2

theorem x {P Q} {D} : (t : Derivable (Sequent.mk [P] (D ++ [P, Q]))) -> Derivable (Sequent.mk [P] [Formula.or P Q]) := by
  intro h
  apply @Derivable.or_r _ _ _ []
  simp
  exact h

-- Example: P ⊢ P ∨ Q
theorem p_or_q_from_p {P Q} : Derivable (Sequent.mk [P] [Formula.or P Q]) := by
  begin_gentzen
    have h_id := identity P
    have h_weak_r := weak_r Q from h_id
    simp at h_weak_r
    have h_or_r := or_r P, Q from h_weak_r
    conclude h_or_r
  end_gentzen

-- -- Example: ⊢ P → P (which is ⊢ ¬P ∨ P)
-- theorem p_imp_p : Derivable (Sequent.mk [] [P.imp P]) := by
--   begin_gentzen
--     -- Target: ⊢ p → p  (i.e., ⊢ ¬p ∨ p)

--     -- Step 1: p ⊢ p (Identity)
--     have h_id := identity p
--     -- h_id : Derivable (Sequent.mk [var p] [var p])

--     -- Step 2: ⊢ ¬p, p (Not Right)
--     -- Derivable.neg_r takes A,G ⊢ D  =>  G ⊢ D, ¬A
--     -- Here, A is `var p`. It's inferred from h_id.
--     have h_neg_r := neg_r from h_id
--     -- h_neg_r : Derivable (Sequent.mk [] [Formula.not (var p), var p])

--     -- Step 3: ⊢ ¬p ∨ p (Or Right)
--     -- Derivable.or_r infers A = ¬p, B = p from h_neg_r
--     have h_or_r := or_r from h_neg_r
--     -- h_or_r : Derivable (Sequent.mk [] [Formula.or (Formula.not (var p)) (var p)])
--     -- which is Derivable (Sequent.mk [] [Formula.imp (var p) (var p)])

--     conclude h_or_r
--   end_gentzen

-- -- Example demonstrating `let` and more connectives: P ∧ Q ⊢ P
-- def PandQ : Formula := [Logic| p ∧ q]

-- theorem and_elim_left : Derivable (Sequent.mk [PandQ] [P]) := by
--   begin_gentzen
--     -- Target: p ∧ q ⊢ p

--     -- Define P and Q locally if not using global ones
--     let P_form := p
--     let Q_form := q

--     -- Step 1: p, q ⊢ p (Identity on p, then weaken right with q, then exchange)
--     -- More direct: p,q,G ⊢ D implies (p∧q),G ⊢ D by and_l
--     -- Need premise for and_l: p, q ⊢ p
--     -- Start with p ⊢ p
--     have id_p := identity P_form
--     -- id_p : Derivable (Sequent.mk [P_form] [P_form])

--     -- p, q ⊢ p (Weaken Left with Q_form)
--     have weak_pq_p := weak_l Q_form from id_p
--     -- weak_pq_p : Derivable (Sequent.mk [Q_form, P_form] [P_form])
--     -- Need P, Q in order for and_l. Use exch_l.
--     -- A=Q_form, B=P_form in rule exch_l {A B} {G1 G2 D} from premise G1ABG2 ⊢ D gives G1BAG2 ⊢ D
--     -- Here G1=[], G2=[]
--     have exch_qp_pq := exch_l from weak_pq_p -- A=Q_form, B=P_form. Switches them.
--     -- exch_qp_pq : Derivable (Sequent.mk [P_form, Q_form] [P_form])

--     -- Step 2: p ∧ q ⊢ p (And Left)
--     -- Derivable.and_l {A B} from (A,B,G ⊢ D) gives (A∧B,G ⊢ D)
--     -- A and B are inferred from premise. A=P_form, B=Q_form
--     have and_l_pq := and_l from exch_qp_pq
--     -- and_l_pq : Derivable (Sequent.mk [Formula.and P_form Q_form] [P_form])

--     conclude and_l_pq
--   end_gentzen

end GentzenStyle
