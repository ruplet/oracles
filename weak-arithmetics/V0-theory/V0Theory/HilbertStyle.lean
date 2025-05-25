import Lean
import Qq
open Lean Elab Tactic Term Meta Syntax PrettyPrinter Qq

namespace HilbertStyle

inductive Formula where
| var : Name -> Formula
| imp : Formula -> Formula -> Formula
deriving Repr, DecidableEq

notation:60 a " ==> " b => Formula.imp a b

def A1 (phi psi : Formula)
  := phi ==> psi ==> phi
def A2 (phi psi ksi : Formula)
  := (phi ==> psi ==> ksi) ==> (phi ==> psi) ==> phi ==> ksi

open Formula

-- perhaps we should be able to somehow take as axiom a formula,
-- for which the proof of being of the form A1 / A2 is non-constructive
-- i.e. have predicate isAxiom. but this is slightly harder in Lean
inductive Derivable : Formula -> Prop where
  | ax1 {phi psi} : Derivable $ A1 phi psi
  | ax2 {phi psi ksi} : Derivable $ A2 phi psi ksi
  | mp {phi psi} : Derivable (phi ==> psi) -> Derivable phi -> Derivable psi

declare_syntax_cat logic_expr

syntax ident : logic_expr
syntax logic_expr " -> " logic_expr : logic_expr
syntax "(" logic_expr ")" : logic_expr
syntax "[Logic| " logic_expr "]" : term

set_option pp.rawOnError true
elab_rules : term
  | `([Logic| $i:ident]) => do
      -- let n := i.getId
      -- let nameSyntax := Syntax.mkStrLit n.toString
      let nameExpr ← elabTerm i (some (mkConst ``Name))
      let res := mkApp (mkConst ``Formula.var) nameExpr
      return res
      -- let p <- elabTermEnsuringType (mkIdent i.getId) none
      -- return mkApp (mkConst ``Formula.var) p

  | `([Logic| $p:logic_expr -> $q:logic_expr]) => do
      -- recursively elaborate the left and right logic_expr parts
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.imp) lhs rhs

  | `([Logic| ($p)]) => do
      -- elaborate inner expression directly
      elabTerm (← `([Logic| $p])) none

  -- | stx => do
  --     logInfo m!"Unsupported syntax in [Logic| ...]: {stx}"
  --     throwUnsupportedSyntax

-- Syntax category for Hilbert proof steps
declare_syntax_cat hilbert_tactic
syntax "let " ident ":=" logic_expr                                  : hilbert_tactic
syntax "have" ident ":=" "ax1" logic_expr "," logic_expr                         : hilbert_tactic
syntax "have" ident ":=" "ax2" logic_expr "," logic_expr "," logic_expr                    : hilbert_tactic
syntax "have" ident ":=" "mp" ident ident                        : hilbert_tactic
syntax "conclude " ident                                          : hilbert_tactic

syntax "begin_hilbert " (hilbert_tactic)* : tactic

elab_rules : tactic
  | `(tactic| begin_hilbert $[$tacs:hilbert_tactic]*) => do
    for tacNode in tacs do
      let tac ← match tacNode with
        | `(hilbert_tactic| let $name:ident := $e:logic_expr) => do
            let e' <- `([Logic| $e])
            let phi' <- Lean.Elab.Term.elabTerm e' none
            let phi <- delab phi'
            `(tactic| let $name := $phi)
        | `(hilbert_tactic| have $name:ident := ax1 $e1, $e2) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let phi <- delab phi'
            let psi <- delab psi'
            let goal ← `(Derivable (A1 $phi $psi))
            `(tactic| have $name : $goal := Derivable.ax1)

        | `(hilbert_tactic| have $name:ident := ax2 $e1, $e2, $e3) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let e3' <- `([Logic| $e3])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let ksi' ← Lean.Elab.Term.elabTerm e3' none
            let phi <- delab phi'
            let psi <- delab psi'
            let ksi <- delab ksi'
            `(tactic| have $name : Derivable (A2 $phi $psi $ksi) := Derivable.ax2)

        | `(hilbert_tactic| have $name:ident := mp $h1 $h2) =>
            `(tactic| have $name := Derivable.mp $h1 $h2)

        | `(hilbert_tactic| conclude $id:ident) =>
            `(tactic| exact $id)

        | _ => throwError m!"Unsupported tactic: {tacNode}"
      withTacticInfoContext tacNode do
        evalTactic tac


def a : Name := `a
variable (φ p q: Name)

def phi := [Logic| φ]
def pphi := [Logic| p -> q]

-- types of combinators A1 A2
def K_type (x y : Name) := [Logic| x -> y -> x]
def S_type (x y z : Name) := [Logic| (x -> y -> z) -> (x -> y) -> x -> z]


-- Urzyczyn, Sorensen: example 5.1.3
example {φ : Formula} : Derivable (φ ==> φ) := by
  have a : Derivable $ A2 φ (φ ==> φ) φ := Derivable.ax2
  have b : Derivable $ A1 φ (φ ==> φ) := Derivable.ax1
  have c := Derivable.mp a b
  have d : Derivable $ A1 φ φ := Derivable.ax1
  exact Derivable.mp c d

theorem urzyczyn : Derivable [Logic| φ -> φ] := by
  begin_hilbert
    have a := ax2 φ , φ -> φ, φ
    have b := ax1 φ, φ -> φ
    have c := mp a b
    have d := ax1 φ, φ
    have e := mp c d
    conclude e

#check urzyczyn

end HilbertStyle
