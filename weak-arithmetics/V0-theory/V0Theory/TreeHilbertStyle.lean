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
inductive Derivable : (List Formula) -> Formula -> Prop where
| assumption {Γ} {φ} : (φ ∈ Γ) -> Derivable Γ φ
| axK {Γ} {phi psi} : Derivable Γ $ A1 phi psi
| axS {Γ} {phi psi ksi} : Derivable Γ $ A2 phi psi ksi
| mult_mp {Γ1 Γ2} {phi psi} : Derivable Γ2 (phi ==> psi) -> Derivable Γ1 phi -> Derivable (Γ1 ++ Γ2) psi

declare_syntax_cat logic_expr

syntax ident : logic_expr
syntax logic_expr " -> " logic_expr : logic_expr
syntax "(" logic_expr ")" : logic_expr
syntax "[Logic| " logic_expr "]" : term

elab_rules : term
  | `([Logic| $e:logic_expr]) => elabTerm e none
  | `(logic_expr| $i:ident) => do
      let nameExpr ← Term.elabTerm i none
      return mkApp (mkConst ``Formula.var) nameExpr

  | `(logic_expr| $p:logic_expr -> $q:logic_expr) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      return mkApp2 (mkConst ``Formula.imp) lhs rhs

  | `(logic_expr| ($p)) => do
      elabTerm (← `([Logic| $p])) none

partial def extractGammaFromGoal : TacticM Expr := do
  let goal ← getMainTarget
  let goal <- whnf goal
  match goal with
  | Expr.app (Expr.app (Expr.const name _) gamma) _ =>
    if name == `HilbertStyle.Derivable then
      pure gamma
    else
      throwError "Goal head constant is not HilbertStyle.Derivable, got: {name}"
  | _ =>
    throwError "Goal is not of the form `HilbertStyle.Derivable Γ φ`, got: {goal}"

elab "hilbertDebug" : tactic => do
  let goal ← getMainTarget
  let ppGoal := goal.dbgToString
  logInfo m!"Goal expression: {ppGoal}"
  -- let goalType ← goal.getType
  let gamma ← extractGammaFromGoal

  logInfo m!"Gamma: {gamma}"

elab "by_mem" : tactic => do evalTactic (← `(tactic| simp [List.Mem]))

-- Syntax category for Hilbert proof steps
declare_syntax_cat hilbert_tactic
-- syntax "let " ident ":=" logic_expr : hilbert_tactic
syntax "have" ident ":" logic_expr "by" "assumption" : hilbert_tactic
syntax "have" ident ":=" "axK" logic_expr "," logic_expr : hilbert_tactic
syntax "have" ident ":=" "axS" logic_expr "," logic_expr "," logic_expr : hilbert_tactic
syntax "have" ident ":=" "mp" ident ident : hilbert_tactic
syntax "debug" : hilbert_tactic
syntax "exact " ident : hilbert_tactic

syntax "begin_hilbert " (hilbert_tactic)* : tactic

elab_rules : tactic
  | `(tactic| begin_hilbert $[$tacs:hilbert_tactic]*) => do
    for tacNode in tacs do
      let tac ← match tacNode with
        -- | `(hilbert_tactic| let $name:ident := $e:logic_expr) => do
        --     let e' <- `([Logic| $e])
        --     let phi' <- Lean.Elab.Term.elabTerm e' none
        --     let phi <- delab phi'
        --     `(tactic| let $name := $phi)
        | `(hilbert_tactic| debug) => do
            `(tactic| hilbertDebug)

        | `(hilbert_tactic| have $name:ident : $phi:logic_expr by assumption) => do
            -- let e1' <- `([Logic| $e1])
            -- withoutErrToSorry do
            let phi' ← Lean.Elab.Term.elabTerm phi none
            let phi <- delab phi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            let goal ← `(Derivable $gamma $phi)
            -- let goalTy := mkApp2 (mkConst ``Derivable) gamma' phi'
            -- let byMem ← `(by by_mem)
            -- let rhs ← mkAppM ``Derivable.assumption #[gamma', phi', ← Lean.Elab.Term.elabTerm byMem (some goalTy)]
            -- let goal <- getMainGoal
            -- let fVarId <- goal.assert name goalTy rhs

            `(tactic| have $name : $goal := @Derivable.assumption _ $phi (by by_mem))

        | `(hilbert_tactic| have $name:ident := axK $e1, $e2) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let phi <- delab phi'
            let psi <- delab psi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            let goal ← `(Derivable $gamma (A1 $phi $psi))
            `(tactic| have $name : $goal := Derivable.axK)

        | `(hilbert_tactic| have $name:ident := axS $e1, $e2, $e3) => do
            let e1' <- `([Logic| $e1])
            let e2' <- `([Logic| $e2])
            let e3' <- `([Logic| $e3])
            let phi' ← Lean.Elab.Term.elabTerm e1' none
            let psi' ← Lean.Elab.Term.elabTerm e2' none
            let ksi' ← Lean.Elab.Term.elabTerm e3' none
            let phi <- delab phi'
            let psi <- delab psi'
            let ksi <- delab ksi'
            let gamma' <- extractGammaFromGoal
            let gamma <- delab gamma'
            `(tactic| have $name : Derivable $gamma (A2 $phi $psi $ksi) := Derivable.axS)

        | `(hilbert_tactic| have $name:ident := mp $h1 $h2) =>
            `(tactic| have $name := Derivable.mult_mp $h1 $h2)

        | `(hilbert_tactic| exact $id:ident) =>
            `(tactic| exact $id)

        | _ => throwError m!"Unsupported tactic: {tacNode}"
      withTacticInfoContext tacNode do
        withMacroExpansion tacNode tac (evalTactic tac)
        -- evalTactic tac


def a : Name := `a
variable (φ ψ ϑ p q: Name)

-- Urzyczyn, Sorensen: example 5.1.3
example {φ : Formula} : Derivable [] (φ ==> φ) := by
  have a : Derivable [] $ A2 φ (φ ==> φ) φ := Derivable.axS
  have b : Derivable [] $ A1 φ (φ ==> φ) := Derivable.axK
  have c := Derivable.mult_mp a b
  have d : Derivable [] $ A1 φ φ := Derivable.axK
  exact Derivable.mult_mp c d

example : Derivable [] [Logic| φ -> φ] := by
  begin_hilbert
    have a := axS φ, φ -> φ, φ
    have b := axK φ, φ -> φ
    have c := mp a b
    have d := axK φ, φ
    have e := mp c d
    exact e

-- Urzyczyn, Sorensen: example 5.1.6
example {φ ψ ϑ: Formula} : Derivable [φ, φ ==> ψ, ψ ==> ϑ] (ϑ) := by
  have a : Derivable [φ ==> ψ] $ φ ==> ψ := Derivable.assumption (by simp [List.Mem])
  have b : Derivable [φ] $ φ := Derivable.assumption (by simp [List.Mem])
  have c : Derivable [φ, φ ==> ψ] $ ψ := Derivable.mult_mp a b
  have d : Derivable [ψ ==> ϑ] $ ψ ==> ϑ := Derivable.assumption (by simp [List.Mem])
  have e : Derivable [φ, φ ==> ψ, ψ ==> ϑ] $ ϑ := Derivable.mult_mp d c
  exact e

syntax "[Logic|" sepBy(logic_expr, ",") "⊢" logic_expr "]": term

elab_rules : term
  | `([Logic| $assumptions,* ⊢ $goal]) => do
    let assumpExprs ← assumptions.getElems.mapM (fun stx => elabTerm stx none)
    let goalExpr ← elabTerm goal none
    let listExpr <- Lean.Meta.mkListLit (mkConst ``Formula) assumpExprs.toList
    pure $ mkApp2 (mkConst ``Derivable) listExpr goalExpr

-- Urzyczyn, Sorensen: proposition 5.1.7
-- syntax for mixing formulas with sets of formulas not yet supported
-- this proof is conducted in the meta theory!

-- strengthen to any Gamma not just []
-- + conduct proof in system with multiplicative mp, not standard
theorem urzyczyn5_1_3' {φ : Formula} {Γ} :  Derivable Γ (φ ==> φ) := by
  have a : Derivable Γ $ A2 φ (φ ==> φ) φ := Derivable.axS
  have b : Derivable [] $ A1 φ (φ ==> φ) := Derivable.axK
  have c := Derivable.mult_mp a b
  have d : Derivable [] $ A1 φ φ := Derivable.axK
  exact Derivable.mult_mp c d

theorem weakening {Γ} {φ ψ} : Derivable Γ ψ -> Derivable (φ :: Γ) ψ := by
  generalize Sub1 : φ :: Γ = Sub1_
  generalize Sub2 : ψ = Sub2_
  intro h
  induction h
  case _ h1 h2 =>
    apply Derivable.assumption
    rw [<- Sub1]
    rw [List.mem_cons]
    right
    apply h2
  case _ phi psi =>
    apply Derivable.axK
  case _ phi psi ksi =>
    apply Derivable.axS
  case _ a b c d imp base imp_ih base_ih =>
    -- the induction hypothesis for some reason is unusable...
    rw [<- Sub1]
    rw [<- Sub2]
    rw [<- Sub1] at base_ih
    rw [<- Sub1] at imp_ih
    simp at base_ih
    rw [Sub2] at base_ih
    simp at imp_ih
    sorry

theorem deduction {Γ} : Derivable (var φ :: Γ) [Logic|ψ] <-> Derivable Γ [Logic|φ -> ψ] := by
  apply Iff.intro
  {
    -- trick to bypass "index in target's type is not a variable" at `induction h`
    generalize Sub1 : var φ :: Γ = Sub1_
    generalize Sub2 : var ψ = Sub2_
    intro h
    induction h
    case mp.assumption h1 h2 =>
      cases h2 with
      | head =>
        injection Sub1 with head_eq
        rw [head_eq]
        apply urzyczyn5_1_3'
      | tail _ mem =>
        injection Sub1 with _ tail_eq
        rw [<- tail_eq] at mem
        have aux : Derivable Γ h1 := by
          apply Derivable.assumption
          assumption
        have aux2 : Derivable [] (h1 ==> var φ ==> h1) := by
          apply Derivable.axK

        rw [<- List.append_nil Γ]
        apply Derivable.mult_mp aux2 aux
    case mp.axK phi psi =>
      have aux : Derivable Γ (A1 phi psi) := by
        apply Derivable.axK
      have aux2 : Derivable [] ((A1 phi psi) ==> var φ ==> (A1 phi psi)) := by
        apply Derivable.axK
      rw [<- List.append_nil Γ]
      apply Derivable.mult_mp aux2 aux
    case mp.axS phi psi theta =>
      have aux : Derivable Γ (A2 phi psi theta) := by
        apply Derivable.axS
      have aux2 : Derivable [] ((A2 phi psi theta) ==> var φ ==> (A2 phi psi theta)) := by
        apply Derivable.axK
      rw [<- List.append_nil Γ]
      apply Derivable.mult_mp aux2 aux
    case mp.mult_mp =>
      sorry
  }
  {
    -- this is slightly different to the proof in the book
    -- we don't use weakening in this version due to multiplicative mp
    intro h
    have aux_base : Derivable ([var φ]) (var φ) := by
      apply Derivable.assumption
      simp
    apply Derivable.mult_mp h aux_base
  }

end HilbertStyle
