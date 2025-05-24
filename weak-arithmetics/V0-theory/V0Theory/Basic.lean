-- This file defines a deep embedding of propositional natural deduction in Lean 4.
-- It includes the syntax of formulas, the concept of a context (Gamma),
-- and an inductive definition of the `Derivation` relation (Gamma ⊢ phi).

-- We'll use the `Prop` type for our `Derivation` relation, meaning proofs are types.

import Lean
import Lean.Data.Name

namespace NaturalDeduction

/-!
## 1. Syntax of Propositions (Formulas)
Defines the structure of our logical propositions.
-/

inductive Formula : Type where
  | atom (s : String)  -- Atomic propositions (e.g., P, Q, R)
  | top                -- Truth (⊤)
  | bot                -- Falsity (⊥)
  | imp (φ ψ : Formula)  -- Implication (φ → ψ)
  deriving Repr, DecidableEq, BEq

-- Custom notation for ⊤ and ⊥
notation "⊤" => Formula.top
notation "⊥" => Formula.bot

def Formula.neg (φ : Formula) : Formula :=
  Formula.imp φ Formula.bot

def Formula.conj (φ ψ : Formula) : Formula :=
  Formula.neg (Formula.imp φ (Formula.neg ψ))

def Formula.disj (φ ψ : Formula) : Formula :=
  Formula.imp (Formula.neg φ) ψ

instance : AndOp Formula where
  and := Formula.conj

instance : OrOp Formula where
  or := Formula.disj

-- Example formulas:
-- `atom "P"`
-- `atom "P" → atom "Q"`
-- `(atom "P" ∧ atom "Q") ∨ ¬atom "R"`

abbrev Context := List (Lean.Name × Formula)

/-!
## 3. Derivation Relation (Γ ⊢ φ)
This inductive type defines what it means for a formula `φ` to be derivable
from a `Context Γ` according to natural deduction rules.
Each constructor corresponds to a natural deduction rule.
-/

infixr:60 " → " => Formula.imp

inductive Derivation : Context → Formula → Prop where
  -- Assumption (Axiom)
  | ax {Γ : Context} {φ : Formula} {n : Lean.Name} (h : (n, φ) ∈ Γ) : Derivation Γ φ
  -- Primitive Connective Rules:
  | top_intro (Γ : Context) : Derivation Γ ⊤
  | bot_elim (Γ : Context) (φ : Formula) (h : Derivation Γ ⊥) : Derivation Γ φ
  | imp_intro {Γ : Context} {φ ψ : Formula} {n : Lean.Name}
      (h : Derivation ((n, φ) :: Γ) ψ) : Derivation Γ (φ → ψ)
  | imp_elim {Γ : Context} {φ ψ : Formula}
      (h₁ : Derivation Γ (φ → ψ)) (h₂ : Derivation Γ φ) : Derivation Γ ψ
  | dne {Γ : Context} {φ : Formula} (h₁ : Derivation Γ ((φ → ⊥) → ⊥)) : Derivation Γ φ

-- Custom notation for the derivation relation (turnstile)
notation:35 Γ " ⊢ " φ => Derivation Γ φ

open Derivation

def weaken_by_swap (a b : Lean.Name × Formula) (Γ : Context) (φ : Formula)
  (h : Derivation (a :: b :: Γ) φ)
  : Derivation (b :: a :: Γ) φ := by
  generalize h_eq : a :: b :: Γ = G'
  rw [h_eq] at h
  induction h with
  | ax hmem =>
    cases hmem with
    | head _ =>
      apply ax
      injection h_eq with head_eq
      rw [head_eq]
      apply List.mem_cons_of_mem
      apply List.mem_cons_self
    | tail _ in_tl =>
      apply ax
      cases in_tl with
      | head _ =>
        injection h_eq with _ tail_eq
        injection tail_eq with th_eq
        rw [th_eq]
        apply List.mem_cons_self
      | tail _ in_t =>
        injection h_eq with _ h_tail_eq
        injection h_tail_eq with _ tt_eq
        rw [tt_eq]
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        exact in_t
  | top_intro => exact top_intro _
  | bot_elim _ _ h h_ih =>
    apply bot_elim
    apply h_ih
    exact h_eq
  -- for some reason, h_ih is impossible to use here?
  | imp_intro h _ =>
    sorry
  | imp_elim h1 h2 h1_ih h2_ih =>
    apply imp_elim
    apply h1_ih
    exact h_eq
    apply h2_ih
    exact h_eq
  | dne h1 h1_ih =>
    apply dne
    apply h1_ih
    exact h_eq

def weaken_by_cons (Γ_new_elem : Lean.Name × Formula) {Γ : Context} {φ : Formula}
    (h : Derivation Γ φ) : Derivation (Γ_new_elem :: Γ) φ := by
  induction h with
  | ax h =>
    exact ax (List.mem_cons_of_mem Γ_new_elem h)
  | top_intro Γ =>
    exact top_intro (Γ_new_elem :: Γ)
  | bot_elim Γ φ h h_ih =>
    exact bot_elim (Γ_new_elem :: Γ) φ h_ih
  | imp_intro h ih =>
    apply Derivation.imp_intro
    apply weaken_by_swap
    exact ih
  | imp_elim h1 h2 h1_ih h2_ih =>
    apply Derivation.imp_elim
    apply h1_ih
    exact h2_ih
  | dne h1 h1_ih =>
    apply dne
    exact h1_ih

def weaken_by_concat (Γ1 : Context) (Γ2 : Context) (φ : Formula)
    (h : Derivation Γ1 φ) : Derivation (Γ1 ++ Γ2) φ := by
    induction Γ2 with
    | nil =>
      simp
      exact h
    | cons hd tl ih =>
      sorry

def neg_intro (Γ : Context) (φ : Formula) (n : Lean.Name)
    (h : Derivation ((n, φ) :: Γ) ⊥) : Derivation Γ (Formula.neg φ) := by
  exact imp_intro h

def neg_elim {Γ : Context} {φ : Formula}
    (h₁ : Derivation Γ (Formula.neg φ)) (h₂ : Derivation Γ φ) : Derivation Γ ⊥ := by
  exact imp_elim h₁ h₂

def conj_intro {Γ : Context} {φ ψ : Formula}
    (h₁ : Derivation Γ φ) (h₂ : Derivation Γ ψ) : Derivation Γ (Formula.conj φ ψ) := by
  unfold Formula.conj
  apply neg_intro Γ (φ → (Formula.neg ψ)) `H1
  generalize H1_eq : (`H1, _) = H1
  have h1 := weaken_by_cons H1 h₁
  have h2 := @ax [H1] H1.snd H1.fst (by rw [Prod.eta]; simp)
  have h3 := weaken_by_concat [H1] Γ H1.snd h2
  rw [<- H1_eq] at h3
  simp [H1_eq] at h3
  have h4 := @imp_elim (H1 :: Γ) φ (ψ.neg) h3 h1
  apply imp_elim h4
  apply weaken_by_cons H1
  exact h₂

theorem imp_intro_dummy {Γ : Context} (p : Formula) {q : Formula} (h : Derivation Γ q)
  : Derivation Γ (p → q) := by
  have h1 := weaken_by_cons (`a, p) h
  apply Derivation.imp_intro
  exact h1

theorem imp_intro_undo {Γ : Context} {p q : Formula} (n : Lean.Name) (h : Derivation Γ (p → q))
  : Derivation ((n, p) :: Γ) q := by
  apply imp_elim (weaken_by_cons (n, p) h)
  apply ax
  apply List.mem_cons_self

def conj_elim1 {Γ : Context} {φ ψ : Formula}
  (h : Derivation Γ (Formula.conj φ ψ)) : Derivation Γ φ := by
  unfold Formula.conj at h
  apply dne
  apply Derivation.imp_intro
  generalize H1_eq : (`H1, _) = H1
  have h1 := weaken_by_cons H1 h
  have h2 := @ax (H1 :: Γ) H1.snd H1.fst (by simp)
  rw [<- H1_eq] at h2; simp [H1_eq] at h2
  clear h
  -- trick: if we have ⊥, we also have ψ → ⊥
  -- so from φ → ⊥, we can make φ → (ψ → ⊥)
  have h2' := imp_intro_undo `_ h2
  have h2'' := imp_intro_dummy ψ h2'
  have h3 := Derivation.imp_intro h2''
  rw [<- Formula.neg] at h3
  have h4 := imp_elim h1 h3
  exact h4

def conj_elim2 {Γ : Context} {φ ψ : Formula}
  (h : Derivation Γ (Formula.conj φ ψ)) : Derivation Γ ψ := by
  apply dne
  unfold Formula.conj at h
  apply Derivation.imp_intro
  generalize H1_eq : (`H1, _) = H1
  have h1 := weaken_by_cons H1 h
  have h2 := @ax (H1 :: Γ) H1.snd H1.fst (by simp)
  rw [<- H1_eq] at h2; simp [H1_eq] at h2
  clear h
  have h3 := imp_intro_dummy φ h2
  rw [<- Formula.neg] at h3
  have h4 := imp_elim h1 h3
  exact h4

def disj_introL {Γ : Context} {φ ψ : Formula}
  (h : Derivation Γ φ) : Derivation Γ (Formula.disj φ ψ) := by
  sorry

def disj_introR {Γ : Context} {φ ψ : Formula}
  (h : Derivation Γ ψ) : Derivation Γ (Formula.disj φ ψ) := by
  sorry

def disj_elim {Γ : Context} {φ ψ χ : Formula}
  (h : Derivation Γ (Formula.disj φ ψ)) (h1 : Derivation Γ (φ → χ)) (h2 : Derivation Γ (ψ → χ))
  : Derivation Γ χ := by
  sorry

namespace MinimalLogic

open Lean Elab Tactic Term Meta Syntax

/-
  Step 1: Define custom syntax for minimal logic
-/

declare_syntax_cat logic_expr

syntax "⊤"                        : logic_expr
syntax "⊥"                        : logic_expr
syntax logic_expr " ∧ " logic_expr : logic_expr
syntax logic_expr " ∨ " logic_expr : logic_expr
syntax logic_expr " → " logic_expr : logic_expr
syntax ident                      : logic_expr
syntax "(" logic_expr ")" : logic_expr

syntax "[Logic| " logic_expr "]" : term

/-
  Step 2: Macro expansion to Lean's internal logic
-/

elab_rules : term
  | `([Logic| ⊤]) => return mkConst ``True
  | `([Logic| ⊥]) => return mkConst ``False
  | `([Logic| ($p)]) => do elabTerm (← `([Logic| $p])) none -- Recurse for parentheses
  | `([Logic| $p:logic_expr ∧ $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkAppM ``And #[lhs, rhs]
  | `([Logic| $p:logic_expr ∨ $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkAppM ``Or #[lhs, rhs]
  | `([Logic| $p:logic_expr → $q:logic_expr]) => do
      let lhs ← elabTerm (← `([Logic| $p])) none
      let rhs ← elabTerm (← `([Logic| $q])) none
      mkArrow lhs rhs
  | `([Logic| $i:ident]) =>
      elabTerm (mkIdent i.getId) none

declare_syntax_cat minitactic
syntax "assume " ident " : " term                       : minitactic
syntax "introa " ident                                  : minitactic
syntax "introduce " term                                : minitactic
syntax "apply " ident                                   : minitactic
syntax "exact " ident                                   : minitactic
syntax "split"                                          : minitactic
syntax "left"                                           : minitactic
syntax "right"                                          : minitactic
syntax "cases " ident                                   : minitactic
syntax "done"                                           : minitactic

syntax "begin_min " (minitactic)*  : tactic


elab_rules : tactic
  | `(tactic| begin_min $[$tacs:minitactic]*) => do
      let mut tacList : Array (TSyntax `tactic) := #[]
      for tacNode in tacs do
        let newTac : TSyntax `tactic ← match tacNode with
          | `(minitactic| assume $h:ident : $ty) => `(tactic| have $h : $ty := sorry)
          | `(minitactic| introa $h:ident)       => `(tactic| intro a)
          | `(minitactic| introduce $h:term)       => `(tactic| intro $h:term)
          | `(minitactic| apply $h:ident)       => `(tactic| apply $h)
          | `(minitactic| exact $h:ident)       => `(tactic| exact $h)
          | `(minitactic| split)                => `(tactic| constructor)
          | `(minitactic| left)                 => `(tactic| apply Or.inl)
          | `(minitactic| right)                => `(tactic| apply Or.inr)
          -- | `(minitactic| cases $h:ident)       => `(tactic| cases $h)
          | `(minitactic| done)                 => `(tactic| assumption)
          | _ => throwError m!"Unsupported mini tactic: {tacNode}"
        tacList := tacList.push newTac
        withTacticInfoContext tacNode do
          evalTactic newTac

example (P Q : Prop) : [Logic| P → (Q → P)] := by
  begin_min
    introduce p
    introduce q

end MinimalLogic
