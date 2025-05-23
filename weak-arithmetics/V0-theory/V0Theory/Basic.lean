-- This file defines a deep embedding of propositional natural deduction in Lean 4.
-- It includes the syntax of formulas, the concept of a context (Gamma),
-- and an inductive definition of the `Derivation` relation (Gamma ⊢ phi).

-- We'll use the `Prop` type for our `Derivation` relation, meaning proofs are types.

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
  | ax (Γ : Context) (φ : Formula) (n : Lean.Name) (h : (n, φ) ∈ Γ) : Derivation Γ φ

  -- Primitive Connective Rules:
  | top_intro (Γ : Context) : Derivation Γ ⊤
  | bot_elim (Γ : Context) (φ : Formula) (h : Derivation Γ ⊥) : Derivation Γ φ

  | imp_intro {Γ : Context} {φ ψ : Formula} {n : Lean.Name}
      (h : Derivation ((n, φ) :: Γ) ψ) : Derivation Γ (φ → ψ)

  | imp_elim {Γ : Context} {φ ψ : Formula}
      (h₁ : Derivation Γ (φ → ψ)) (h₂ : Derivation Γ φ) : Derivation Γ ψ

-- Custom notation for the derivation relation (turnstile)
notation:35 Γ " ⊢ " φ => Derivation Γ φ

open Derivation

def weaken_by_swap (a b : Lean.Name × Formula) (Γ : Context) (φ : Formula)
  (h : Derivation (a :: b :: Γ) φ)
  : Derivation (b :: a :: Γ) φ := by
  generalize h_eq : a :: b :: Γ = G'
  rw [h_eq] at h
  induction h with
  | ax _ _ n hmem =>
    cases hmem with
    | head _ =>
      apply ax _ _ n
      injection h_eq with head_eq
      rw [head_eq]
      apply List.mem_cons_of_mem
      apply List.mem_cons_self
    | tail _ in_tl =>
      apply ax _ _ n
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

def weaken_by_cons (Γ_new_elem : Lean.Name × Formula) (Γ : Context) (φ : Formula)
    (h : Derivation Γ φ) : Derivation (Γ_new_elem :: Γ) φ := by
  induction h with
  | ax Γ φ n h =>
    exact ax (Γ_new_elem :: Γ) φ n (List.mem_cons_of_mem Γ_new_elem h)
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

def neg_elim (Γ : Context) (φ : Formula)
    (h₁ : Derivation Γ (Formula.neg φ)) (h₂ : Derivation Γ φ) : Derivation Γ ⊥ := by
  exact imp_elim h₁ h₂

def conj_intro (Γ : Context) (φ ψ : Formula)
    (h₁ : Derivation Γ φ) (h₂ : Derivation Γ ψ) : Derivation Γ (Formula.conj φ ψ) := by
  unfold Formula.conj
  apply neg_intro Γ (φ → (Formula.neg ψ)) `H1
  generalize H1_eq : (`H1, φ → ψ.neg) = H1
  have h1 := weaken_by_cons H1 Γ _ h₁
  have h2 := ax [H1] H1.snd H1.fst (by rw [Prod.eta]; simp)
  have h3 := weaken_by_concat [H1] Γ H1.snd h2
  rw [<- H1_eq] at h3
  simp [H1_eq] at h3
  have h4 := @imp_elim (H1 :: Γ) φ (ψ.neg) h3 h1
  apply imp_elim h4
  apply weaken_by_cons H1 Γ
  exact h₂



  -- -- have h2 := weaken_by_add H1 Γ H1.snd (by )
  -- rw [h1]

  -- intro h_phi_imp_not_psi_hyp -- `h_phi_imp_not_psi_hyp` is the derivation for `φ → ¬ψ`

  -- -- Current context is `Γ'` = `((`hyp_phi_imp_not_psi`, φ → ¬ψ) :: Γ)`.
  -- -- We need to prove `⊥` in `Γ'`.
  -- -- We have `h₁ : Γ ⊢ φ` and `h₂ : Γ ⊢ ψ`.
  -- -- Weaken `h₁` to `Γ'`:
  -- let d_phi_in_Gamma_prime := weaken_by_add (`hyp_phi_imp_not_psi, φ → (Formula.neg ψ)) Γ φ h₁

  -- -- Now we can apply `h_phi_imp_not_psi_hyp` (which is `φ → ¬ψ`) to `d_phi_in_Gamma_prime` (which is `φ`).
  -- -- This yields `¬ψ`.
  -- let d_not_psi_in_Gamma_prime := imp_elim Γ' φ (Formula.neg ψ) h_phi_imp_not_psi_hyp d_phi_in_Gamma_prime

  -- -- Weaken `h₂` to `Γ'`:
  -- let d_psi_in_Gamma_prime := weaken_by_add (`hyp_phi_imp_not_psi, φ → (Formula.neg ψ)) Γ ψ h₂

  -- -- Now we have `d_not_psi_in_Gamma_prime : Γ' ⊢ ¬ψ` and `d_psi_in_Gamma_prime : Γ' ⊢ ψ`.
  -- -- Apply `neg_elim` to get `⊥`.
  -- exact neg_elim Γ' ψ d_not_psi_in_Gamma_prime d_psi_in_Gamma_prime
