-- https://github.com/leanprover-community/mathlib4/blob/0c55a410bbb4c0f54eb649c14f25d4a89bb2a49e/Mathlib/ModelTheory/Syntax.lean
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import V0Theory.TwoSortedModelTheory.Basic
-- import Mathlib.ModelTheory.LanguageMap
import Mathlib.Algebra.Order.Group.Nat


namespace TwoSortedFirstOrder

universe w u' v'

namespace Language

universe u v x
variable (Sorts: Type x) [Fintype Sorts]
variable (L : Language.{u, v} Sorts) -- {L' : Language Sorts}
variable (varIndT: Type u')

open TwoSortedFirstOrder

-- open Structure
open Fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term : (sort: Sorts) -> Type max u u' x
  | var sort : varIndT -> Term sort
  | func sort :
    {arities : Sorts -> Nat} ->
    ∀
    (_f : L.Functions arities sort)
    (_ts : (s : Sorts) → ((Fin (arities s)) → Term s)),
    Term sort

-- export Term (var func)

-- variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}
-- variable {a : Type u'}
-- variable {L}

-- variable (L) (α)

-- definition II.2.2 CookNguyen
/-- `OpenFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive OpenFormula : ℕ → Type max u v u' x
  | falsum {n} : OpenFormula n
  | truth {n} : OpenFormula n
  | rel
    {n}
    {arities : Sorts -> Nat}
    (R : L.Relations arities)
    (ts :
      (s : Sorts) -> ((Fin (arities s)) → L.Term Sorts (varIndT ⊕ (Fin n)) s)
    )
    : OpenFormula n
  | not {n} (A: OpenFormula n) : OpenFormula n
  | and {n} {m} (A: OpenFormula n) (B: OpenFormula m) : OpenFormula (n + m)
  | or {n} {m}  (A: OpenFormula n) (B: OpenFormula m) : OpenFormula (n + m)
  -- | all {n} (f : OpenFormula (n + 1)) : OpenFormula n
  -- implication A -> B is defined as not A or B (classical logic!)
  -- | ex {n} (f : OpenFormula (n + 1)) : OpenFormula n

end Language
end TwoSortedFirstOrder
