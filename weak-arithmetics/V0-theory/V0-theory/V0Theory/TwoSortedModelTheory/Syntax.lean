-- https://github.com/leanprover-community/mathlib4/blob/0c55a410bbb4c0f54eb649c14f25d4a89bb2a49e/Mathlib/ModelTheory/Syntax.lean
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import V0Theory.TwoSortedModelTheory.Basic
-- import Mathlib.ModelTheory.LanguageMap
import Mathlib.Algebra.Order.Group.Nat

universe u v w u' v'
variable (Sorts: Type) [Fintype Sorts]

namespace TwoSortedFirstOrder
namespace Language

variable (L : Language.{u, v} Sorts) {L' : Language Sorts}
variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}

open TwoSortedFirstOrder

-- open Structure
open Fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : (sort: Sorts) -> Type max u u'
  | var sort : α -> Term α sort
  | func sort :
    {arities : Sorts -> Nat} ->
    ∀
    (_f : L.Functions arities sort)
    (_ts : (s : Sorts) → ((Fin (arities s)) → Term α s)),
    Term α sort

export Term (var func)

variable {L}

namespace Term

end Term
end Language
end TwoSortedFirstOrder
