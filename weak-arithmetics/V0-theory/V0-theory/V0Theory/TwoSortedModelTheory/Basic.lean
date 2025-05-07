-- https://github.com/leanprover-community/mathlib4/blob/0c55a410bbb4c0f54eb649c14f25d4a89bb2a49e/Mathlib/ModelTheory/Basic.lean
-- import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Common
-- import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Fintype.Basic

namespace TwoSortedFirstOrder
universe u v -- u' v' w w'

-- variable (sorta sortb : Type)

-- inductive Sorts where
-- | sorta
-- | sortb

variable (Sorts : Type) [Fintype Sorts]

-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  /-- For every arity, a `Type*` of functions of that arity -/
  Functions : (Sorts -> Nat) -> Sorts -> Type u
  /-- For every arity, a `Type*` of relations of that arity -/
  Relations : (Sorts -> Nat) -> Type v


namespace Language

variable (L : Language Sorts)

end Language
end TwoSortedFirstOrder
