-- `ArithModel` takes 6 arguments and returns a `Prop`: a logical statement.
-- The arguments are an object `num` of type `Type` and 5 proofs
-- of the required properties of `num` - to have designated elements
-- `0`, `1` and to have well-defined `+`, `*`, ... .
structure ArithModel
  (num : Type) [Zero num] [One num] [Add num] [Mul num] [LE num]
where
  b1  : ∀ x : num, x + (1 : num) ≠ 0
  b2  : ∀ x y : num, x + 1 = y + 1 → x = y
  b3  : ∀ x : num, x + 0 = x
  b4  : ∀ x y : num, x + (y + 1) = (x + y) + 1
  b5  : ∀ x : num, x * 0 = 0
  b6  : ∀ x y : num, x * (y + 1) = (x * y) + x
  b7  : ∀ x y : num, x ≤ y ∧ y ≤ x → x = y
  b8  : ∀ x y : num, x ≤ x + y

-- Introduce the 6 variables below to automatically take them as arguments
-- in the functions that use them.
variable (num : Type) [Zero num] [One num] [Add num] [Mul num] [LE num]

-- The function `leq_refl` takes 8 arguments, but Lean is able to
-- automatically infer `[Zero]` etc., and we don't have to pass them explicitly.
-- It returns an object of type `x ≤ x`;
-- the type of the type `x ≤ x` itself is `Prop`.
-- Note that the return type *depends* on the value of `x` which is an argument.
theorem leq_refl (h : ArithModel num) : ∀ x : num, x <= x := by
  intro x
  conv => right; rw [<- h.b3 x]
  apply h.b8

-- As `ArithModel num` is a `Prop`, it can be true; it also can be false.
-- We can prove that `ArithModel Nat` holds for a Lean built-in
-- type `Nat` of natural numbers.
theorem NatModel : ArithModel Nat :=
by
  refine {b1 := ?b1, b2 := ?b2, b3 := ?b3, b4 := ?b4,
          b5 := ?b5, b6 := ?b6, b7 := ?b7, b8 := ?b8}
  · intro x; simp -- this proves b1 for Nat
  · intro x y h
    exact Nat.add_right_cancel h -- this proves b2 for Nat
  repeat sorry -- we skip the rest of proofs for the sake of demo
