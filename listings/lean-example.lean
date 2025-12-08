-- D1. x ≠ 0 → ∃ y ≤ x, x = y + 1  (Predecessor)
-- proof: induction on x
theorem pred_exists :
  ∀ {x : M}, x ≠ 0 → ∃ y ≤ x, x = y + 1 :=
by
  -- peano.Formula (Vars2 .y .x) is the type of deeply-embedded formulas
  -- with two free variables, "y" and "x"
  let ind1 : peano.Formula (Vars2 .y .x) := x =' (y + 1)
  -- similarly below, "y" cannot be free in `ind2`.
  -- `iBdEx' t phi` denotes `∃ var ≤ t . phi` for some variable name `var`
  let ind2 : peano.Formula (Vars1 .x) :=
    (Formula.iBdEx' x (display2 .y ind1).flip)
  -- `display1` takes a formula with 1 free variable and makes it explicit
  -- that it is intended to be bound by the induction axiom scheme
  let ind := idelta0.delta0_induction $ display1 $ (x ≠' 0) ⟹ ind2

  -- prove that the formula actually is Delta0
  unfold ind2 ind1 at ind
  specialize ind (by
    rw [IsDelta0.display1]
    rw [IsDelta0.of_open.imp]
    · constructor
      · unfold Term.neq
        rw [IsDelta0.of_open.not]
        constructor; constructor; constructor
        constructor; constructor
      · constructor
    · unfold Term.neq
      rw [IsOpen.not]
      constructor; constructor
  )
  -- use our custom macro to simplify `ind` to use it in proving
  simp_induction at ind
  -- proceed with the proof by induction; name subgoals; clear helpers
  apply ind ?base ?step <;> clear ind ind1 ind2
  · simp only [IsEmpty.forall_iff]
  · intro a hind h
    exists a
    constructor
    · exact B8 a 1
    · rfl
