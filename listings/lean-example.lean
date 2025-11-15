-- D1. x ≠ 0 → ∃ y ≤ x, x = y + 1  (Predecessor)
-- proof: induction on x
theorem pred_exists :
  ∀ {x : M}, x ≠ 0 → ∃ y ≤ x, x = y + 1 :=
by
  let ind1 : peano.Formula (Vars2 .y .x) := x =' (y + 1)
  let ind2 : peano.Formula (Vars1 .x) :=
    (Formula.iBdEx' x (display2 .y ind1).flip)
  let ind := idelta0.delta0_induction $ display1 $ (x ≠' 0) ⟹ ind2

  unfold ind2 ind1 at ind

  specialize ind (by
    rw [IsDelta0.display1]
    -- TODO: this lemma can't be in @[delta0_simps],
    -- as it creates a goal 'φ.IsOpen' - which might be not true!
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
  simp_induction at ind

  apply ind ?base ?step <;> clear ind ind1 ind2
  · simp only [IsEmpty.forall_iff]
  · intro a hind h
    exists a
    constructor
    · exact B8 a 1
    · rfl
