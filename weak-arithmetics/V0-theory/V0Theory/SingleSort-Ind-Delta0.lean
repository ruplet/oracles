import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

namespace L2

inductive Functions0 where
| zero
| one
deriving BEq, DecidableEq

inductive Functions2 where
| add
| mul
deriving BEq, DecidableEq

inductive Relations2 where
| eqnum
| leq
deriving BEq, DecidableEq

def Functions (arity : Nat) : Type :=
  match arity with
  | 0 => Functions0
  | 2 => Functions2
  | _ => Empty


def Relations (arity : Nat) : Type :=
  match arity with
  | 2 => Relations2
  | _ => Empty

def Lang : FirstOrder.Language :=
{ Functions := Functions,
  Relations := Relations
}

open FirstOrder.Language (Term BoundedFormula Formula Sentence)

def isOpen (sentence: FirstOrder.Language.Sentence Lang) : Bool :=
match sentence with
| .falsum => true
| .equal _ _ => false -- please use our internal equation symbol!
| .rel _ _ => true
| .imp pre post => isOpen pre ∧ isOpen post
| .all _ => false

def contains_var_zero {a} [DecidableEq a] {n} (t : Lang.Term (a ⊕ Fin n)) : Bool :=
  if h_eq : n = 0 then
    false
  else
    (Sum.inr $ @Fin.mk n 0 (Nat.pos_of_ne_zero h_eq)) ∈ t.varFinset

def is_x_le_t_imp_A {a} [DecidableEq a] {n} (f : Lang.BoundedFormula a n) : Bool :=
  match f with
  | BoundedFormula.imp pre _ =>
    match pre with
    | @BoundedFormula.rel _ _ _ l R ts =>
      if h_eq_2 : l = 2 then
        let relationLeq : Lang.Relations 2 := Relations2.leq
        let R_as_rel2 : Relations2 := Eq.mp (congrArg Lang.Relations h_eq_2) R
        let term_vec_type (k : ℕ) := Fin k → Term Lang (a ⊕ (Fin n))
        let ts_as_fin2 : term_vec_type 2 := Eq.mp (congrArg term_vec_type h_eq_2) ts
        if R_as_rel2 == relationLeq then
          let x_term := ts_as_fin2 (0 : Fin 2)
          let t_term := ts_as_fin2 (1 : Fin 2)
          -- Check if x_term is the de Bruijn index 0
          (match x_term with
           | Term.var (Sum.inr j) => j == (0 : Fin (n + 1))
           | _ => false) &&
          -- Check if t_term does NOT contain the de Bruijn index 0
          !(contains_var_zero t_term)
        else false
      else false
    | _ => false
  | _ => false

def isDelta0 {a} [DecidableEq a] {n} : Lang.BoundedFormula a n -> Bool
| .falsum => true
| .equal _ _=> false
| .rel _ _ => true
| .imp pre post => isDelta0 pre ∧ isDelta0 post
| .all phi =>
  (is_x_le_t_imp_A phi) ∧ (isDelta0 phi) -- Recursively check inner formula

def relationEq : Lang.Relations 2 := Relations2.eqnum
def relationLeq : Lang.Relations 2 := Relations2.leq

-- --- Sentence Construction Helpers ---
-- For sentences, α is Empty, and n is 0.

-- A variable term (for current context `n`).
-- For sentences, `n = 0`, so `Fin 0` is `Empty`.
-- If we're inside `all {n} f`, then `f` has context `n+1`, so `Fin (n+1)`.
def var_term {k : ℕ} (idx : Fin k) : Term Lang (Empty ⊕ (Fin k)) := Term.var (Sum.inr idx)

-- -- A constant term (e.g., 0 or 1 from `L2.Functions0`)
-- def const_term (c : Lang.Functions 0) : Term Lang (Empty ⊕ (Fin 0)) := Term.func c ![]

-- -- A term from a unary function (if you had any, e.g., successor)
-- -- def unary_func_term (f : Lang.Functions 1) (t : Term Lang (Empty ⊕ (Fin k))) : Term Lang (Empty ⊕ (Fin k)) := Term.func f ![t]

-- -- A term from a binary function (e.g., add, mul)
-- def binary_func_term {k : ℕ} (f : Lang.Functions 2) (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : Term Lang (Empty ⊕ (Fin k)) := Term.func f ![t1, t2]

-- A constant term. Now `k` is a free variable, so Lean can infer it.
-- This term type is `Term Lang (α ⊕ (Fin k))`
def const_term {α} {k : ℕ} (c : Lang.Functions 0) : Term Lang (α ⊕ (Fin k)) := Term.func c ![]

-- A term from a binary function (e.g., add, mul). `k` is also generic here.
def binary_func_term {α} {k : ℕ} (f : Lang.Functions 2) (t1 t2 : Term Lang (α ⊕ (Fin k))) : Term Lang (α ⊕ (Fin k)) := Term.func f ![t1, t2]

-- Atomic formulas
def eq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationEq ![t1, t2]

def leq_form {k : ℕ} (t1 t2 : Term Lang (Empty ⊕ (Fin k))) : BoundedFormula Lang Empty k :=
  BoundedFormula.rel relationLeq ![t1, t2]

def falsum_form {a} {k : ℕ} : Lang.BoundedFormula a k := BoundedFormula.falsum

def imp_form {a} {k : ℕ} (f1 f2 : BoundedFormula Lang a k) : BoundedFormula Lang a k :=
  BoundedFormula.imp f1 f2

def all_form {a} {k : ℕ} (f : BoundedFormula Lang a (k + 1)) : BoundedFormula Lang a k :=
  BoundedFormula.all f

-- --- Example Sentences ---

-- 1. Open Sentences (no quantifiers)

def funcZero := Functions0.zero
def funcOne := Functions0.one
def funcAdd := Functions2.add
def funcMul := Functions2.mul

-- 0 = 1 (false)
def open_s_1 : Sentence Lang :=
  eq_form (const_term funcZero) (const_term funcOne)

-- 0 <= 0 (true)
def open_s_2 : Sentence Lang :=
  leq_form (const_term funcZero) (const_term funcZero)

-- (0 <= 1) -> (1 = 0)
def open_s_3 : Sentence Lang :=
  imp_form (leq_form (const_term funcZero) (const_term funcOne))
           (eq_form (const_term funcOne) (const_term funcZero))

-- 2. Delta0 Sentences (only bounded quantifiers)

-- ∀x (x <= 1 -> x = 0)
-- Here, x corresponds to the de Bruijn index 0 in the inner formula.
-- '1' is the constant `funcOne`.
def delta0_s_1 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) (const_term funcOne))
                     (eq_form (var_term (0 : Fin 1)) (const_term funcZero)))

-- ∀x (x <= 1 -> (x = 0 -> x <= 1))
def delta0_s_2 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) (const_term funcOne))
                     (imp_form (eq_form (var_term (0 : Fin 1)) (const_term funcZero))
                               (leq_form (var_term (0 : Fin 1)) (const_term funcOne))))

-- ∀x (x <= y -> x = 0) -- This is NOT a sentence because 'y' is a free variable (unless y is 0 here)
-- Let's make it a proper sentence: ∀x (x <= 1 + 1 -> x = 0)
-- The term `1 + 1` should not contain `x` (de Bruijn index 0).
def term_one_plus_one : Term Lang (Empty ⊕ (Fin 1)) :=
  binary_func_term funcAdd (const_term funcOne) (const_term funcOne)

def delta0_s_3 : Sentence Lang :=
  all_form (imp_form (leq_form (var_term (0 : Fin 1)) term_one_plus_one)
                     (eq_form (var_term (0 : Fin 1)) (const_term funcZero)))


-- 3. Pi1 Sentences (block of universal quantifiers, inner formula is Delta0)

-- ∀x (x = x) -- This is Pi1 (vacuously Delta0 inside) and also not Delta0 (unbounded quantifier)
def pi1_s_1 : Sentence Lang :=
  all_form (eq_form (var_term (0 : Fin 1)) (var_term (0 : Fin 1)))

-- ∀x (∀y (x <= y -> x = x)) -- This is Pi1 (inner is Delta0, outer is unbounded)
-- The `(0 : Fin 1)` refers to `y`, `(1 : Fin 2)` refers to `x` in the `Fin 2` context
def pi1_s_2 : Sentence Lang :=
  all_form (all_form (imp_form (leq_form (var_term (1 : Fin 2)) (var_term (0 : Fin 2))) -- x <= y
                                (eq_form (var_term (1 : Fin 2)) (var_term (1 : Fin 2))))) -- x = x

-- Let's make a Pi1 where the inner formula is a full Delta0 formula with its own bounded quantifier
-- ∀z (∀x (x <= 1 -> x = 0)) -- This is Pi1, the outermost `z` is unbounded
def pi1_s_3 : Sentence Lang :=
  all_form (all_form (imp_form (leq_form (var_term (0 : Fin 2)) (const_term funcOne))
                                (eq_form (var_term (0 : Fin 2)) (const_term funcZero))))

-- --- Test Cases ---

#eval isOpen open_s_1   -- Expected: true
#eval isDelta0 open_s_1 -- Expected: true (open formulas are vacuously Delta0)

#eval isOpen open_s_2   -- Expected: true
#eval isDelta0 open_s_2 -- Expected: true

#eval isOpen open_s_3   -- Expected: true
#eval isDelta0 open_s_3 -- Expected: true

#eval isOpen delta0_s_1   -- Expected: false
#eval isDelta0 delta0_s_1 -- Expected: true

#eval isOpen delta0_s_2   -- Expected: false
#eval isDelta0 delta0_s_2 -- Expected: true

#eval isOpen delta0_s_3   -- Expected: false
#eval isDelta0 delta0_s_3 -- Expected: true

#eval isOpen pi1_s_1    -- Expected: false
#eval isDelta0 pi1_s_1    -- Expected: false (unbounded quantifier)

#eval isOpen pi1_s_2    -- Expected: false
#eval isDelta0 pi1_s_2    -- Expected: false (outer quantifier is unbounded)

#eval isOpen pi1_s_3    -- Expected: false
#eval isDelta0 pi1_s_3    -- Expected: false (outermost quantifier is unbounded)


-- Section 3.1 Peano Arithmetic (Draft)


structure BASICModel where
  -- Sorts
  num    : Type          -- First sort: natural numbers

  -- Functions and predicates for num
  zero   : num
  one    : num
  add    : num → num → num
  mul    : num → num → num
  le     : num → num → Prop
  eqnum  : num → num → Prop := fun x y => x = y

  -- B1. x + 1 ≠ 0
  B1 : ∀ (x : num), add x one ≠ zero

  -- B2. x + 1 = y + 1 ⊃ x = y
  B2 : ∀ (x y : num), add x one = add y one → x = y

  -- B3. x + 0 = x
  B3 : ∀ (x : num), add x zero = x

  -- B4. x + (y + 1) = (x + y) + 1
  B4 : ∀ (x y : num), add x (add y one) = add (add x y) one

  -- B5. x · 0 = 0
  B5 : ∀ (x : num), mul x zero = zero

  -- B6. x · (y + 1) = (x · y) + x
  B6 : ∀ (x y : num), mul x (add y one) = add (mul x y) x

  -- B7. (x ≤ y ∧ y ≤ x) ⊃ x = y
  B7 : ∀ (x y : num), le x y → le y x → x = y

  -- B8. x ≤ x + y
  B8 : ∀ (x y : num), le x (add x y)

  -- C. 0 + 1 = 1
  C : add zero one = one

def lt (M : BASICModel) (x y : M.num) : Prop :=
  M.le x y ∧ x ≠ y

structure IOPENModel extends BASICModel where
  -- the sole `num` argument of `φ` is the exposed free
  -- variable for induction purposes!
  OPEN (φ : num -> Prop) : Prop

  open_induction :
    ∀ (φ : num → Prop),
    OPEN φ →
    φ zero →
    (∀ x, φ x → φ (add x one)) →
    ∀ x, φ x


axiom open_add_zero : IOPENModel.OPEN (λ x => add x zero = x)
theorem add_x_zero_eq_x (M : IOPENModel) : ∀ x, M.add x M.zero = x :=
  M.open_induction
    (λ x => M.add x M.zero = x)
    open_add_zero
    (by
      -- base case: add 0 0 = 0 by axiom B1
      exact M.b1)
    (by
      -- inductive step: assume add x 0 = x ⇒ add (x+1) 0 = x + 1
      intros x ih
      -- use axiom B2: add (x+1) y = (add x y) + 1
      have h := M.b2 x M.zero
      rw [h, ih]
      exact rfl)
