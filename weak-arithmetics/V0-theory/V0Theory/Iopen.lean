import Mathlib.ModelTheory.Syntax

open FirstOrder.Language

inductive functions0 where
| zero
| one

inductive functions2 where
| add
| mul

inductive relations2 where
| eq
| leq

-- arity to type of functions of given arity
def Functions (n : Nat) : Type :=
  match n with
  | 0 => functions0
  | 2 => functions2
  | _ => Empty

def Relations (n : Nat) : Type :=
  match n with
  | 2 => relations2
  | _ => Empty

def Lang : FirstOrder.Language :=
{
  Functions := Functions,
  Relations := Relations
}

-- this BoundedFormula is something completely different
-- to bounded formulas from Cook and Nguyen!
-- this 'bounding' refers to number of free variables only
open BoundedFormula

-- def zero {n : Nat} : Term Lang (Empty ⊕ Fin n) := Term.func funZero Fin.elim0
def zero {fvDom} : Term Lang fvDom :=
  Constants.term funZero
  where funZero : Lang.Constants := functions0.zero

def one {fvDom} : Term Lang fvDom :=
  Constants.term funOne
  where funOne : Lang.Constants := functions0.one

def add {fvDom} (a b : Term Lang fvDom) :=
  Functions.apply₂ funAdd a b
  where funAdd : Lang.Functions 2 := functions2.add

def mul {fvDom} (a b : Term Lang fvDom) :=
  Functions.apply₂ funMul a b
  where funMul : Lang.Functions 2 := functions2.mul

def eq {fvDom} {n} (a b : Term Lang (fvDom ⊕ Fin n)) :=
  Relations.boundedFormula₂ relEq a b
  where relEq : Lang.Relations 2 := relations2.eq

def leq {fvDom} {n} (a b : Term Lang (fvDom ⊕ Fin n)) :=
  Relations.boundedFormula₂ relLeq a b
  where relLeq : Lang.Relations 2 := relations2.leq

def neq {fvDom} {n} (a b : Term Lang (fvDom ⊕ Fin n)) : BoundedFormula Lang fvDom n :=
  BoundedFormula.not $ eq a b

-- this only holds in classical logic!
def and {fvDom} {n} (a b : BoundedFormula Lang fvDom n) :=
  min a b

-- this only holds in classical logic!
def or {fvDom} {n} (a b : BoundedFormula Lang fvDom n) :=
  max a b

-- def l {fvDom} {k} (var : fvDom) (f : BoundedFormula Lang fvDom k) :=
--   castLE (Nat.le_succ k) f

-- def fall {k} (var : fv) (f : BoundedFormula Lang fv k) :=
--   all $
--     relabel (
--       fun x => match x with
--       | var => Sum.inr (k : Fin (k + 1))
--       | t => t
--     )
--     f
--     -- (castLE (Nat.le_succ k) f)

-- inductive fv | x | y | z deriving DecidableEq

-- def fall {k} (var : fv) (phi : BoundedFormula Lang fv k)
--   : BoundedFormula Lang {v : fv // v != var} (k + 1) :=
--   subst phi (
--     fun v =>
--       if v == var
--       then Term.var $ Sum.inr (k : Fin (k + 1))
--       else Term.var $ Sum.inl v
--   )
-- def x {n : Nat} : Term Lang (fv ⊕ Fin (n + 1)) :=
--   Term.var $ Sum.inl fv.x


-- warning: this 'x' can bind to different quantifiers,
-- as it is not actually named! it will bind to first quantifier in scope
-- y will bind to second etc.

inductive isAtLevel {fvDom} (n : Nat) : Term Lang (fvDom ⊕ Fin (n + 1)) -> Prop
| mk : isAtLevel n $ Term.var $ Sum.inr n

-- def atLevel {fvDom} (n : Nat) := Subtype (@isAtLevel fvDom n)
def atLevel {fvDom} (n : Nat) :=
  { t : Term Lang (fvDom ⊕ Fin (n + 1)) // isAtLevel n t}

def x {fvDom} {n} : Term Lang (fvDom ⊕ Fin (n + 1)) := Term.var $ Sum.inr 0
def y {fvDom} {n} : Term Lang (fvDom ⊕ Fin (n + 2)) := Term.var $ Sum.inr 1
def z {fvDom} {n} : Term Lang (fvDom ⊕ Fin (n + 3)) := Term.var $ Sum.inr 2
-- def x {fvDom} : @atLevel fvDom 0 := ⟨Term.var $ Sum.inr 0, isAtLevel.mk⟩
-- def y {fvDom} : @atLevel fvDom 1 := ⟨Term.var $ Sum.inr 1, isAtLevel.mk⟩
-- -- def y {fvDom} {n} : Term Lang (fvDom ⊕ Fin (n + 2)) := Term.var $ Sum.inr 1

-- -- this is pretty clever - since it's difficult to reason about formulas
-- -- with actual named free variables, we will just do a check that
-- -- the quantifier we add is at the desired depth, denoted by
-- -- the variable it should bind!
-- def fall {fvDom} {n} (_ : @atLevel fvDom n) (phi : BoundedFormula Lang fvDom (n + 1)) :=
--   all phi

-- now, this is type mismatch!
-- def B1 : Sentence Lang :=
--   fall y $ neq (add x one) zero
-- but this works!
-- shitty idea. it binds in other order than intuitive!
def B1 : Sentence Lang :=
  -- for the <> version, use x.val to discard proof
  all $ neq (add x one) zero

def B2 : Sentence Lang :=
  all $ all $ imp (eq (add x one) (add y one)) (eq x y)

def B3 : Sentence Lang :=
  all $ eq (add x zero) x

def B4 : Sentence Lang :=
  all $ all $ eq (add x (add y one)) (add (add x y) one)

def B5 : Sentence Lang :=
  all $ eq (mul x zero) zero

def B6 : Sentence Lang :=
  all $ all $ eq (mul x (add y one)) (add (mul x y) x)

def B7 : Sentence Lang :=
  all $ all $ imp (and (leq x y) (leq y x)) (eq x y)

def C : Sentence Lang :=
  eq (add zero one) one

def Basic1 : Theory Lang := {B1, B2, B3, B4, B5, B6, B7, C}

-- inductive isOpen : Π {n : Nat}, BoundedFormula Lang Empty n -> Prop
inductive isOpen {n} : BoundedFormula Lang Empty n -> Prop
| falsum : isOpen $ falsum
-- | equal R ts : isOpen $ equal R ts
| rel R ts : isOpen $ rel R ts
| imp f1 f2 : isOpen $ imp f1 f2

def OpenFormula {n : Nat} := Subtype (@isOpen n)

-- inductive isDelta0 : (n : Nat) -> BoundedFormula Lang Empty n -> Prop
-- | falsum n : isDelta0 n $ falsum
-- | rel R ts : isDelta0 n $ rel R ts
-- | imp f1 f2 : isDelta0 n $ imp f1 f2
-- | all (f : isDelta0 (n + 1)) (bound : Term Lang (Empty ⊕ Fin n)) : isDelta0 $ all (imp (leq x bound) f)

-- open fv

inductive fv
| x

-- def Induction {n} (phi : BoundedFormula Lang fv n) : Sentence Lang :=
--   BoundedFormula.alls $ imp (and phi0 (imp phix phixp1)) (all phix)
--   where
--     phi0 : BoundedFormula Lang Empty n := phi.subst (
--       fun ident =>
--       match ident with
--       | fv.x => zero
--     )

--     phix : BoundedFormula Lang Empty (n + 1) :=
--       subst (castLE (Nat.le_succ n) phi) (
--         fun ident =>
--         match ident with
--         | fv.x => Term.var $ Sum.inr n
--       )

--     phixp1 : BoundedFormula Lang Empty (n + 1) :=
--       subst (castLE (Nat.le_succ n) phi) (
--         fun ident =>
--         match ident with
--         | fv.x => add Term.var $ Sum.inr n
--       )

-- def Induction (phi : BoundedFormula Lang Empty 1) : Sentence Lang :=
--   BoundedFormula.alls $ imp (and phi0 (imp phix phixp1)) (all phix)

-- def OpenInduction := { }

def induction_ex_O1 : Sentence Lang :=
  imp (and base step) (target)
  where
    -- phi(0); forall x y . (x + y) + 0 = x + (y + 0)
    base := all $ all $ eq (add (add x y) zero) (add x (add y zero))
    -- forall z . forall x y . phi(z) -> phi(z + 1)
    -- now quantifier order matters!
    step := all $ all $ all $
      imp
        (eq (add (add x y) z) (add x (add y z)))
        (eq (add (add x y) (add z one)) (add x (add y (add z one))))

    -- forall z, phi(z)
    target := all $ all $ all $ eq (add (add x y) z) (add x (add y z))

def IOPEN : Theory Lang := Set.union {B1, B2, B3, B4, B5, B6, B7, C} {induction_ex_O1}

-- example III.1.8: the following formulas (and their universal closures)
-- are theorems of IOPEN:
-- O1. (x + y) + z = x + (y + z) ; associativity of +; by induction z
def ex_III_1_8_O1_stmt : Sentence Lang :=
  all $ all $ all $ eq (add (add x y) z) (add x (add y z))

-- theorem ex_III_1_8_O1 : provable IOPEN ex_III_1_8_O1_stmt
