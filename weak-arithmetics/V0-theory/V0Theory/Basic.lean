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

open BoundedFormula

-- def x : Term Lang (Empty ⊕ Fin 2) := Term.var (Sum.inr 0)
def funZero : Lang.Functions 0 := functions0.zero
def funOne : Lang.Functions 0 := functions0.one
def funAdd : Lang.Functions 2 := functions2.add
def funMul : Lang.Functions 2 := functions2.mul
def relEq : Lang.Relations 2 := relations2.eq
def relLeq : Lang.Relations 2 := relations2.leq

def x {n : Nat} : Term Lang (Empty ⊕ Fin (n + 1)) := Term.var $ Sum.inr (0 : Fin (n + 1))
def y {n : Nat} : Term Lang (Empty ⊕ Fin (n + 2)) := Term.var $ Sum.inr (1 : Fin (n + 1))

def zero {n : Nat} : Term Lang (Empty ⊕ Fin n) := Term.func funZero Fin.elim0
def one {n : Nat} : Term Lang (Empty ⊕ Fin n) := Term.func funOne Fin.elim0

def add {n : Nat} (a b : Term Lang (Empty ⊕ Fin n)) : Term Lang (Empty ⊕ Fin n) :=
  Term.func funAdd (
    fun argInd => match argInd with
    | 0 => a
    | 1 => b
  )

def mul {n : Nat} (a b : Term Lang (Empty ⊕ Fin n)) : Term Lang (Empty ⊕ Fin n) :=
  Term.func funMul (
    fun argInd => match argInd with
    | 0 => a
    | 1 => b
  )

def eq {n : Nat} (a b : Term Lang (Empty ⊕ Fin n)) : BoundedFormula Lang Empty n :=
  rel relEq (fun argInd => match argInd with | 0 => a | 1 => b)

def leq {n : Nat} (a b : Term Lang (Empty ⊕ Fin n)) : BoundedFormula Lang Empty n :=
  rel relLeq (fun argInd => match argInd with | 0 => a | 1 => b)

def neq {n : Nat} (a b : Term Lang (Empty ⊕ Fin n)) : BoundedFormula Lang Empty n :=
  BoundedFormula.not $ eq a b

def and {n : Nat} (a b : BoundedFormula Lang Empty n) :=
  BoundedFormula.not (imp a (BoundedFormula.not b))

def or {n : Nat} (a b : BoundedFormula Lang Empty n) :=
  imp (BoundedFormula.not a) b

-- x + 1 neq 0
def B1 : Sentence Lang :=
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
