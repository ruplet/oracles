import V0Theory.TwoSortedModelTheory.Basic
import V0Theory.TwoSortedModelTheory.Syntax

namespace L2

-- Step 1: Define the two sorts
inductive Sorts
| num : Sorts
| str : Sorts
deriving DecidableEq, Repr

inductive Functions00Num where
| zero
| one

inductive Functions00Str where
| eps

inductive Functions20Num where
| add
| mul

inductive Functions01Num where
| length

inductive Relations20
| eqnum
| leq

inductive Relations02
| eqstr

inductive Relations11
| ins

def Functions (arities: Sorts -> Nat) (retSort: Sorts) : Type
:= match retSort with
| Sorts.num =>
    match arities Sorts.num, arities Sorts.str with
    | 0, 0 => Functions00Num
    | 2, 0 => Functions20Num
    | 0, 1 => Functions01Num
    | _, _ => Empty
| Sorts.str =>
    match arities Sorts.num, arities Sorts.str with
    | 0, 0 => Functions00Str
    | _, _ => Empty

def Relations (arities: Sorts -> Nat) : Type
:= match arities Sorts.num, arities Sorts.str with
| 0, 2 => Relations02
| 2, 0 => Relations20
| 1, 1 => Relations11
| _, _ => Empty

def Lang : TwoSortedFirstOrder.Language Sorts :=
{ Functions := Functions,
  Relations := Relations
}

def varIndT := String
def TermTN n := TwoSortedFirstOrder.Language.Term Sorts Lang (varIndT ⊕ Fin n)
def TermT := TermTN 0

inductive DeltaB0 : Nat -> Type
| openFormula {n} {f : TwoSortedFirstOrder.Language.OpenFormula Sorts Lang varIndT n} : DeltaB0 n
| boundedNumAll {n} (f : DeltaB0 (n + 1)) : DeltaB0 n
| boundedNumEx {n} (f : DeltaB0 (n + 1)) : DeltaB0 n

mutual
inductive SigmaB : Nat -> Nat -> Type
| exPi {nFree : Nat} {lv : Nat} (f : PiB (nFree + 1) lv) (t: TermT Sorts.num) : SigmaB nFree (lv + 1)
| exSigma {nFree : Nat} {lv : Nat} (f: SigmaB (nFree + 1) lv) (t: TermT Sorts.num): SigmaB nFree lv

inductive PiB : Nat -> Nat -> Type
| allSigma {nFree : Nat} {lv : Nat} (f : SigmaB (nFree + 1) lv) (t: TermT Sorts.num) : PiB nFree (lv + 1)
| allPi {nFree : Nat} {lv : Nat} (f: PiB (nFree + 1) lv) (t: TermT Sorts.num): PiB nFree lv
end


namespace FormulaBuilder
-- namespace TermBuilder

open TwoSortedFirstOrder.Language

def arities00 (_: Sorts) : Nat := 0
def arities20 (s: Sorts) : Nat :=
match s with
| Sorts.num => 2
| Sorts.str => 0


-- def nameSubset (name : varIndT) : varIndT ⊕ Fin 0 :=
--   Sum.inl name

def var (s: Sorts) (name: varIndT) : TermTN 0 s :=
  Term.var s (Sum.inl name)

-- /-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
-- @[simp]
-- def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
--   | _m, _n, _h, falsum => falsum
--   | _m, _n, h, equal t₁ t₂ =>
--     equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
--   | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
--   | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
--   | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all


def terms00 : (s: Sorts) -> (Fin (arities00 s)) -> (TermT s) := fun _ => Fin.elim0
-- def terms20 {a b : Nat} (t1: TermTN a Sorts.num) (t2: TermTN b Sorts.num) : (s: Sorts) -> (Fin (arities20 s)) -> TermTN (a + b) s :=
--   fun s =>
--   match s with
--   | Sorts.num =>
--     fun (i: Fin 2) =>
--     match i with
--     | 0 => t1.relabel Sorts Lang (varIndT ⊕ Fin a) (varIndT ⊕ Fin (a + b)) (Sum.map id (Fin.castLE (Nat.le_add_right a b)))
--     -- here, Fin.castLE is needed!
--     -- t1.relabel
--     | 1 => t2.relabel Sorts Lang (varIndT ⊕ Fin b) (varIndT ⊕ Fin (a + b)) (Sum.map id (Fin.castLE (Nat.le_add_left b a)))
--   | Sorts.str => Fin.elim0
def terms20 {n : Nat} (t1 t2: TermTN n Sorts.num) : (s: Sorts) -> (Fin (arities20 s)) -> TermTN n s :=
  fun s =>
  match s with
  | Sorts.num =>
    fun (i: Fin 2) =>
    match i with
    | 0 => t1
    | 1 => t2
  | Sorts.str => Fin.elim0

def funZero : Lang.Functions arities00 Sorts.num := Functions00Num.zero
def funOne : Lang.Functions arities00 Sorts.num := Functions00Num.one
def funAdd : Lang.Functions arities20 Sorts.num := Functions20Num.add
def funMul : Lang.Functions arities20 Sorts.num := Functions20Num.mul

def zero : TermTN 0 Sorts.num :=
  Term.func Sorts.num funZero terms00

def one : TermTN 0 Sorts.num :=
  Term.func Sorts.num funOne terms00

def add {n : Nat} (t1 t2 : TermTN n Sorts.num) : TermTN n Sorts.num :=
  Term.func Sorts.num funAdd (terms20 t1 t2)

def mul {n : Nat} (t1 t2 : TermTN n Sorts.num) : TermTN n Sorts.num :=
  Term.func Sorts.num funMul (terms20 t1 t2)

-- end TermBuilder

-- open TwoSortedFirstOrder.Language

def OpenFormulaT (n: Nat) := OpenFormula Sorts Lang varIndT n

def relEqnum : Lang.Relations arities20 := Relations20.eqnum
def relLeqnum : Lang.Relations arities20 := Relations20.leq

def eqNum {n : Nat} (t1 t2 : TermTN n Sorts.num) : OpenFormulaT n :=
  OpenFormula.rel relEqnum (terms20 t1 t2)

def neNum {n : Nat} (t1 t2 : TermTN n Sorts.num) : OpenFormulaT n :=
  OpenFormula.not $ eqNum t1 t2

def leqNum {n : Nat} (t1 t2 : TermTN n Sorts.num) : OpenFormulaT n :=
  OpenFormula.rel relLeqnum (terms20 t1 t2)

def leNum {n : Nat} (t1 t2 : TermTN n Sorts.num) : OpenFormulaT n :=
  OpenFormula.and (leqNum t1 t2) (neNum t1 t2)

def imp {n : Nat} (p q : OpenFormulaT n) : OpenFormulaT n :=
  OpenFormula.or (OpenFormula.not p) q

notation:100 "%"x => (var Sorts.num x)
notation:50 t1 " + " t2 => add t1 t2
notation:50 t1 " * " t2 => mul t1 t2
notation:45 t1 " <n " t2 => leNum t1 t2
notation:45 t1 " <=n " t2 => leqNum t1 t2
notation:40 t1 " =n " t2 => eqNum t1 t2
notation:40 t1 " !=n " t2 => neNum t1 t2
notation:30 phi " & " psi => OpenFormula.and phi psi
notation:30 phi " ~> " psi => imp phi psi
notation:20 "!" phi => OpenFormula.not $ phi

def B1 (x : varIndT) : OpenFormulaT 0 :=
  ((%x) + zero) =n %x

def B7 (x y : varIndT) : OpenFormulaT 0 :=
  (((%x) <=n (%y)) & ((%y) <=n (%x))) ~> ((%x) =n (%y))

def B9 (x : varIndT) : OpenFormulaT 0 :=
  (%x) <=n zero

def Exercise51a (x : varIndT) : OpenFormulaT 0 :=
  !((%x) <n zero)

end FormulaBuilder

end L2
