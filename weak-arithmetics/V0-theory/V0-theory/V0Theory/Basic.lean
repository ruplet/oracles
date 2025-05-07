import V0Theory.TwoSortedModelTheory.Basic
import V0Theory.TwoSortedModelTheory.Syntax

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

def L2 : TwoSortedFirstOrder.Language Sorts :=
{ Functions := Functions,
  Relations := Relations
}

open TwoSortedFirstOrder
open Language
open OpenFormula

def varIndT := String

inductive DeltaB0 : Nat -> Type
| openFormula {n} {f : OpenFormula Sorts L2 varIndT n} : DeltaB0 n
| boundedNumAll {n} (f : DeltaB0 (n + 1)) : DeltaB0 n
| boundedNumEx {n} (f : DeltaB0 (n + 1)) : DeltaB0 n

mutual
inductive SigmaB : Nat -> Nat -> Type
| exPi {nFree : Nat} {lv : Nat} (f : PiB (nFree + 1) lv) (t: Term Sorts L2 varIndT Sorts.num) : SigmaB nFree (lv + 1)
| exSigma {nFree : Nat} {lv : Nat} (f: SigmaB (nFree + 1) lv) (t: Term Sorts L2 varIndT Sorts.num): SigmaB nFree lv

inductive PiB : Nat -> Nat -> Type
| allSigma {nFree : Nat} {lv : Nat} (f : SigmaB (nFree + 1) lv) (t: Term Sorts L2 varIndT Sorts.num) : PiB nFree (lv + 1)
| allPi {nFree : Nat} {lv : Nat} (f: PiB (nFree + 1) lv) (t: Term Sorts L2 varIndT Sorts.num): PiB nFree lv
end
