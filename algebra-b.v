Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.

Section BellantoniCook.
Inductive B : nat -> nat -> Type :=
| zero : B 0 0
| proj : forall {nNormal nSafe : nat},
  Fin.t (nNormal + nSafe)
  -> B nNormal nSafe
| succ : bool -> B 0 1
| pred : B 0 1
| cond : B 0 3
| rec : forall {nNormal nSafe : nat},
  B nNormal nSafe
  -> B (nNormal + 1) (nSafe + 1)
  -> B (nNormal + 1) (nSafe + 1)
  -> B (nNormal + 1) nSafe
| comp : forall {N M nNormal nSafe : nat},
  B N M
  -> Vector.t (B nNormal 0) N
  -> Vector.t (B nNormal nSafe) M
  -> B nNormal nSafe.

End BellantoniCook.

Section Cobham.

Inductive Cobham : nat -> Type :=
| Czero : Cobham 0 (* this is not originally mentioned, but implicitly necessary *)
| Csucc : Fin.t 10 -> Cobham 1
| Csmash : Cobham 2 (* x^{len(y)} *)
| Crec : forall {n : nat},
  Cobham n
  -> Vector.t (Cobham (n + 2)) 10
  -> Cobham (n + 1)
  -> Cobham (n + 1)
| Ccomp : forall {N n : nat},
  Cobham N
  -> Vector.t (Cobham n) N
  -> Cobham n.

End Cobham.




