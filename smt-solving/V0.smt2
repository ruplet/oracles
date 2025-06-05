(set-option :produce-models true)
(set-logic UFLIA)

(declare-sort Nat 0)
(declare-sort Str 0)

; Symbols for the first sort: 0, 1, +, *, ||, = (nat), = (str), <=, in
(declare-fun zero () Nat)
(declare-fun one () Nat)
(declare-fun plus (Nat Nat) Nat)
(declare-fun mul (Nat Nat) Nat)
(declare-fun card (Str) Nat)
(declare-fun eq_nat (Nat Nat) Bool)  ; Equality for Nat
(declare-fun eq_str (Str Str) Bool)  ; Equality for Nat
(declare-fun le_nat (Nat Nat) Bool)  ; Less than for Nat
(declare-fun memb (Nat Str) Bool)

(define-fun neq ((x Nat) (y Nat)) Bool
  (not (eq_nat x y))
)

(define-fun lt_nat ((x Nat) (y Nat)) Bool
    (and (le_nat x y) (neq x y))
)

; --- 2-BASIC Axioms (Figure 2) ---

; B1. x + 1 != 0
(assert (forall ((x Nat)) (not (eq_nat (plus x one) zero))))

; B2. x + 1 = y + 1 => x = y
(assert (forall ((x Nat) (y Nat)) (=> (eq_nat (plus x one) (plus y one)) (eq_nat x y))))

; B3. x + 0 = x
(assert (forall ((x Nat)) (eq_nat (plus x zero) x)))

; B4. x + (y + 1) = (x + y) + 1
(assert (forall ((x Nat) (y Nat)) (eq_nat (plus x (plus y one)) (plus (plus x y) one))))

; B5. x * 0 = 0
(assert (forall ((x Nat)) (eq_nat (mul x zero) zero)))

; B6. x * (y + 1) = (x * y) + x
(assert (forall ((x Nat) (y Nat))
  (eq_nat (mul x (plus y one)) (plus (mul x y) x))
))

; B7. (x <= y /\ y <= x) => x = y
(assert (forall ((x Nat) (y Nat)) (=> (and (le_nat x y) (le_nat y x)) (eq_nat x y))))

; B8. x <= x + y
(assert (forall ((x Nat) (y Nat)) (le_nat x (plus x y))))

; B9. 0 <= x
(assert (forall ((x Nat)) (le_nat zero x)))

; B10. x <= y \/ y <= x
(assert (forall ((x Nat) (y Nat)) (or (le_nat x y) (le_nat y x))))

; B11. x <= y <=> x < y + 1
(assert (forall ((x Nat) (y Nat)) 
    (= (le_nat x y) (lt_nat x (plus y one)))
))
; B12. x neq 0 => exists y . y <= x & (y + 1 = x)
(assert (forall ((x Nat))
    (=>
        (neq x zero)
        (exists
            ((y Nat))
            (and
                (le_nat y x)
                (eq_nat (plus y one) x)
            )
        )
    )
))

; --- L1. X(y) => y < |X| ---
; The `memb` is `in`. The `<` here is the strict less-than.
(assert (forall ((X Str) (y Nat)) (=> (memb y X) (lt_nat y (card X)))))

; --- L2. y + 1 = |X| => X(y) ---
; This implies if `card X` is `y+1`, then `y` must be a member of X.
(assert (forall ((X Str) (y Nat)) (=> (eq_nat (plus y one) (card X)) (memb y X))))

; --- SE. (|X| = |Y| /\ ForAll i < |X| (X(i) <=> Y(i))) => X = Y (Extensionality) ---
; The `<` here is the strict less-than.
; The `X(i)` is `memb i X`.
(assert (forall ((X Str) (Y Str))
  (=> (and (eq_nat (card X) (card Y))
           (forall ((i Nat))
             (=> (lt_nat i (card X))
                 (= (memb i X) (memb i Y)) ; Corrected: using (= A B) for iff
             )
           )
      )
      (eq_str X Y)
  )
))

; Exercise V.1.1. Show that the following formulas are provable from 2-BASIC
; a) not x < 0
(push)
(assert (not (forall ((x Nat)) (not (lt_nat x zero)))))
(check-sat)
(pop)

; b) x < x + 1
(push)
(assert (not (forall ((x Nat)) (lt_nat x (plus x one)))))
(check-sat)
(pop)

; c) 0 < x + 1
(push)
(assert (not (forall ((x Nat)) (lt_nat zero (plus x one)))))
(check-sat)
(pop)

; TIMEOUT
; d) x < y => x + 1 <= y (use B10, B11, B7)
(push)
(assert (not (forall ((x Nat) (y Nat))
    (=> (lt_nat x y) (le_nat (plus x one) y))
)))
(check-sat)
(pop)

; TIMEOUT
; e) x < y => x + 1 < y + 1
(push)
(assert (not (forall ((x Nat) (y Nat))
    (=> (lt_nat x y) (lt_nat (plus x one) (plus y one)))
)))
(check-sat)
(pop)
