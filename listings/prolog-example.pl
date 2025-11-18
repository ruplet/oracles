% Run at: https://swish.swi-prolog.org/
succ(bit1, bit2).
succ(bit2, bit3).
succ(bit3, bit4).
succ(bit4, bit5).

zero(bit1).
zero(bit3).
one(bit2).
one(bit4).
one(bit5).

exists_1  :- one(X). 							  % true
exists_00 :- succ(X, Y), zero(X), zero(Y).        % false
no_00     :- \+ ( succ(X, Y), zero(X), zero(Y) ). % true
no_11     :- \+ ( succ(X, Y), one(X), one(Y) ).   % false