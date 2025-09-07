# Directions left unexplored

## Straight-up formalization using turing machines:
previous approaches to formalize turing machines in coq; dafny; why3

## Some obvious and obviously impractical approaches
- The obvious approach: LOOP language.  
problem: it is PRA. it is not practical.

- Another obvious approach is: python + polynomial expressing max  
number of steps. Problem: semantics impossible to reason about.

- another obvious approach: "natural number coding nth program of a language
having these properties". problem: syntax might be undecidable! won't write an
interpreter.

- another approach: only use Nat type and grzegorczyk hierarchy. problem: ?

## Explicit characterizations
Need Coq to check (and define!) the proof that term is really less than some boud.

## Classes (conjectured) impossible to be captured syntactically
Some of the studied complexity classes remain notoriously difficult to be characterized implicitly. 
The classes for which a characterization exists are called 'syntactic' complexity classes, as opposed to 'semantic'
complexity classes, for which such characterization is conjectured to not exist.

- BPP  
    a characterization of which was however studied in [@lago2012higherordercharacterizationprobabilisticpolynomial].
    Despite that, PP has been characterized implicitly by Dal Lago in 2021: $\text{PP}$ [@dallago_et_al:LIPIcs.MFCS.2021.35].

- permutation-invariant PTIME
    The class `inv-P` of graph permutation-invariant problems decidable in polynomial time, is conjectured
    to not be characterizable this way. This is a restatement of the problem of finding a "logic capturing PTIME on unordered structures".
    A good discussion of this problem is present in Anuj Dawar's presentation from 2012: [@dawar2012syntactic].

## Decisive class characterizations
We only study classes for functions in general, not only these outputing a bool

## Descriptive complexity
it goes from another side. we want to define computations, not result!

## Fine-grained complexity
No results to be used for our research. The fields are not yet connected.