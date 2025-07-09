# Introduction: what should we (and what we can) expect from a programming language?

Thousands of programming languages have been invented since the creation of first computers in the 1940s.
Practically any algorithm invented to be run on a standard computer could be readily implemented using
the languages already existing. Nevertheless, the research on the design of programming languages is
far from being settled. There are properties of computer programs that are highly desirable,
but notoriously difficult to be guaranteed by design, for example:
- a program documented to perform some computation and return a result should not run into an
  infinite loop
- a program implementing an O(n)-time algorithm, and documented to execute in O(n) should not
  need O(n^2) time to run by an accident in the implementation.
- thoughtfully written (i.e. "clean") code should convince the user reading it that
  it does what it is documented to. One way this is typically done is including parts of proof
  of correctness in the documentation. Another way is declaring a function to have a particular type
  and ensuring the user can quickly verify the implementation type-checks.


Co czyni jedne jezyk programowania lepszy od drugiego?
Co czyni kod czystszy od innego, dla tego samego problemu?
Krotszy dowod poprawnosci!
porownanie:
- kod w C vs wygenerowany ASM
- kod, ktory dla kazdej z 256 mozliwych wartosci chara zwraca wynik funkcji vs ktory oblicza


# Różne wyniki z teorii złożoności
P vs FP
TFNP, źródła niekonstruktywności (PPP, PPAD, etc.)
Morioka: kolorowanie grafu jako przyklad problemu ktory sie nie redukuje
self-reducibility
relacje vs funkcje, search problems vs functional problems (cook, nguyen)
implicit vs explicit characterizations: taki jezyk dla FP, w ktorym program to (Python, polynomial)
co to znaczy problem FP-zupelny?
język: problem z FP + AC0-redukcje / L-redukcje = FL-funkcje
czy Descriptive Complexity dostarcza nam języka dla decyzyjnego P? Co to jest struktura uporzadkowana?

<!-- Some properties of computer programs are so often desirable and so important that the
designers of modern programming languages have found ways to address them successfully, notably:
- by passing an array using a `const` pointer in C, we can "guarantee" that when array
  is not "expected" to be modified by a function, it will actually not be.
- by using the C++ RAII technique [1], we can practically guarantee that whenever an object is
  expected by the programmer to be initialized, it actually will be, and that it will not dangle
  after its lifetime causing a memory leak
- by using monads carefully in Haskell, we can "guarantee" that a function won't have
  unexpected side-effects such as writing to stdout -->

[1] - https://en.cppreference.com/w/cpp/language/raii.html


1. dlaczego potrzebujemy języka programowania?
   dla "czystego kodu" = argumentu poprawności programu!
   przykład: język programowania = liczba naturalna -> n-ta maszyna Turinga
   przykład: język programowania = ASM
   dygresja: Rice theorem, saying that any semantic property of TM is undecidable, doesn't apply - 
     we operate in a subset of TM programs such that some particular property IS decidable!
   w tym celu musimy z jednej strony móc "wyłączyć" pewne możliwości (soundness),
   by zachować własność "jeśli coś jest oznaczone jako poprawne, to wierzymy że będzie poprawne"
   a z drugiej - pewne "dodać" (completeness),
   by móc "ładnie" napisać każdy program o którym pomyślimy.
2. ograniczanie z góry - soundness: jakie własności języka programowania dają nam pożądany argument poprawności?
  - każdy program terminuje
  - static type system: jeśli obiekt ma typ A, to nie ma typu B? subject reduction breaking
  - Hoare-style pre/post condition checking?
  - każdy program działa w czasie wielomianowym?
  - dla każdej permutacji wejścia (wierzchołków grafu) zwróci ten sam wynik?
  - każdy typ jest niepusty? STLC inhabitation problem complexity
3. ograniczanie z dołu - completeness:
  - automatyczna inferencja typów
  - dodanie GADT (niszczy principal type property)
  - dodanie kontynuacji
  - cechy języków z JPP
  - siła wyrazu STLC
  - interakcje różnych feature'ów
4. języki programowania wyrażające klasy złożoności
  - Cobham
  - Neergaard (+ moje programy w Haskellu + moje odświeżenie jego repo)
  - dal Lago (+ moja prośba o licencję)
  - logiki liniowe!
  - Bellantoni Cook
  - David Nowak, Sylvain Heraud (formalizacja Cobham = BC)
  - przegląd literatury
  - koncepcja: różnica między algebrą BCeps- a BC jest taka, że BCeps- "wymaga"
    re-obliczania podwyrażeń po zrobieniu na nich ifa. To jest insight za L neq P
  - mały paper z Marktoberfest (Murawski); nieznana praca Neergaarda nieopublikowana
5. logiki wyrażające klasy złożoności
  - indepence proof = nie-implementowalność programu w danym języku
  - witnessing theorem = code extraction
  - siła języka vs siła metateorii (związek z JPP, czy syntax to drzewo,
     jaka najsłabsza teoria może udowodnić Soundness innej teorii)
  - extension of a theory
  - język programowania "odpowiadający" RCA0, tj. programy to implementacje funkcji
      będące dowodami twierdzeń (specyfikacji)
  - RCA0 neq WKL0, ale w logice pierwszego rzedu (specyfikacji pierwszego rzedu), te
      teorie sa sobie rownowazne. Czyli dla prostych specyfikacji, nowe feature'y 'dodane'
      dla dowodow w WKL0, nie dodaja sily wyrazu do jezyka

dygresja:
- formalizacja maszyn turinga (kontakt z Yannickiem Forsterem)
- moje odswiezenie wyniku Ciaffaglionego (nierozstrzygalnosc halt) + komunikacja z ludzmi z undecidability lib


co mnie interesowalo:
1. probability without axiom of choice / non-measurable sets (Solovay)
2. definicja i istotnosc kompozycjonalnosci syntaxu
3. czy mozna byc informatykiem bez magit, topo 2, topalg
4. jezyk programowania z typami liniowymi (dla komputera kwantowego)
5. jezyk niezmienny ze wzgledu na porzadek struktury na wejsciu (p vs np)
6. gdzie znalezc algorytm 'synchronizacja grupowa' z pw, dziedziczenie sekcji krytycznej

! 7. automatyczne sprawdzanie trojek Hoare'a - rozwiazane! Dafny
8. wymagania z JPP vs utrata wlasnosci jezyka po dodaniu do niego feature'ow
  - sml + continuations unsound
  - adding gadts breaks Principal-type property, which is necessary for modular type inference
9.  zero knowledge proof of password knowledge
10. czemu chcemy koniecznie żeby syntax był CFG? 
11. extended curry-howard:
  - double negation ~ first-class callbacks
  - friedman's translation ~ dynamic exeptions
  - cohen's forcing ~ global variables
  - dialectica trans. ~ scoped gotos (a la Python's yield)
12. POMYSL (Tiuryn): taka hierarchia jezykow programowania, w ktorej:
  - definiujesz problem do rozwiazania
  - sprawdzasz w jakim najslabszym jezyku mozesz zdefiniowac problem (np logika odp. PTIME)
  - sprawdzasz w jakim jezyku mozesz napisac rozwiazanie
13. Descriptive complexity
14. losowanie losowego słowa matchującego regex (regular grammars? + boltzmann samplers?)
15. losowanie losowego DAGu? sudoku, rubik, 15-puzzle
16. losowanie losowego grafu izomorficznego do danego na wejściu? to by chyba NIE prowadzilo
    do sensowengo zrandomizowanergo algorytmu testowania izomorficznosci grafow
17. POPL: jaka teoria wystarczy zeby obliczyc GCD itd. (bounded arithmetic)
18. CoqPL: Hamilton to itauto
19. losowe generowanie sudoku: uniform generation of NP witnesses :)
20. SAT competition etc.: https://docs.google.com/document/d/1K4UHdfplQ2ImxofjGuqVh-CazCaOKVxv6Ftte5ROVas/edit?tab=t.0 
21. formalizacja: Foundations; palalansouki
22. importance of descriptive complexity: (https://eccc.weizmann.ac.il/resources/pdf/morioka.pdf)
Theorem 2.1. [BIS90, Imm99] A relation  is in    iff it is representable by an  -
sentence.
23. Morioka tells that it is important to tell between decision and function complexity classes!
Cook, Nguyen shows that FAC0 is enough for reductions
24. Cook-Nguyen (history):
The universal theory VPV is based on the single-sorted theory PV [39].
which historically was the first theory designed to capture polynomial time
reasoning. 

25. Język programowania to JEST system dowodowy.
Żeby do teorii dodac axiom schema of comprehension, trzeba do języka programowania dodać funkcję filter.
Żeby dodać indukcję, trzeba dodać rekurencję dla pewnych operacji.
To do czego język programowania się interpretuje, powinno w sumie MODELOWAĆ teorię np. V0:

jeśli mamy aksjomaty
x >= 0
x + (y + z) == (x + y) + z

to po prostu gwarantujemy że w "prawdziwym" życiu, do którego kompilujemy, one naprawdę zachodzą.

KOLODZIEJCZYK:
po prostu zebrac informacje (z ksiazki Cook Nguyen, z Morioki)
ktore mam na temat witnessingu. podeslac mu. tam jest tez wzmianka o refleksji (RFN)


Bounded arithmetic:

file:///home/maryjane/Downloads/1235421934.pdf
strona 52 pdf, strona 316 ksiazki
chapter V Bounded arithmetic
tu jest o kodowaniu CFG

Urzyczyn, podzbiory IIPL:
https://arxiv.org/pdf/2405.05670#section.5

QBF solver:
https://github.com/lonsing/nenofex
https://github.com/lonsing/depqbf

QBF evaluation competition 2023
https://qbf23.pages.sai.jku.at/gallery/
https://doi.org/10.1016/j.artint.2019.04.002
SAT 2025:
https://satisfiability.org/SAT25/dates/



SML online:
https://sosml.org/editor?0&

Paper:
Suppose IS12 proves Exists y . A(y, c).
Then S12 proves istnieje dowod
https://mathweb.ucsd.edu/~sbuss/ResearchWeb/intuitionisticBA/intuitionisticBA_OCR.pdf
Tutaj strona 160 (58 pdfa) wykazuje conjecture 3 z powyzszego!:
https://doi.org/10.1016/0168-0072(93)90044-E
no i Godel encoding jest wazny, bo jego dowod 1 twierdzenia o niezupelnosci
to tak naprawde interpreter!


ważne: Cook and Urquhart's theory IPV
przykłady rozszerzeń arytmetyki:
https://en.wikipedia.org/wiki/Conservative_extension

Complexity of Presburger Arithmetic:
https://www.cs.ox.ac.uk/people/christoph.haase/home/publication/haa-18/haa-18.pdf

Skolem arithmetic = Peano arithmetic without addition.
It is decidable - for any sentence in the language, it is decidable
if it is provable from the axioms. The complexity is 3EXP
https://en.wikipedia.org/wiki/Skolem_arithmetic

hierarchia arytmetyk
https://en.wikipedia.org/wiki/Ordinal_analysis

Should your specification language be typed?
https://lamport.azurewebsites.net/pubs/lamport-types.pdf

Weak systems of arithmetic:
https://golem.ph.utexas.edu/category/2011/10/weak_systems_of_arithmetic.html

IΔ₀ and linear time hierarchy!
Elementary Function Arithmetic = EFA
Primitive Recursive Arithmetic = PRA
RCA0*
IDelta0 + Exp

Primitive recursion:
https://ftp.cs.ru.nl/CSI/CompMath.Found/week9.pdf

A constructive proof of the Gödel-Rosser incompleteness theorem has been completed using the Coq proof assistant
http://r6.ca/Goedel/goedel1.html


Redukcje w Coq różne:  jest tutaj Ackermann function, PRA
https://github.com/rocq-community/hydra-battles


Definicje e.g. arytmetyki Q Robinsona:
file:///home/maryjane/Downloads/1235421930-2.pdf

Coding of sets and sequences, strona 31 pdfa (295):
file:///home/maryjane/Downloads/1235421934.pdf
Książka:
https://projecteuclid.org/eBooks/perspectives-in-logic/Metamathematics-of-First-Order-Arithmetic/toc/pl/1235421926


Funkcja jest dowodliwa w PA wtedy i tylko wtedy gdy rośnie wystarczająco wolno!
https://math.stackexchange.com/questions/4859305/are-there-examples-of-statements-not-provable-in-pa-that-do-not-require-fast-gro?rq=1
Czyli funkcje, które są niedowodliwe, a rosną wolno (np. są 0/1), nie mogą być wyrażalne!

https://mathoverflow.net/questions/382179/what-can-i-delta-0-prove

Euler's phi function in IDelta0:
https://link.springer.com/article/10.1007/BF01375521


czym jest transfinite induction w ERA, PRA, PA:
https://mathoverflow.net/questions/123713/era-pra-pa-transfinite-induction-and-equivalences?rq=1






https://smlfamily.github.io/Basis/array.html#SIG:ARRAY.foldri:VAL
https://www.cs.princeton.edu/~appel/smlnj/basis/array.html
https://www.cs.princeton.edu/~appel/smlnj/basis/aggregates-chapter.html#array-vector-slice
https://smlfamily.github.io/Basis/vector.html#SIG:VECTOR.mapi:VAL
https://github.com/spamegg1/unix-sml
https://cakeml.org/
