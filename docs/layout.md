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

25. Język programowania to JEST system dowodowy.
Żeby do teorii dodac axiom schema of comprehension, trzeba do języka programowania dodać funkcję filter.
Żeby dodać indukcję, trzeba dodać rekurencję dla pewnych operacji.
To do czego język programowania się interpretuje, powinno w sumie MODELOWAĆ teorię np. V0:

jeśli mamy aksjomaty
x >= 0
x + (y + z) == (x + y) + z

to po prostu gwarantujemy że w "prawdziwym" życiu, do którego kompilujemy, one naprawdę zachodzą.
