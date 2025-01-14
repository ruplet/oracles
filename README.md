# Oracle-oriented programming: a proof of concept


notatki z Neergaarda:
lemat:
jesli dla kazdej wartosci y, g(x:y) zwraca to samo,
oraz dla kazdego y, f(b, x: y) zwraca to samo,
to rekurencja f(n, x: y) dla kazdego y zwraca to samo.

analogiczny lemat dla zlozenia funkcji

jesli nie uzywamy cond(:y, ., .), to wynik ''nie wymaga
rozpakowywania y''

dla ustalonej funkcji f i argumentu x, ksztalt drzewa obliczen f(x : y)
moze zalezec co najwyzej od jednego bitu y:
jesli bedziemy testowac bit 0 y, to testujemy tylko parzystosc y
jesli bedziemy testowac bit 1 y, to musimy najpierw uciąć na siłe bit 0,
 zatem wynik dla [], [1], MSB[100]LSB, [101], [1001], [1000], [1100], [1101] beda takie same
 oraz dla [10], [11], [110], [111], [1010], [1011], [1110], [1111]

przechodzimy od argumentu y drzewo obliczen. na sciezce znajda sie jakies wierzcholki
p, jakies pi, jakies s i jakies cond. po wierzcholku cond, bity y nie przezywaja,
ale rezultat bedzie zalezec od jakiegos y_i, gdzie i to dokladnie liczba wierzcholkow p,
ktore ''usmiercily'' ktorys bit y (tj. nie byly poprzedzone jakims S).

drzewo obliczen: rozpatrujemy osobno wszystkie bity argumentow, zaczynamy od wierzcholkow
$x_^{(1)}_1 x^{(1)}_2, ..., x^{(n)}_1, ..., y^{(m)}_k$

na pozycjach bezpiecznych bedzie zawsze tylko podzbior oryginalnych y i stale.
liczba tych stalych moze zalezec od argumentu normalnego.




wazny paper w kwestii przegladu literatury:
https://link.springer.com/article/10.1007/BF01202288#preview
Function-algebraic characterizations of log and polylog parallel time



extract OCaml to Javascript:
https://melange.re/v4.0.0/
this is how they did it here:
(formalization of regex matching)
https://arxiv.org/pdf/2403.11919

znalazlem gdzie jest zdefiniowana ekstrakcja coqa.
jest tutaj:
https://github.com/coq/coq/blob/master/plugins/extraction/common.ml

to sie nie wydaje bardzo duzym zadaniem zeby zamienic ekstrakcje ocamla na ekstrakcje jsa

Najważniejsza rzecz:
Heraud, Nowak sformalizowali algebrę BC ale na bitstringach i w Coq!
https://inria.hal.science/hal-00654217/file/itp2011-arxiv.pdf




open problem: an implicit characterization of parimonious reductions


Damiano mazza:
Simple Parsimonious Types and Logarithmic Space
https://drops.dagstuhl.de/storage/00lipics/lipics-vol041-csl2015/LIPIcs.CSL.2015.24/LIPIcs.CSL.2015.24.pdf

Najwazniejsi badacze:
Isabel Oitavem
Ugo Dal Lago

kolejna characteryzacja FPTIME, NC:
Implicit characterizations of FPTIME and NC revisited

Two function algebras defining functions in NC^k
 boolean circuits

Current todo:
- present the history of the problem
- list all the papers I've read, including BibTeX references and mirrors

do Tourlakis (dowod na to ze Cobham = PTIME):
 H. E. Rose. Subrecursion: Functions and Hierarchies. Oxford University Press, 1984.


mój plan: zapoczątkować program, a nie tylko zaliczyć pracę magisterską
coś jak OEIS, ale dla programów komputerowych
zjawisko obserwowalne na LeetCode to powoływanie się na inne zadania po numerach
indeks problemów z różnych stron z zadaniami algorytmicznymi

fajna konferencja
https://popl20.sigplan.org/track/POPL-2020-tutorialfest#program

make a language for AC0-reductions and NC0:
> It is known, however, that AC0 reductions define a strictly smaller class than polynomial-time reductions (https://en.wikipedia.org/wiki/NP-completeness#Completeness_under_different_types_of_reduction)
make language for FO-reductions to consider P-complete problems
make language for L-reductions to consider NP-complete problems

write existing NP-reductions in my own language for LOGSPACE :)


- z tego co rozumiem, teoria typów jest logiką. jeśli dodamy do niej odpowiednik
   typu niedeterministycznego, np. monady List, to dla logiki wyrażającej uprzednio
   języki regularne, nic nie powinno się zmienić (DFA = NFA), ale dla logiki
   wyrażającej języki bezkontekstowe, siła wyrazu powinna się zwiększyć (DPDA < PDA)



TODO jak na teraz:
znaleźć istniejące formalizacje maszyn turinga w Coq i/lub innych weryfikatorach.
Być może formalizacja Cobhama nie będzie konieczna - być może istnieje inne,
zweryfikowane sformułowanie teorii wyrażającej dokładnie PTIME i pokazanie jej
równoważności do prawdziwych maszyn turinga.

   
- What is the most natural X-complete problem?
> We consider weaker and weaker reductions, and check
> which problems can still be reduced to other in the class.  
> The most natural problem is the one, to which we can reduce all other problems
> under the weakest reductions

pytanie: czy jedynym typem w jezyku programowania moze byc int?
to by otwieralo droge do po prostu primitive recursion,
hierarchii grzegorczyka i latwej skladni

jak silna jest potrzebna logika by stwierdzić spójność / sprzeczność zestawu aksjomatów?
czy syntax musi być drzewem?
teoria typów metajęzyka
najsłabszy syntax, który wyrazi wszystkie poprawne programy innego języka
taki syntax jest w stanie rozwiązać problem HALT dla rozważanego języka!!
szukamy takiego metajęzyka, żeby problem stopu podjęzyka był łatwy.

# About these files:
- book.md: Pandoc-style Markdown file, containing all the theory behind the
project.

## Pandoc command
pandoc -o output.md book.md -f markdown -t gfm --bibliography references.bib --filter pandoc-citeproc --csl apa.csl

## Citation style
apa
source:
https://github.com/citation-style-language/styles/blob/master/apa.csl
