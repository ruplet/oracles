# oracles
Proof of concept: Oracle-Oriented Programming

https://web.archive.org/web/20240611105719/https://inicjatywadoskonalosci.uw.edu.pl/dzialania/iii-2-2/ios/

# How to design a programming language?
In the senior year of your Bachelor's studies in Computer Science at the University of Warsaw (MIMUW), you're asked to write an interpreter for a programming language (ideally invented by yourself). But you're never really taught how to actually design a programming language. Here I want to share with you the rabbit hole I have fallen into, trying to answer the question:

what features are worth adding to a programming language?


## Motywacja ZSM
Temat projektu: Praktyczne języki programowania wyrażające klasy złożoności obliczeniowej
O programie komputerowym mówimy że jest poprawny, gdy kończy się i zwraca poprawny wynik. Rzadko chcemy pisać programy, które nie terminują, a jeśli już – to zazwyczaj ich nieterminacja wynika z nieskończonej wielkości wejścia (np. serwer obsługujący w nieskończoność kolejne żądania klientów). Popularniejszym zadaniem jest konieczność wykazania, że dany program komputerowy faktycznie się kończy, a jeszcze popularniejszym – że kończy się ,,szybko’’, tj. jego czas wykonania jest jakąś funkcją wielkości wejścia. Dowody tego, że dany program ma konkretną złożoność obliczeniową, często są trudne nie tylko do wymyślenia, ale również do prześledzenia. W wielu przypadkach dowodzący może ułatwić czytelnikowi zadanie zapisując swój program w taki sposób, że ze składni wyraźniej widać złożoność. Przykładowo, często pierwszą rzeczą, na którą patrzymy w kodzie jest maksymalne zagnieżdżenie i zakresy pętli w programie. Jeśli są to dwie zagnieżdżone pętle od 1 do n, to często przyjmujemy wstępnie, że program wykonuje kwadratowo dużo operacji. Co jednak jeśli piszący program podstępnie modyfikuje zmienną n w ciele pętli? Albo nie zwiększa indeksu pętli o 1, a na przykład go podwaja? Problemem nie są tutaj piszący programy, a to że popularne języki programowania często pozwalają na ,,zbyt dużo’’.
Celem badań będzie projektowanie takich języków programowania, w których przyzwoite ograniczenia górne na złożoność obliczeniową będą własnością syntaktyczną programu, a nie semantyczną. Poprzez szereg restrykcji nakładanych na programy akceptowane przez kompilator, język będzie tak ograniczać możliwości programisty, by niemożliwe było napisanie programu, który zużywa zbyt dużo zasobów – czasu procesora (przy ograniczaniu złożoności czasowej) lub pamięci operacyjnej (przy ograniczaniu złożoności pamięciowej). Główną trudnością projektu jest znalezienie takich konstrukcji językowych i sposobów iteracji, przy których język ciągle będzie użyteczny – w szczególności, chcemy by język działał na stosownym poziomie abstrakcji i mógł wykorzystywać przydatne struktury danych takie jak tablice, a nie tylko liczby naturalne.
Projektowanie systemu typów będzie elementem pracy nad projektem, ale nie powinno stanowić jego głównego problemu. Możliwe że koncept złożoności obliczeniowej trzeba będzie zintegrować z systemem typów języka. Potencjalnym rozwiązaniem jest zaimplementowanie sposobów iteracji jako funkcje z efektami ubocznymi (np. zamiast pętli for i = 1 to n , funkcja map o efekcie ubocznym LINTIME oznaczającym że obliczenie wykona się w czasie liniowym) i zastosowanie takich technik jak monady lub efekty algebraiczne, by zaimplementować to w systemie typów. Możliwe jednak, że język będzie użyteczny i bez tego.
Korzyścią jaką przyniesie projekt będzie to, że powszechnie znane programy o znanej złożoności wymagającej analizy, będzie można przedstawić w tym języku, uzyskując certyfikat na to, że dany kod istotnie spełnia zadane własności, bez konieczności ,,wierzenia’’ w osobno sporządzony dowód. Zadaniem autora, jak również bardzo silną metryką postępu w projekcie, będzie implementowanie w tym języku znanych algorytmów. Przykładem algorytmu, który autor będzie próbował w ten sposób zaimplementować, jest algorytm Knutha-Morrisa-Pratta, którego złożoność obliczeniowa zazwyczaj wymaga dłuższej argumentacji. Na potrzeby spełnienia tego celu będzie potrzebne zaprojektowanie języka, który wyraża klasę złożoności czasowej DTIME(n), oraz przerobienie znanych już implementacji tego algorytmu w taki sposób, by dało się je w nim zapisać.
W grupie ,,znanych algorytmów’’, które warto będzie implementować jako programy testowe będą również, znane z teorii złożoności obliczeniowej, redukcje między problemami obliczeniowymi. Przykładowo, popularnym zadaniem dla studentów informatyki jest wskazanie tzw. ,,L-redukcji’’ między problemami, czyli programu, który pokazuje że jeden problem można rozwiązać znając rozwiązanie innego, a transformacja wejścia zajmuje tylko logarytmicznie dużo pamięci. Popularne języki programowania nie dostarczają metod iteracji, które pozwalają w ,,bezpieczny’’ sposób pisać takie programy – zazwyczaj potrzeby jest osobny dowód, że dany program nie przekroczy logarytmicznej pamięci. Częścią projektu będzie rozwiązanie tego problemu i zaprojektowanie języka programowania, który wyraża klasę L (LOGSPACE).
Argumentem za sukcesem projektu jest to, że teoretyczne prace wprowadzające takie języki już istnieją. Dziedzina implicit complexity theory zajmuje się m.in. tymi zagadnieniami i dostarcza szereg narzędzi i gotowych rozwiązań, które prawdopodobnie będzie można wprost zaimplementować, by szybko dostarczyć prototypową wersję projektu. W szczególności, znane są autorowi prace, które bezpośrednio wskazują ograniczenia na język programowania C, które sprawiają że wtedy wyraża on klasy złożoności LOGSPACE lub LINSPACE.
Wątpliwości może budzić np. trudność problemu znalezienia logiki wyrażającej PTIME. Jest to jeden z najważniejszych otwartych problemów w informatyce i mało prawdopodobnym jest, by badania autora uczyniły w nim postęp. Nie jest to jednak argumentem przeciwko szansie sukcesu projektu, ponieważ badania będą dotyczyć tylko obliczeń wykonywanych na komputerze – co oznacza, że dane do algorytmów będą ,,uporządkowane’’, a otwarty problem logiki dla PTIME dotyczy danych bez zadanego porządku.
W ramach badań publikowany będzie na bieżąco kod źródłowy środowiska wykonawczego. Ponadto publikowane będą artykuły popularnonaukowe wprowadzające w temat i autorskie implementacje znanych algorytmów, a także podsumowania i demonstracje istniejących prac teoretycznych, które podają języki programowania lub logiki wyrażające klasy złożoności.


# Introduction

We say that a computer program is *correct* with respect to a specification if it terminates and returns the
specified result. Specification of a computer program can range from a simple and (relatively) informal
LeetCode problem description to the complex and detailed ISO C++ standard.
However, the concept of termination is a more straightforward property:
the program simply has to terminate for every input. While almost every major programming language
features a variety of solutions (most importantly, type systems) to help programmers write code matching with
the specification, little progress has been made on possible syntactic restrictions which could help
us analyze the time required for a program to run. In this work, we will focus on a stronger notion
of the time-complexity of a program which, roughly speaking, not only can tell us that
a program terminates, but gives us specific bounds on how quickly will it terminate with
respect to the size of the input. Brilliant algorithms often have to be accompanied
by a separate formal proof that they indeed are contained in a particular complexity class.





# The below is for archive purposes only

Turing machines are too strong. We practically cannot reason about them in general, due to the implications of Rice's theorem.

No perfect programming language exists - as no perfect natural language exists. Different tribes have short words for frequently used things.

Things in real life are typed in the sense of natural languages - you can ,,eat a sandwich'', but you wouldn't say you ,,breathe a sandwich''; even though at the end of the day, it's all just atoms, untyped. Same with programming languages - even though in the end it all compiles to untyped assembly language instructions, at a higher level we operate in a typed world. We need types in our language, as also we need a way to describe objects and their transformations.

The data and the functions are not something we create. It's something we discover or merely describe. We describe data using a logic (e.g. first order logic). Thus we can describe infinite data like
V("start node"), V("end node"), E("start node", "end node")
Forall n: Nat, V(n), E(n, n+1)

We want to strenghten our type theory to have more Theorems for free
We want to weaken our type theory to be able to compute more


Objects of our language are graphs.
A ,,type'' is a model of a logical sentence
i.e. a ,,type'' is described exactly by a logical sentence

FO: can talk about vertices, edges
MSO1: can talk about vertices, edges, sets of vertices
MSO2: can talk about vertices, edges, sets of vertices and edges

equality is graph isomorphism

Trakhtenbrot's theorem: it is undecidable whether FO sentence
  can be realized by a finite undirected graph

What is in

# Krytyka Cobhama

w tym paperze Cobhama nic nie ma!
co więcej, nie jest on normalnie dostępny. to jest link do skanu:
https://web.archive.org/web/20240121142633/https://www.cs.toronto.edu/~sacook/homepage/cobham_intrinsic.pdf

i w nim widać że nic tam nie ma ciekawego. denerwuje mnie to że
ludzie się powołują na tę pracę i zakładają że on tam cokolwiek
ciekawego zrobił, co jest nieprawdą.

to jest link, pod którym można obejrzeć review:
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/alan-cobham-the-intrinsic-computational-difficulty-of-functions-logic-methodology-and-philosophy-of-science-proceedings-of-the-1964-international-congress-edited-by-yehoshua-barhillel-studies-in-logic-and-the-foundations-of-mathematics-northholland-publishing-company-amsterdam-1965-pp-2430/475D96633FB147B7C78B1FCCE3A7B053?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark

i w tym review jest wprost napisane, że Cobham tylko rzuca hipotezę,
że ta jego algebra funkcji faktycznie wyraża PTIME.

pełne cytowanie:
@article{Cook_1970, title={Alan Cobham. The intrinsic computational difficulty of functions. Logic, methodology and philosophy of science, Proceedings of the 1964 International Congress, edited by Yehoshua Bar-Hillel, Studies in logic and the foundations of mathematics, North-Holland Publishing Company, Amsterdam 1965, pp. 24–30.}, volume={34}, DOI={10.2307/2270886}, number={4}, journal={The Journal of Symbolic Logic}, author={Cook, Stephen A.}, year={1970}, pages={657–657}} <div></div>

ta jego algebra to jest:
L = PTIME = the least class of functions including the eleven functions s_i(x) = 10x + i, i=0,1,...,9 and x^{l(y)} (where l(y) is the decimal length of y), and closed under the operations of explicit transformation, composition, and limited recursion on notation (digit-by-digit recursion).

Cobham nie ma dowodu że L = PTIME.

Dowód można znaleźć np. tutaj:
https://web.archive.org/web/20240103230629/http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf
na stronie 186 PDFa. (175 numeracji wewnetrznej)

Również, w Tourlakis 2022 (jest na libgenie)
George Tourlakis - Computability-Springer (2022).pdf
na stronie 625 pdfa (608 wewnetrznie),
jest nie tylko dowód (stronę wyżej), ale też
remark na temat tego twierdzenia, wraz ze wskaźnikiem na pracę Odifreddiego i inne dowody.


Ta praca z dowodem w Coq twierdzi, że w Tourlakis 1984, jest reformulation of Cobham's class
with bitstrings and the proof that it contains exactly PTIME functions

TODO jak na teraz:
znaleźć istniejące formalizacje maszyn turinga w Coq i/lub innych weryfikatorach.
Być może formalizacja Cobhama nie będzie konieczna - być może istnieje inne,
zweryfikowane sformułowanie teorii wyrażającej dokładnie PTIME i pokazanie jej
równoważności do prawdziwych maszyn turinga.

