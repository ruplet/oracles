# oracles
Proof of concept: Oracle-Oriented Programming

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

