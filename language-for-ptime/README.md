- Cobham paper

- PV logic

- Bellantoni and Cook introduced a safe-recursive characterization of FP
- I asked them to add a License to the repository (they did!)
- here is code which formalizes that Cobham algebra is the same as Bellantoni and Cook's on bitstrings (as opposed to natural numbers): 
https://github.com/davidnowak/bellantonicook
- in this subdir is also my code which just defines their algebra as inductive types

- linear logic is important in this field! add overview + ask Paupa

- discussion with Murawski about unaccessible paper about characterization of ptime:
> In your paper, you reference:
> 
> W.G. Handley, Bellantoni and Cook's characterization of polynomial time 
> with some related results, in: S. Wainer's Marktoberdorf'97 Technische 
> Universität München, Lecture Notes, 1997.
Pawle,

przepraszam za zwłokę w odpowiedzi. Dopiero teraz znalazłem czas, żeby przejrzeć stare rzeczy w pokoju. Niestety nie udało mi się znaleźć tej książeczki. Wyglądała tak samo jak ta na załączonym obrazku (niebieska broszurka, format A5).

Jest pewna szansa, że ktoś ma ją w gabinecie w Warszawie albo można ją namierzyć w bibliotece. Jeśli nie, to praca

https://link.springer.com/chapter/10.1007/978-3-642-58622-4_8

wydaje się zawierać podobne wyniki, ale nie wiem na pewno, bo nie mam do niej pełnego dostępu. Być może UW wykupiło dostęp?

Z pozdrowieniami,
Andrzej


Safe recursion dalej (light affine logic)
https://arxiv.org/pdf/1005.0522

- On Syntactic and Semantic Complexity Classes
> Anuj Dawar  
> University of Cambridge Computer Laboratory  
> Spitalfields Day, Isaac Newton Institute, 9 January 2012  
> https://www.newton.ac.uk/files/seminar/20120109163017301-152985.pdf  
> e.g. NP = ESO (Fagin 1974), so NP is syntactical  
> major open problem:  
> Does P admit a syntactic characterisation?  
> Can the class P be “built up from below” by finitely many operations?  
> If a complexity class C has a complete problem L, it is a syntactic class.  
> because we can enumerate all AC0 reductions  
> Two Possible Worlds:
> Either
> - there is no effective syntax for inv-P
> - there is no classification possible of polynomial-time graph problems
> - there is an inexhaustible supply of efficient algorithmic techniques to be discovered
> - P neq NP
> Or,
> - there is an effective syntax for inv-P
> - there is a P-complete graph problem under FO-reductions
> - all polynomial-time graph problems can be solved by easy variations of one algorithm.

- Leivant article: Ramified Recurrence and Computational Complexity I: Word Recurrence and Poly-time
> https://link.springer.com/chapter/10.1007/978-1-4612-2566-9_11#preview

- About semantic and syntactic complexity classes
> An interesting difference is that PR functions can be explicitly enumerated, whereas functions in R cannot be (since otherwise the halting problem would be decidable). In this sense, PR is a "syntactic" class whereas R is "semantic."  
> https://complexityzoo.net/Complexity_Zoo:P#pr

https://lipn.univ-paris13.fr/~moyen/walgo/papers/MS-Dice16.pdf
czyli nie ma jezyka dla P?
problem w reprezentacji:
mozemy miec jezyk programowania dla P, ale odkladamy nierozstrzygalnos do problemu sprawdzenia czy mozna przetlumaczyc dana maszyne turinga na ten jezyk

do Tourlakis (dowod na to ze Cobham = PTIME):
 H. E. Rose. Subrecursion: Functions and Hierarchies. Oxford University Press, 1984.

- Critique of Cobham's paper
> there is nothing in this paper, really  
> additionally, it's difficult to access:  
> https://web.archive.org/web/20240121142633/https://www.cs.toronto.edu/~sacook/homepage/cobham_intrinsic.pdf  
> here, you can see the review of the above, written by Cook  
> https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/alan-cobham-the-intrinsic-computational-difficulty-of-functions-logic-methodology-and-philosophy-of-science-proceedings-of-the-1964-international-congress-edited-by-yehoshua-barhillel-studies-in-logic-and-the-foundations-of-mathematics-northholland-publishing-company-amsterdam-1965-pp-2430/475D96633FB147B7C78B1FCCE3A7B053?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark  
> and in this review you can see that Cobham only hypothesises that his algebra expresses P  
> his algebra is:  
> L = PTIME = the least class of functions including the eleven functions s_i(x) = 10x + i, i=0,1,...,9 and x^{l(y)} (where l(y) is the decimal length of y), and closed under the operations of explicit transformation, composition, and limited recursion on notation (digit-by-digit recursion).  
> And he doesn't have the proof that his L (it's not logspace) is really equal to P.  
> Here is the proof of the above, though:  
> https://web.archive.org/web/20240103230629/http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf  
> it's page 186 of the PDF (175 in internal numeration)  
> also, in Tourlakis 2022 (accessible on libgen)  
> George Tourlakis - Computability-Springer (2022).pdf  
> on page 625 of the PDF (608 internally), there is a proof, but also a remark about  
> this theorem, with a reference to Odifreddi's work


- Niggl, Wunderlich 2010: Implicit characterizations of FPTIME and NC revisited
> Cob = FPTIME
> From a programming point of view, function algebras like Cob are not practically appealing because they cannot be used as
a construction kit: Whenever a recursion is performed, one is prompted with a proof that the computed function is bounded
by some function already constructed.
Building on work of Simmons [25] and Leivant [15,16], Bellantoni and Cook [4] were the first to give a purely functional
characterization of FPTIME that does away with the “explicit” reference to the growth rate of functions defined by (BRN) in
Cobham’s class. In fact, this “explicit” reference can be made “implicit” by ensuring the following principle (P-BC): Computed
values in recursions must not control other recursions (cf. [20,22]).
That principle led to the well-known function algebra BC [4] which actually can be used as a construction kit, since all
restrictions are of purely syntactical nature. 
> https://www.sciencedirect.com/science/article/pii/S1567832609000113

