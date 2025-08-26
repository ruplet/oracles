While thinking about computational complexity, we need to ask ourselves the question: "what is our computational model?". While we are used to thinking about the computational complexity of algorithms executing on a Turing machine, the notions of complexity for lambda calculus are less standard and less commonly agreed on (beta-reduction is not everything, as the existence of lamping's algorithm show). Instead of thinking of an algorithm as a sequence of transitions of a Turing machine,
we can think about a sequence of union and intersection operations on sets, about sequence of operations in any other algebra or a deductive system. Here we explore what is the current state of knowledge when it comes to "which computational model is the most natural to study computational complexity?" - because maybe it happens that, similarly like RAM model is more appropritae than Turing machines, some other model is even more appropriate? We explore the notion of algorithm, hypothethical hypercomputation and of different foundations as mathematics as candidates for the computational model we'll target.

We revisit what is the best programming paradigm to
study complexity. turing machines are not useful anymore, we rather use ram model!
what should we really do the proofs in? we examine foundations of mathematics.
we propose that physics and philosophy should constitute the foundations, and
we should have a framework to easily switch between these. define hypercomputation,
halt oracles.


- Computing aspects of set theory, Erwin Engeler ETH Zurich
> https://people.math.ethz.ch/~engeler/computing_aspects.pdf

- About the computational content of set theory
https://terrytao.wordpress.com/2010/03/19/a-computational-perspective-on-set-theory/

- Can a specific graph theory be a foundations of mathematics?
> https://mathoverflow.net/q/397581

- Comparing set theory, type theory and category theory as foundations
> https://philosophy.stackexchange.com/questions/87027/set-theory-vs-type-theory-vs-category-theory

- What do we want a foundation to be?
> What do we want a foundation to do? Comparing set-theoretic, category-theoretic, and univalent approaches  
> https://sites.socsci.uci.edu/~pjmaddy/bio/What%20do%20we%20want%20-%20final

- About different theories for foundations of mathematics
> https://mathoverflow.net/questions/364228/are-categories-special-foundationally  
> https://mathoverflow.net/questions/8731/categorical-foundations-without-set-theory  
> https://mathoverflow.net/questions/360578/category-theory-and-set-theory-just-a-different-language-or-different-foundati  
> https://mathoverflow.net/questions/352298/could-groups-be-used-instead-of-sets-as-a-foundation-of-mathematics?noredirect=1&lq=1  
> https://mathoverflow.net/questions/24773/why-do-categorical-foundationalists-want-to-escape-set-theory  
> https://mathoverflow.net/questions/9269/category-of-categories-as-a-foundation-of-mathematics

- Physical aspects of the foundational model
> What is the physical nature of computation?  
> Church-Turing thesis only relates to N->N functions.  
> Turing machines operating on real numbers are hypercomputation  
> Malament-Hogarth spacetime; relativistic Turing machines, that can
> peek into the future
> https://plato.stanford.edu/entries/computation-physicalsystems/

yuri gurevich what is an algorithm?

Cytat ze skryptu jajo:
https://www.mimuw.edu.pl/~szymtor/jao/skrypt.pdf

Jego głównym celem było udowodnienie, że nie istnieje algorytm
stwierdzający, czy
dane zdanie matematyczne jest prawdziwe. Jest to słynny problem
nazywany Entscheidungsproblem, postawiony przez Davida Hilberta
w roku 1928. Problem został rozwiązany (negatywnie) niezależnie
przez Alonso Churcha i Alana Turinga w roku 1936. Żeby odpowie-
dzieć na to pytanie, wpierw należało podać matematyczną definicję
algorytmu. Definicja Turinga opierała się na maszynach Turinga
(podejście “imperatywne”), a Church wymyślił $\lambda$-rachunek (podejście
,,funkcyjne''). Natychmiast zauważono, że oba formalizmy są sobie
równoważne. Nieformalna ,,teza Churcha-Turinga'' mówi, że wszystkie
sensowne formalizacje pojęcia algorytmu są równoważne maszynom
Turinga czy $\lambda$-rachunkowi.

Teza Churcha-Turinga to nieformalne stwierdzenie mówiąace, że do-
wolna formalizacja intuicyjnego pojęcia algorytmicznej obliczalności
jest równowazne maszynom Turinga i $\lambda$-rachunkowi. Teza ta jest
współcześnie mocno ugruntowana faktem, że wszystkie matema-
tyczne modele komputerów [3] i języki programowania są – przy
nieograniczonych zasobach – równowazne maszynom Turinga. W
szczególności, rózne warianty maszyn Turinga – wielotaśmowe,
niedeterministyczne, z taśmą dwustronnie nieskończoną, z taśmą
dwuwymiarową, itd. – są sobie wszystkie równoważne.

[3]: To dotyczy takze modeli korzystających z efektów kwantowych, które,
choć trudne do zaimplementowania fizycznie, matematycznie są precyzyjnie
opisane i badane.

# How to design a programming language?
In the senior year of your Bachelor's studies in Computer Science at the University of Warsaw (MIMUW), you're asked to write an interpreter for a programming language (ideally invented by yourself). But you're never really taught how to actually design a programming language. Here I want to share with you the rabbit hole I have fallen into, trying to answer the question:

what features are worth adding to a programming language?


At the Annual Meeting of the Association for Symbolic Logic in 2000, a panel was organized titled ,,THE PROSPECTS FOR MATHEMATICAL LOGIC IN THE
TWENTY-FIRST CENTURY''.[@757d00a2-cc01-38d8-ac3b-ecd9b7df0a72] Richard A. Shore pointed out three, as he states, ,,certainly not original and probably pie-in-the-sky, problems'' for logics in computer science for the 21st century: [@buss2002prospects]
-  “Prove” the Church-Turing thesis by finding intuitively obvious or at
least clearly acceptable properties of computation that suffice to guarantee that any function so computed is recursive.
- What does physics have to say about computability (and provability
or logic)?
- Find, and argue conclusively for, a formal definition of algorithm
and the appropriate analog of the Church-Turing thesis.

Kilka uwag do tego:
1. matematyczna definicja algorytmu: [@10.1007/978-3-642-27660-6_3]
specifically: ,,In our opinion, the notion of algorithm cannot be rigorously defined in full
generality, at least for the time being.'' - because there are many types of algorithms: sequential (used from antiquity), parallel, interactive, quantum etc. The notion of an algorithm is expanding and it's unlikely we will be able to capture it.
but it is totally possible to give an axiomatic definition of sequential algorithms. in [@38f4ae44-9556-3cc6-af5a-4949b6479e76] it is used to derive the Church-Turing thesis from first principles. These principles are based on the following informal notions:
- Sequential Time. An algorithm determines a sequence of “computational”
states for each valid input. Specifically, the time is discrete. what if time is not a successor structure? i.e. we can travel back in time

The answers to these problems will be provided to us by physics and philosophy :)

Can we focus on turing machines only? Not really. There exist projects implementing hardware for evaluating lambda terms: Reduceron
https://www.cs.york.ac.uk/fp/reduceron/

Can we say that turing machines are in some way more natural to implement
than lambda calculus? not really. also, what about game semantics,
parallel execution etc.?


neither is better. but, keeping in mind that reduceron is very limited,
in this work we will begin with algorithms for turing machines


c++ compiler is turing complete :{ not so good.
we don't want the compiler we'll be writing to be turing complete!
we want it to at least terminate, since we only compile LOGSPACE programs.


@article{757d00a2-cc01-38d8-ac3b-ecd9b7df0a72,
 ISSN = {10798986},
 URL = {http://www.jstor.org/stable/421070},
 journal = {The Bulletin of Symbolic Logic},
 number = {3},
 pages = {361--396},
 publisher = {[Association for Symbolic Logic, Cambridge University Press]},
 title = {2000 Annual Meeting of the Association for Symbolic Logic},
 urldate = {2024-04-05},
 volume = {6},
 year = {2000}
}

@misc{buss2002prospects,
      title={The prospects for mathematical logic in the twenty-first century},
      author={Samuel R. Buss and Alexander S. Kechris and Anand Pillay and Richard A. Shore},
      year={2002},
      eprint={cs/0205003},
      archivePrefix={arXiv},
      primaryClass={cs.LO}
}


@InProceedings{10.1007/978-3-642-27660-6_3,
author="Gurevich, Yuri",
editor="Bielikov{\'a}, M{\'a}ria
and Friedrich, Gerhard
and Gottlob, Georg
and Katzenbeisser, Stefan
and Tur{\'a}n, Gy{\"o}rgy",
title="What Is an Algorithm?",
booktitle="SOFSEM 2012: Theory and Practice of Computer Science",
year="2012",
publisher="Springer Berlin Heidelberg",
address="Berlin, Heidelberg",
pages="31--42",
abstract="We attempt to put the title problem and the Church-Turing thesis into a proper perspective and to clarify some common misconceptions related to Turing's analysis of computation. We examine two approaches to the title problem, one well-known among philosophers and another among logicians.",
isbn="978-3-642-27660-6"
}

@article{38f4ae44-9556-3cc6-af5a-4949b6479e76,
 ISSN = {10798986},
 URL = {http://www.jstor.org/stable/20059987},
 abstract = {Church's Thesis asserts that the only numeric functions that can be calculated by effective means are the recursive ones, which are the same, extensionally, as the Turing-computable numeric functions. The Abstract State Machine Theorem states that every classical algorithm is behaviorally equivalent to an abstract state machine. This theorem presupposes three natural postulates about algorithmic computation. Here, we show that augmenting those postulates with an additional requirement regarding basic operations gives a natural axiomatization of computability and a proof of Church's Thesis, as Gödel and others suggested may be possible. In a similar way, but with a different set of basic operations, one can prove Turing's Thesis, characterizing the effective string functions, and--in particular--the effectively-computable functions on string representations of numbers.},
 author = {Nachum Dershowitz and Yuri Gurevich},
 journal = {The Bulletin of Symbolic Logic},
 number = {3},
 pages = {299--350},
 publisher = {[Association for Symbolic Logic, Cambridge University Press]},
 title = {A Natural Axiomatization of Computability and Proof of Church's Thesis},
 urldate = {2024-04-05},
 volume = {14},
 year = {2008}
}

