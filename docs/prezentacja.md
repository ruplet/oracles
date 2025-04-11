---
title:
- Implicit (or not) characterizations of complexity classes
author:
- Paweł Balawender
date:
- April 10, 2025
# pandoc -t beamer prezentacja.md -o prezentacja.pdf --bibliography references.bib --citeproc  -M link-citations=true -V colortheme:crane -V theme:CambridgeUS --csl apa.csl
# pdftk A=inria-curryhoward.pdf B=prezentacja.pdf cat B1-7 A8-15 output out.pdf
---

# Capturing a complexity class
>- Suppose you want to have a programming language, in which every program is guaranteed
  to terminate in time polynomial w.r.t. the number of bits of input

# Idea 1: only ```for i=1..n``` loops
>- This is well studied. This is primitive recursion. You will not express Ackermann's function.
>- This is not PTIME-complete
>- It's difficult(?) to guess whether you'll be able to implement your PTIME program in it.
>- Theoretically, every function growing slow enough, will be expressible. What's the deal
   with the halting function though? I think it depends on the specification of the input/output

# Idea 2: C programs + a bounding polynomial
>- This is extensively complete and sound
>- This becomes semantic (like BPP); you cannot(?) tell for a given (program, polynomial)
   what the output will be (whether it'd finish in time).

# Idea 3: Grzegorczyk hierarchy

# Idea 4: Cobham's algebra (1965) @[]

# Functional Logspace @[Neergaard2004AFL]


# The power of different provers
>- Crucial criterion: if you took the logic of a specific prover, could you prove your theorem in this logic?
>- If your theorem prover is based on intuitionistic logic, you might not prove a classical theorem
>- Specifically: in Lean, you will not prove that for every predicate $P$, $P \lor \lnot P$ holds.
>- (Lean is expressive enough to understand the second-order sentence $\forall P. P \lor \lnot P$ and take is as an axiom, so you can use it without proving)
>- Beware: these logics are not simple!

# Let's consider a game
>- Consider the set of all infinite sequences of natural numbers, $\mathbb{N}^\mathbb{N}$, and a subset $A \subseteq \mathbb{N}^\mathbb{N}$, which we call the winning set.
>- Alice and Bob alternately pick natural numbers $n_0, n_1, n_2, ...$. Alice is the first one to pick.
>- That generates a sequence $\langle n_i \rangle_{i \in \mathbb{N}}$. Alice wins iff the generated sequence belongs to $A$, the set of winning sequences.

# When Alice can win?
>- If the winning set is finite, then the set of elements $B_1$ that Bob should choose in his first turn is also finite. So Bob can choose any number from $\mathbb{N} - B_1$ and the rest of the game doesn't matter - Alice loses.
>- In this proof, we need to be able to:
>- Define natural numbers $\mathbb{N}$
>- Define an infinite, ordered sequence of numbers
>- Define a set of sequences, the winning set
>- Define taking the second element of a sequence
>- Define a set $B_1$ of second elements
>- Prove that $\mathbb{N} - B_1$ is not empty
>- Prove that for any suffix, Bob's sequence won't be winning

# Language and logic of set theory
>- The language consists of:
>- A countably-infinite amount of variables $x_1, x_2, ...$ used for representing sets
>- Logical symbols $\lnot, \land, \lor, \forall, \exists, =, \in, ()$

# Set theory as a graph
![alt text](image-3.png){ width=80% }

# ZFC: Zermelo-Fraenkel axioms of set theory + choice (1922)
>- Empty set (?)
>- Sum Set
>- Power Set
>- Infinity
>- Unordered Pair

. . .

>- Extensionality
>- Regularity

. . .

>- Specification (Comprehension)
>- Replacement (*)
>- Choice (**)

# Axiom of the Sum Set (Union)
Given a collection of sets (which is itself a set), we can form a new set containing all the elements that belong to at least one set in the collection.
$\forall X \exists Y \forall u(u \in Y \iff \exists z(z \in X \land u \in z))$

# Axiom of the Power Set
For any set, we can form a new set that contains all possible subsets of the original set.
$\forall X \exists Y \forall u(u \in Y \iff u \subseteq X)$

# Axiom of Infinity
This axiom postulates the existence of at least one set with infinitely many elements. A common example is the set of natural numbers (or a set that can be put into one-to-one correspondence with it).
$\exists S [\emptyset \in S \land (\forall x \in S) [x \cup \{x\} \in S]]$

# Axiom of the Unordered Pair
Given any two sets, we can form a new set containing precisely those two sets.
$\forall a \forall b \exists c \forall x(x \in c \iff (x = a \lor x = b))$

# Axiom of Extensionality
Two sets are equal if and only if they contain exactly the same members.
$\forall u(u \in X \iff u \in Y) \implies X = Y$

# Axiom of Foundation (Regularity)
This axiom prevents the existence of infinite descending chains of set membership; every nonempty set has an $\in$-minimal element.
$\forall S [S \neq \emptyset \implies (\exists x \in S) [S \cap x = \emptyset]]$

# Axiom of Specification (Separation / Comprehension)
>- We can form a subset of an existing set consisting of all elements that satisfy a given property. Note that we can only take a subset and not form arbitrary sets - the latter leads to Russel's paradox.
>- $\forall X \forall p \exists Y \forall u(u \in Y \iff (u \in X \land \phi(u,p)))$

# Axiom of Replacement
>- If F is a function, then for any X there exists a set $\{F(x):x \in X\}$
>- $\forall p (\forall x \forall y \forall z [\phi(x,y,p) \land \phi(x,z,p) \implies y = z]) \implies (\forall X \exists Y \forall y [y \in Y \iff (\exists x \in X) \phi(x,y,p)])$

# Axiom of Choice
>- Given any family of non-empty sets, there exists a **function** which selects precisely one element from every member of the family
>- $\forall x \in a \exists y A(x,y) \implies \exists f \forall x \in a A(x, f(x))$

# {N, P(N), P(P(N)), ...}
>- This set is not definable in Zermelo set theory, i.e. ZF without the axiom schema of replacement!
>- Will we not run into troubles while proving statements about more complicated winning sets in our game?

# Gale-Stewart game
>- A Gale-Stewart game is a game like above. For simplicity, say that Alice and Bob choose elements from $\{0, 1\}$, so that they construct a sequence from $\{0, 1\}^\omega$. Denote the winning set as $P \subseteq \{0, 1\}^\omega$.
>- Discrete topology on $\{0, 1\}$: the topology where every subset is open.
>- $\{0, 1\}^\omega$: an infinite product of topological spaces. What is the topology? On the next slide!
>- When we say 'open game', 'closed game', 'Borel game' we only consider e.g. openness of $P$ in $\{0, 1\}^\omega$ with the product topology

<!-- # Box topology
- The topology on $\prod_{\alpha \in J} X_\alpha$ with basis $\prod_{\alpha \in J} U_\alpha$, where each $U_\alpha$ is open in $X_\alpha$. -->

# Product topology
>- The topology on $\prod_{\alpha \in J} X_\alpha$ with basis $\prod_{\alpha \in J} U_\alpha$, where each $U_\alpha$ is open in $X_\alpha$ and all but finitely many $U_\alpha = X_\alpha$.
>- Any open set in this topology can be expressed as a union of some family of elements from the basis
>- Intuitively, an open set in the product topology is such that it only specifies a finite number of conditions on coordinates
<!-- >- The key difference is that the box topology allows infinitely many factors in the basis element to be proper open subsets, while the product topology requires all but finitely many to be the entire space. -->

# Intuition
<!-- >- In an open game, if Player I is going to win, they will win after a finite number of moves. There will be a point in the game where, no matter what Player II does afterwards, the resulting infinite play will be in Player I's winning set. Player I's victory becomes guaranteed at some finite stage. -->
>- In a closed game, if Player II is going to win (meaning the play will *not* be in Player I's winning set $P$), they will win after a finite number of moves. There will be a point in the game where, no matter what Player I does afterwards, the resulting infinite play will *not* be in Player I's winning set. Player II's victory (Player I's loss) becomes guaranteed at some finite stage.
>- If Player II doesn't win after any finite number of steps, then necessarily, Player I wins.
<!-- >- TODO: In formal verification, such conditions are called 'safety' conditions. -->

# Is the game determined when the winning set is closed? (Gale-Stewart)
>- Consider a game where Player I wins if the play is in $P$, for $P$ closed.
>- If Player II has a winning strategy, the game is determined.
>- Assume Player II does not have a winning strategy. We will show Player I has one.
>- A position $p = (a_0, a_1, ..., a_{2n-1}) \in \{0, 1\}^*$ (with I to play next) is "not losing for I" if Player II does not have a winning strategy from that position.
>- I.e. II has no winning strategy in the game on $P|_p$, where $P|_p = p^{-1} P = \{y \mid py \in P\}$. So $\varphi$ is not losing for I.

# Crucial observation
>- Suppose position $p = (a_0, ..., a_{2n-1})$ is not losing for Player I
>- It means that Player I has at least one move $a_{2n}$ such that for any possible response $a_{2n+1}$ by Player II (resulting in the position $pa_{2n}a_{2n+1}$), the new position $pa_{2n}a_{2n+1}$ is also not losing for Player I.
>- If for every possible move $a_{2n}$ by Player I, there existed a response $a_{2n+1}$ by Player II leading to a position from which Player I loses, then the initial position $p$ would be losing for Player I, which contradicts our assumption.

# Player I's Strategy Construction
>- Player I starts by choosing $a_0$ such that for all $a_1$, the position $(a_0, a_1)$ is not losing for Player I.
>- II then plays some $a_1$. I responds with $a_2$ such that for all responses $a_3$, $(a_0, a_1, a_2, a_3)$ is not losing for I, **etc.**

# Remark: neighbourhoods
>- Suppose $(a_n) = (a_0, a_1, ...) \in W$, for $W$ open.
>- Then there exists a neighbourhood $N$ around $(a_n)$, contained in $W$ -- a neighbourhood contained in the winning set is just a node in the game tree such that the whole subtree is winning for Alice.
>- There is a $k$ such that $(a_0, ... , a_{2k-1}) * \{0,1\}^\omega \subseteq W$

# Winning Argument for Player I
>- We claim this strategy is winning for Player I.
>- Consider a run $(a_0, a_1, ...)$ of the game in which Player I followed the strategy.
>- Then, forall $n$, $(a_0, ... a_{2n-1})$ is not losing for Player I.
>- Since $P$ is closed, $P^c$ is open in $\{0, 1\}^\omega$.
>- Suppose that $(a_0, ...) \notin P$.
>- Then there exists $k$ such that the neighborhood $(a_0, ..., a_{2k-1})\{0, 1\}^\omega \subseteq P^c$.

# Winning Argument for Player I
>- But this means that any suffix after $(a_0, ..., a_{2k-1})$ leads to winning, i.e. Player II has a trivial winning strategy!
>- So Player I loses from this position.
>- This contradicts the fact that $p$ was chosen by Player I such that for any next move by Player II, the resulting position is "not losing for Player I".
>- Therefore, the assumption that $(a_0, ...) \notin P$ must be false
>- So Player I wins.

<!-- 
# Remarks on Axiom of Choice (from Kechris)

>- Theorem 20.1 (Determinacy of Open/Closed Games) generally requires the **Axiom of Choice** due to the single-valuedness condition in the definition of a strategy. A strategy specifies a unique move for each possible history. -->

# Remark: how to define more sets?
>- An idea: Borel sets!
>- First, take all the open sets and say they are all Borel.
>- Take any two Borel sets $A, B$. Their relative complement $B \setminus A$ is also Borel.
>- Take any countably many sets $A_i$. Their union and intersection is also Borel.
>- Iterate these operations transfinitely. The result is the **Borel $\sigma$-algebra**.

# Is the game determined when the winning set is Borel?
>- This is much more difficult, took many years and intermediate results to go from open/closed determinacy to Borel determinacy
>- Harvey Friedman showed that determinacy for Gale-Stewart games where the winning set is only Borel, is not provable in ZF without the axiom schema of replacement!
>- But will we be able to prove it in Lean 4?

# Lean 4: hierarchy of universes
>- In Lean, every object lives at one of (more than) three levels
>- There are the two universes Type and Prop at the top
>- There are the types and the theorem statements one level below them
>- Then there are the terms and the theorem proofs at the bottom. 
>- The type of all real numbers $\mathbb{R}$ is a type, so $\mathbb{R}$ lives at the middle level, and real numbers like 7 are terms; we write $7 : \mathbb{R}$ to indicate that 7 is a real number.

# ZFC version used in Lean 4: infinite hierarchy of universes
>- `Type` is the type of (small) types.
>- it leads to paradoxes to set the type of `Type` to be also `Type`
>- the type of `Type` is `Type 1`, etc.

# Lean 4: inductive types
Type of binary trees over a type $a$ in universe $u$:
```lean4
inductive Tree. {u} (a : Type u) : Type u
  | nil : Tree a
  | node : a → Tree a → Tree a → Tree a
```

# ZFC version used in Lean 4: pre-sets
A pre-set is a set without an equality relation. Type of a **pre-set** over a Lean type $a$ lives in a universe of a higher level. Function $A$ is the embedding of objects of type $a$ into pre-sets, i.e. if we want to have a pre-set of `Nat` objects, we need the type `Nat` in Lean and we need a way to represent objects $n : Nat$ as pre-sets:
```lean4
inductive PSet : Type (u + 1)
  | mk (a : Type u) (A : a → PSet) : PSet

def empty_pset : PSet :=
  PSet.mk Empty (fun x : Empty => nomatch x)
```

# ZFC version used in Lean 4: sets as pre-set quotients
>- Define extensional equivalence on pre-sets
>- Define ZFC sets by quotienting pre-sets by this equivalence.
>- Lean's type theory is said to be equiconsistent to ZFC + "there are countably many inaccessible cardinals" (Mario Carneiro)

<!-- # ZFC version used in Lean 4: classes
Define classes as sets of ZFC sets. Then the rest is usual set theory.
```lean4
def Class :=
  Set ZFSet
``` -->


# Modeling ZFC in Coq
>- There are a few projects, but no uniform way to work with ZFC in Coq
>- I honestly don't know the details. You define that a ZFC-set is a Type, then define some properties. Coq has no quotient types by default, unlike Lean. It is very very subtle
<!-- >- In the HoTT book, there is a whole section on ZFC. Requires in-depth HoTT knowledge, so also category theory and algebraic topology. -->


# Theory of Mizar: Tarski-Grothendieck set theory
>- Mizar: a Polish theorem prover. In 2009 its mathlib was the biggest body of formalized maths in the world!
>- the underlying theory of Mizar is precisely first-order logic with Tarski-Grothendieck set theory
>- ZFC + Tarski's axiom, which implies existence of inaccessible cardinals
>- enough to define category theory, in contrast to ZFC
>- if you were to formalize that ALL games are determined, Mizar would certainly not be your best assistant: using the Axiom of Choice, you can construct a not determined winning set! (see end remark)

# A formalization of Borel determinacy in Lean
>- Sven Manthe published his paper and the complete formalization the proof of Borel determinacy on 5th February 2025.
>- The formalization has been done in Lean 4.
>- The project comprises of about 5000 lines of code [here, show specific code]
>- [...] stronger forms of determinacy,
like analytic determinacy, are not provable in Lean without additional axioms (unless Lean is inconsistent).
>- https://www.arxiv.org/pdf/2502.03432

# Remark: Construct non-determined game using Axiom of Choice
>- Remember: Hamming distance of two binary words is the number of positions they differ at
>- Using Axiom of Choice, we can construct an infinite XOR function $f: \{0, 1\}^\omega \rightarrow \{0, 1\}$ such that if HammingDistance$(w_1, w_2)=1$, then $f(w_1) \neq f(w_2)$.
>- Theorem: No player has a winning strategy in an infinite Gale-Stewart game $G_f$ where the winning set $P$ is such that $(a_n) \in P$ iff . Proof: strategy stealing (Niwiński, Kopczyński: A simple indeterminate infinite game, 2012)
>- https://www.mimuw.edu.pl/~niwinski/Prace/ed.pdf

# Alexander Grothendieck (1928-2014)
![alt text](image.png)
<!-- >- algebraic geometry
>- synthesis between geoalg and number theory
>- synthesis between geoalg and topology
>- Grothendieck universes
>- introduced topoi to category theory
>- worked with Teichmuller, whose idea I showed in my last presentation; Grothendieck-Teichmuller group -->

# Grothendieck, 1970
![alt text](image-1.png)

# Grothendieck, Lasserre, France, 2013
![alt text](image-2.png)


<!-- # References {.allowframebreaks} -->

