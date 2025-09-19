# Descriptive Complexity: An Overview

In descriptive complexity theory, an object (e.g. a set of graphs) in
a complexity class is specified as the set of all finite models of a given
formula. In this work, we only consider the case where the object is a language $L \subseteq \{0, 1\}^*$ and the model is a finite binary string.

The central problem of descriptive complexity is to characterize a complexity class by the power of logic required to *define its problems*. This is in contrast to Implicit Complexity Theory discussed later,
that seeks the weakest system sufficient to *implement algorithms* of the class, and in contrast to Bounded Arithmetic which, in turn, studies the weakest *theory* required to define a function *and prove its correctness*. This perspective has led to elegant characterizations of many traditional complexity classes in terms of logical languages. 

As an example, Grädel’s Theorem in descriptive complexity states that
NL is the class of finite models of the second-order Krom formulas\nobreakspace{}[@GRADEL199235].
Here, a Krom formula is a propositional
formula in conjunctive normal form where each clause contains at most
two literals. The Satisfiability Problem for Krom formulas, Krom-SAT, is
complete for co-NL (or equivalently NL, by the Immerman–Szelepcsényi
Theorem).

Similarly in\nobreakspace{}[@GRADEL199235], it is shown how second-order Horn formulas express precisely the properties decidable in polynomial time.
Here, first define a horn clause as a clause with at most one positive literal and any number of negative literals. Then a Horn formula is a propositional formula formed by conjunction of Horn clauses.
By a result independently proved by Immerman\nobreakspace{}[@IMMERMAN198686] and Vardi\nobreakspace{}[@10.1145/800070.802186], PTIME is also characterized by first-order logic with a least fixed-point operator (FO[LFP]). Similar results exist for most of commonly studied complexity classes: NP (Fagin's theorem), co-NP, PH, PSPACE, EXPTIME.

<!-- Under reasonable assumption [^1] -->
<!-- [^1]: presence of successor relation; in our case this means that for two objects of the model (i.e. two positions `x`, `y` of the input word) we can test if `y` is the right neighbour of `x`. A weaker assumption is *orderedness* of the structure, where we can only test if `y` is somewhere to the right of `x`. -->

For a good introduction, see the self-contained classical reference by Immerman\nobreakspace{}[@Immerman1999-IMMDC].

## "Ordered" and "unordered" structures

Most of the results we discussed in this chapter considered passing the input as an ordered structure, i.e. for two positions `x` and `y` of the input word, we can test if `y` is to the right of `x`. Actually, many of these theorems have an additional assumption of presence of a successor relation --- allowing to test if `y` is *the* right neighbour of `x`.

In practice, computers operate on memory that is linearly ordered (via memory addresses), meaning that the assumption of ordered structures is both natural and realistic. However, this assumption is *crucial*: without an explicit ordering, FO[LFP] does **not** capture PTIME\nobreakspace{}[@Cai1992]. The existence of a logic that characterizes PTIME on *unordered* structures remains a major open problem in computer science as of 2025.

Fagin's theorem says that existential second-order logic characterizes NP. It's worth to notice that this theorem does not assume order on the input --- intuitively, NP is strong enough to "guess" the order relation.

## Descriptive Complexity and Type Systems
After investigating systems within descriptive complexity, we explored whether their logical frameworks could be combined with type-theoretic approaches to design programming languages that capture complexity classes. While this attempt to bridge descriptive complexity and type systems was conceptually motivated, the two fields remain quite far apart in practice, and we were not successful in fully integrating them. Nonetheless, this line of inquiry led us to a broader investigation of type systems that enforce resource bounds --- particularly those inspired by linear logic and implicit computational complexity. The results of this exploration are presented in (TODO: the next chapter).

## $\text{FO} = \text{AC}^0$ and how will we define $\text{FAC}^0$
Due to their declarative nature, results from Descriptive Complexity don't directly help us design programming languages.
However, one result from this field will be important for us in (Chapter: bounded arithmetic). There we will study
a logical system characterizing $\text{FAC}^0$: a class of reductions (functions) that is very weak, but strong enough to define very interesting computations.
The definition of $\text{FAC}^0$ will be based on a logical characterization of $\text{AC}^0$.  

A foundational result in the field of descriptive complexity theory is that $\text{FO}~=~\text{AC}^0$,
i.e. relations describable by a first-order sentence are precisely relations decidable by $\text{AC}^0$ circuits\nobreakspace{}(Corollary 5.32,\nobreakspace{}[@Immerman1999-IMMDC])[^1] [^2].

This characterization will be used in (Definition V.2.3, [@Cook_Nguyen_2010]) to define *functions* in $\text{FAC}^0$ $ as functions of polynomially-bounded length of output, whose *bit-graphs* are in $\text{AC}^0$. That's how we will switch to studying functional complexity classes.

# References
[^1]: under "reasonable assumptions" which here are that: FO formulas have access to order relation on input structure and to basic arithmetical predicates including $+, \times$; $\text{AC}^0$ is FO-uniform; all structures considered are ordered and have at least 2 elements (so that $0$ and $1$ are unequal). For more details, please see Proviso 1.14 and Proviso 1.15 of\nobreakspace{}[@Immerman1999-IMMDC]. Theorems 1.36, 1.37 in\nobreakspace{}[@Immerman1999-IMMDC] (FO without bit characterizes star-free regular languages; monadic SO without bit characterizes regular languages) and the remark after them is also of use to motivate adding arithmetical symbols to FO. Definitions of the symbols mentioned are in Section 1.2 of\nobreakspace{}[@Immerman1999-IMMDC]. We should think of the operations $+, \times$ added to FO as operations on unary numbers, not on binary representations; the former are trivial to implement as binary circuits in $\text{AC}^0$, while existence of the latter is a theorem.
[^2]: Part of Corollary 5.32 that is interesting for us refers to Theorem 5.22 saying that $\text{FO}[t(n)] = \text{AC}[t(n)]$ for all polynomially-bounded and FO-constructible $t(n)$. $FO[t(n)]$ is defined in Definition 4.24 as formulas with a quantifier block iterated $t(n)$ times. $\text{AC}[t(n)]$ is defined in Definition 5.17 as FO-uniform circuits of depth $O(t(n))$. For our purposes, $t(n)$ is just 1, circuits have depth $O(1)$ and $\text{AC}[t(n)]$ is just \text{AC}^0$.

<!-- IMPORTANT: what is bit? what is <=, +, -.
section 1.2 of immerman
bit(i, 0) holds iff i is odd.
PLUS(i, j, k) meaning i + j = k
2. TIMES(i, j, k) meaning i x j = k
3. BIT(i, j) meaning bit j in the binary representation of i is  -->

<!-- this PLUS, TIMES seems to be like operations on unary numbers. This is unary numbers because we can only do it up until `n` (because we only have forall x, PLUS(x), PLUS(0), PLUS(1), PLUS(max),...) -->