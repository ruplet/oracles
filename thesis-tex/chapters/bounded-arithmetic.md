# Reverse mathematics and bounded arithmetics

 connection with descriptive: chapter IV.1 of the book by Cook and Nguyen [@Cook_Nguyen_2010] 
If we can limit mathematics to not use axiom of choice (and study what we can and cannot prove after the restriction), why
not limit computer science to not use full recursion? 

In 1985 Sam Buss PhD thesis was released [@buss1985bounded] introducing Bounded arithmetic.

Very good book released in 2010b by Stephen Cook: [https://www.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf](https://www.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf). 

Good text from July 2025: [https://eccc.weizmann.ac.il/report/2025/086/](https://eccc.weizmann.ac.il/report/2025/086/).

Plase take a look at the following characterization of AC^0 functions:

Corollary V.5.2 ($\Sigma^1_1$-Definability Theorem for $V_0$)
A function is in \textbf{FAC}$^{0}$ if and only if it is $\Sigma_1^1$-definable in $V_0$, which is also equivalent to being $\Sigma_1^B$-definable in $V_0$, and further equivalent to being $\Sigma_0^B$-definable in $V_0$.

$$f \in \mathsf{FAC}^0 \iff f \text{ is } \Sigma^1_1\text{-definable in } V_0 \iff f \text{ is } \Sigma^B_1\text{-definable in } V_0 \iff f \text{ is } \Sigma^B_0\text{-definable in } V_0.$$

This is all based on characterizations of the similar form.

My work on formalizing bounded arithmetic is here: [https://github.com/ruplet/formalization-of-bounded-arithmetic](https://github.com/ruplet/formalization-of-bounded-arithmetic) - in this repo there is also my presentation from AITP, the abstract and the reviews it received.

This is also the subject of my visit at INRIA, beginning 8th September 2025.
