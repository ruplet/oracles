# Implicit Computational Complexity

## What is Implicit Computational Complexity?
Implicit Computational Complexity (ICC) is a research direction that seeks to capture complexity classes through programming language restrictions, without explicitly referring to machine models or resource bounds. Instead of measuring time or space after the fact, ICC designs languages and recursion schemes whose syntactic rules guarantee that every definable function lies within a target class - such as polynomial time or logarithmic space - while still being expressive enough to cover all functions in that class. This approach promises a principled foundation for programming languages that “build in” complexity guarantees by design. It utilizes techniques and results from mathematical logic: proof theory, recursion theory, linear logic.

ICC is often viewed as the **proof-theoretic analogue** of descriptive complexity. While descriptive complexity uses model-theoretic tools to classify decision problems based on their logical definability, ICC approaches computational complexity from within the syntax of programming languages and type systems.

## History of the field
The field started with consecutive results from 1991 by Leivant [@151625] and from 1992 by Bellantoni and Cook [@10.1007/BF01201998] who first provided implicit characterizations of polytime-computable functions.

Results existed before that, e.g.  
- Immerman in 1987 characterized [@doi:10.1137/0216051] polytime *relations* in a way that doesn't involve any explicit size bounds in the defining expressions.  
- Compton and LaFlamme in 1990 [@COMPTON1990241] characterized uniform $\text{NC}^1$. Allen in 1991 [@ALLEN19911] characterized uniform $\text{NC}$. Their works were unsatisfactory due to relying on explicit polynomial bounds, more or less hidden in the definitions. Moreover, they have also only considered *relations* or *decisive* complexity classes (e.g. $\text{PTIME}$) and not *functions* computable in these complexities ($\text{FPTIME}$). But e.g. the exponential relation  $E(x, y) \iff y = 2^x$ is polytime to decide.  
- There has been some related work on characterizations of polytime functions, e.g. of Gurevich from 1983 [@4568079], and the foundational work by Cobham from 1964 [@Cobham1964-COBTIC], but their approaches still contained explicit polynomial bounds in some form, more or less hidden in the definition.  

For a better literature review of the origins of this area, please see [@bloch1994function]

Since 1990's, an abundance of complexity classes have been characterized implicitly, most important of them have been characterized in a variety of ways, see e.g. [@NIGGL201047] for an overview of characterizations of $\text{FPTIME}$ and $\text{FNC}$, or [@10.1016/j.ic.2015.12.009] for two different function algebras capturing the $\text{NC}^k$ hierarchy.

More importantly for us, in 1999 Neil D. Jones published how fragments of the Lisp language correspond to L and P *decisive* complexity classes [@JONES1999151]. Bonfante in 2006, expanding on Jones' work, published his characterizations of the same two classes [@10.1007/11784180_8]. Kristiansen and Voda in 2005 [@kristiansenvoda2005] study an imperative and a functional programming language, fragments of which induce hierarchies of complexity classes, with well-known complexity classes such as LOGSPACE, LINSPACE, P, PSPACE (also: decisive) occuring in the hierarchies. Other characterizations include works of Kristiansen [@kristiansen2005neat], Oitavem [@Oitavem+2010+355+362] and many more.

As the most important classes for the scope of this thesis are FPTIME and FLOGSPACE, we devote separate sections for their characterizations.

A good introduction to Implicit Computational Complexity is there:
Simone Martini's presentation: part 1 [@martini2006implicit1], part 2 [@martini2006implicit2] and part 3 [@martini2006implicit3]. Also, Simona Ronchi Della Rocca's presentation from 2019: [@ronchi2019logic] and 
Ugo Dal Lago's Short Introduction to ICC from 2012 [@DalLago2012].

### Classes (conjectured) impossible to be captured syntactically
Some of the studied complexity classes remain notoriously difficult to be characterized implicitly. 
The classes for which a characterization exists are called 'syntactic' complexity classes, as opposed to 'semantic'
complexity classes, for which such characterization is conjectured to not exist.

#### BPP
One example is BPP,
a characterization of which was however studied in [@lago2012higherordercharacterizationprobabilisticpolynomial].
Despite that, PP has been characterized implicitly by Dal Lago in 2021: $\text{PP}$ [@dallago_et_al:LIPIcs.MFCS.2021.35].

#### PTIME on unordered structures
But more importantly, the class `inv-P` of graph permutation-invariant problems decidable in polynomial time, is conjectured
to not be characterizable this way. This is a restatement of the problem of finding a "logic capturing PTIME on unordered structures".
A good discussion of this problem is present in Anuj Dawar's presentation from 2012: [@dawar2012syntactic].





## Bellantoni and Cook's safe recursion for FP and FL
- Arguments are split into **normal** (left of “;”) and **safe** (right of “;”): $f(x; a)$.
- We formulate the result using computation on non-negative integers, but the same proof carries over to computation on binary strings.

### Definition of $\mathcal B$
$\mathcal B$ is the smallest class of functions containing the initial functions (1.–5.) and closed under (6.–7.).

1. **Constant**: $0$ (a zero-ary function).
2. **Projections** (for $n,m \ge 0$, $1 \le j \le n+m$):
   $$
   \pi^{n,m}_j(x_1,\dots,x_n;\,x_{n+1},\dots,x_{n+m}) \;=\; x_j.
   $$
3. **Successors** (append a bit; $i\in\{0,1\}$):
   $$
   s_i(\,; a) \;=\; 2a + i \quad(\text{i.e. } a \mapsto ai).
   $$
4. **Predecessor** (delete last bit):
   $$
   p(\,; 0) = 0,\qquad p(\,; ai) = a \quad(i\in\{0,1\}).
   $$
5. **Conditional on last bit**:
   $$
   C(\,; a,b,c) \;=\;
   \begin{cases}
     b & \text{if } a \bmod 2 = 0,\\
     c & \text{otherwise.}
   \end{cases}
   $$

**Closure principles**
6. **Predicative Recursion on Notation (PRN).**  
   Given $g,h_0,h_1 \in \mathcal B$, define $f$ by, for $i\in\{0,1\}$,
   $$
   f(0, x;\, a) \;=\; g(x;\, a),\qquad
   f(yi, x;\, a) \;=\; h_i\!\big(y, x;\, a,\, f(y, x;\, a)\big).
   $$

7. **Safe Composition (SC).**  
   Given $h,r,t \in \mathcal B$, define $f$ by
   $$
   f(x;\, a) \;=\; h\!\big(r(x;\, );\, t(x;\, a)\big).
   $$
   Here $r$ produces the normal inputs for $h$ using only the normal data $x$; $t$ produces the safe inputs for $h$ and may depend on both $x$ and $a$.

### Characterization of polytime
- The polynomial-time functions are exactly those functions in $\mathcal B$ whose signature has only normal inputs (i.e., no safe inputs).











## Neergaard’s $BC\text{-}\varepsilon$ (definition and intuition)

### Setup
- Numbers are strings over $\{0,1\}$: $N_2$ (binary); we also mention $N_1$ (unary). The empty string $\varepsilon$ denotes $0$.
- Bitstrings are written $b_k \cdots b_1$ with $b_k$ the most significant bit; the length function is $|\cdot|$.
- Arguments are **split** into **normal** and **safe** parts, written with a colon “$:$”: $f(x_1,\dots,x_m : y_1,\dots,y_n)$.
- **Affine (linear) use of safe arguments**: each safe variable may be used **at most once**.
- Recursion is allowed **only over normal arguments**.

### Definition of $BC\text{-}\varepsilon$
$BC\text{-}\varepsilon$ is the **least** set of functions over $N_2$ containing the **base functions** (1) and **closed** under (2) safe affine composition and (3) safe affine course-of-value recursion.

#### (1) Base functions (over $N_2$)
- Constant: $0(:) = \varepsilon$.
- Predecessor on notation: $p(:\,\varepsilon)=\varepsilon$, and $p(:\, yb)=y$ for $b\in\{0,1\}$.
- Projections: for $1\le j\le m+n$,
  $$
  \pi^{m,n}_j(x_1,\dots,x_m : x_{m+1},\dots,x_{m+n}) = x_j.
  $$
- Successors on notation (append a bit): $s_0(:\,y)=y0$, $s_1(:\,y)=y1$.
- Conditional on last bit (bit-test): $c(:\, y1,\, y_2,\, y_3)=y_2$ and $c(:\, y,\, y_2,\, y_3)=y_3$ otherwise (i.e., pick $y_2$ iff the first argument ends with bit $1$).

#### (2) Safe affine composition
Let
- $f : N_2^{M,N} \to N_2$ (i.e., $M$ normal and $N$ safe inputs),
- $g_1,\dots,g_M : N_2^{m,0} \to N_2$ (produce the **normal** inputs for $f$ using only normal data),
- $h_1 : N_2^{m,n_1}\to N_2,\dots,h_N : N_2^{m,n_N}\to N_2$ with $n\ge n_1+\cdots+n_N$ (consume disjoint bundles of safe variables).

Define, for $x=(x_1,\dots,x_m)$ and $(y_1,\dots,y_n)$ **partitioned** into $\mathbf y^{\,1},\dots,\mathbf y^{\,N}$ so that **each** $y_i$ appears **in at most one** $\mathbf y^{\,j}$:
$$
\bigl(f \circ \langle g_1,\dots,g_M : h_1,\dots,h_N \rangle\bigr)(x_1,\dots,x_m : y_1,\dots,y_n)
\;=\;
f\bigl(g_1(x:),\dots,g_M(x:) : h_1(x:\mathbf y^{\,1}),\dots,h_N(x:\mathbf y^{\,N})\bigr).
$$

#### (3) Safe affine course-of-value recursion
Given
- $g : N_2^{m,n} \to N_2$,
- $h_0,h_1 : N_2^{m+1,1} \to N_2$,
- $d_0,d_1 : N_2^{m+1,0} \to N_2$,

define $f = \mathrm{rec}(g,h_0,\delta_0,h_1,\delta_1) : N_2^{m+1,n} \to N_2$ by
$$
f(n, x : y) \;=\;
\begin{cases}
g(x : y), & \text{if } n=\varepsilon,\\[4pt]
h_{b_1}\!\bigl(b_k\cdots b_2,\, x : f(b_k\cdots b_2 + \delta,\, x : y)\bigr),
& \text{if } n=b_k\cdots b_2 b_1 \text{ with } k\ge 1,
\end{cases}
$$
where $\delta = \bigl|\, d_{b_1}(b_k\cdots b_2, x : ) \,\bigr|$ (the **length** of the offset term), and the safe argument discipline is **affine** (each safe input used at most once).

#### (4) Closure
$BC\text{-}\varepsilon$ is closed under (2) and (3).

### Notation
- If $f$ is nullary (a constant), we write $f$ also for $f\circ\langle : \rangle$ in any arity context.
- Symmetric recursion shorthand: $\mathrm{rec}(g,h,\delta)$ abbreviates $\mathrm{rec}(g,h,\delta,h,\delta)$.

### Intuition
- **Affine safety**: safe inputs are **read-once** (no duplication), preventing uncontrolled growth; normal inputs control recursion.
- **Safe affine composition**: normal arguments of $f$ are computed **only** from normal data; safe data may influence only safe positions, and each safe variable flows to **at most one** consumer.
- **Course-of-value**: recursion over the full binary notation of $n$ can consult “earlier values” via the $d_b$-computed **length offsets**, yet the result of recursion is fed back **only in safe position** and **linearly**, preserving low space bounds.
- **Relation to Bellantoni–Cook $b$**: dropping **affinity** (allowing duplication of safe data) and using the non-affine recursion variant yields the original $b$-algebra.














Lind 1973 [@10.1145/1008293.1008295], 1974 [@lind1974logspace] : function algebra, explicit resource bounds
function algebra with unary numbers (only for small-output logspace functions) [@10.1007/BF01201998]
tail recursive readonly programs [@JONES1999151]

Murawski and Ong in 2000 introduce BCminus [@murawski2000can], [@MURAWSKI2004197].
in 2004 moller-neergaard prove bce- = fl

Martin Hoffman presented an overview of languages for LOGSPACE in 2006: [@hofmann2006logspace]. 

history of logspace: [@schoepp2006spaceefficiency]

- I have obtained the code from the author, refurbished it (ported from Moscow ML to SML/NJ) and found a second, unpublished paper that clarifies a lot in the original paper
- code for Neergaard is there: https://github.com/ruplet/neergaard-logspace-characterization
- for Neergaard, I also have a proof that the function `shiftR` from his published paper is not implementable (typo, need to reverse arguments). The proof is already in `thesis-tex/main.tex`, not copying it here

- we have just a tiny bit of Haskell code written by me to define Neergaard's language and re-write the function proposed in his paper into working, formal implementations in this folder (app/ subdirectory) 


```hs
identity :: Func
identity = Proj 1 0 1

oneNormalToZero :: Func
oneNormalToZero =
  let g = ZeroFunc in
  let h = Proj 1 1 2 in
  let d = identity in
  Recursion 0 0 g h h d d

-- Proposition 1. Let m and n by numbers in binary. Right shift shiftR(m : n) of
-- m by |n| and selection of bit |n| from m are definable in BCe-.

-- shiftR(n : m) = m >> |n|
shiftR :: Func
shiftR =
  let g = Proj 0 1 1 in
  let d = oneNormalToZero in
  -- h(timer : recursive) = tail(recursive)
  let h = Composition 0 1 1 [1] Tail [] [Proj 1 1 2] in
  Recursion 0 1 g h h d d
```


## Linear logic

also was used for logspace, e.g. for characterization of logspace-computable predicates, a variant of propositional linear logic called "parsimonious logic" was introduced in [@mazza:LIPIcs.CSL.2015.24].

- we have an interpreter and examples for the programming language invented by Ugo dal Lago and Ulrich Schopp (based on linear logic) there: https://github.com/uelis/IntML


Ulrich Schöpp introduces **LogFPL**, a typed functional programming language designed to capture the complexity class **LOGSPACE**. [@10.1007/11874683_40]

In 2013, Dal Lago and Schopp introduce IntML : [@DALLAGO2016150], https://github.com/uelis/IntML

In a major milestone for ICC, Dal Lago and Schöpp introduce **IntML**, a functional programming language with a linear type system that characterizes the class **FLOGSPACE**—the class of logarithmic-space *functions*, not just decision problems.

Unlike many prior systems that characterize LOGSPACE in terms of predicates or decision properties, IntML provides a full **function-level** model. Its type system, based on linear logic, ensures that only logarithmic-space computable functions can be expressed.