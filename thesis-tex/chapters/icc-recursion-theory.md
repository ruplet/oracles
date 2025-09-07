# Recursion-theoretical approach to Implicit Computational Complexity {#icc-recursion-theory}

This is based on Bellantoni and Cook characterization
of PTIME ([https://www.cs.toronto.edu/~sacook/homepage/ptime.pdf](https://www.cs.toronto.edu/~sacook/homepage/ptime.pdf)) and on further work by Neergaard to characterize FLOGSPACE in a similar way.


## Bellantoni and Cook's safe recursion for $\mathsf{FP}$ and $\mathsf{FL}$

Bellantoni and Cook introduced a function algebra $\mathcal B$ whose key idea is to separate arguments into two classes:

- normal inputs (written to the left of the semicolon)  
- safe inputs (written to the right of the semicolon)

We write a function as $f(\vec{x}; \vec{a})$, where $\vec{x}$ are normal inputs and $\vec{a}$ are safe inputs.  

Intuitively:  
- Normal inputs control recursion depth.  
- Safe inputs can be passed around but recursion depth cannot depend on them.  
- This should guarantee that recursion does not produce more than polynomial growth.

For an integer $x$, $|x|$ denotes the binary length $\lceil \log_2(x+1) \rceil$. For a vector $\vec{x}=(x_1,\dots,x_n)$, we write $|\vec{x}| = (|x_1|,\dots,|x_n|)$ and we write  $\vec{f(\vec{x})} = (f_1(\vec{x}),\dots,f_m(\vec{x}))$.

The computation considered here is on non-negative integers, but proof of equivalence to PTIME carries to binary strings.

---

### Definition of $\mathcal B$

$\mathcal B$ is the smallest class of functions containing the following initial functions (1–5) and closed under the closure principles (6–7).

1. Constant  
   Zero (a nullary function):  
   $$
   0.
   $$

2. Projections  
   For $n,m \ge 0$ and $1 \le j \le n+m$:  
   $$
   \pi^{n,m}_j(x_1,\dots,x_n;\,x_{n+1},\dots,x_{n+m}) \;=\; x_j.
   $$

3. Successors  
   Append a bit, for $i\in\{0,1\}$:  
   $$
   s_i(\,;a) \;=\; 2a+i \quad (\text{i.e. } a \mapsto ai).
   $$

4. Predecessor  
   Delete the last bit:  
   $$
   p(\,;0) = 0, \qquad p(\,; ai) = a \quad (i\in\{0,1\}).
   $$

5. Conditional on last bit  
   $$
   C(\,;a,b,c) \;=\;
   \begin{cases}
     b & \text{if } a \bmod 2 = 0, \\
     c & \text{otherwise.}
   \end{cases}
   $$

---

### Closure principles

6. Predicative Recursion on Notation (PRN)  
   Given $g,h_0,h_1 \in \mathcal B$, define $f$ by, for $i\in\{0,1\}$,
   $$
   \begin{aligned}
   f(0, \vec{x};\, \vec{a}) \;&=\; g(\vec{x};\, \vec{a}), \\
   f(y i, \vec{x};\, \vec{a}) \;&=\; h_i\!\big(y, \vec{x};\, \vec{a},\, f(y,\vec{x};\,\vec{a})\big),
   \end{aligned}
   $$
   where $y i$ denotes appending the bit $i$ to $y$.

   The recursive call $f(y,\vec{x};\vec{a})$ is passed into a safe argument position of $h_i$. This ensures the result cannot later be promoted to a normal input, preventing uncontrolled growth.

---

7. Safe Composition (SC)  
   Given $h,r,t \in \mathcal B$, define $f$ by
   $$
   f(\vec{x};\,\vec{a}) \;=\; h\!\big(r(\vec{x};\,);\, t(\vec{x};\,\vec{a})\big).
   $$

   Here $r$ produces the normal inputs for $h$ using only the normal data $\vec{x}$, while $t$ produces the safe inputs for $h$, which may depend on both $\vec{x}$ and $\vec{a}$.  

   The restriction is that safe arguments may not flow into normal positions. This enforces that recursion depth is bounded by the normal inputs, never by results of recursion.

---

### Intuition

Functions in $\mathcal B$ can perform arbitrary polynomial-time computations on their normal inputs. Operations on safe inputs are restricted so that they do not increase binary length by more than an additive constant. The asymmetry is crucial: adding a new function to $\mathcal B$ on safe inputs is strictly more powerful than adding it on normal inputs.  

The central idea is that recursive values always remain safe. Thus the depth of recursion cannot depend on the result of recursion itself. This “predicativity” ensures that all functions in $\mathcal B$ are computable in polynomial time, and conversely, every polynomial-time function can be defined in $\mathcal B$ using only normal arguments.



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

- I have obtained the code from the author, refurbished it (ported from Moscow ML to SML/NJ) and released it with a proper free license (matching with the license i have been given the code on). I have also found a second, unpublished paper that clarifies a lot in the original paper [^2]
- for Neergaard, I also have a proof that the function `shiftR` from his published paper is not implementable (typo, need to reverse arguments). The proof is already in `thesis-tex/main.tex`, not copying it here

- we have just a tiny bit of Haskell code written by me to define Neergaard's language and re-write the function proposed in his paper into working, formal implementations in this folder (app/ subdirectory) 

[^2]: [https://github.com/ruplet/neergaard-logspace-characterization](https://github.com/ruplet/neergaard-logspace-characterization)

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
