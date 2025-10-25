pytanie: czy jedynym typem w jezyku programowania moze byc int?
to by otwieralo droge do po prostu primitive recursion,
hierarchii grzegorczyka i latwej skladni


- Digression: why do we assume that proofs have a tree structure?
> Cirquent calculus is a proof calculus that manipulates graph-style constructs termed cirquents, as opposed to the traditional tree-style objects such as formulas or sequents.

- what is the weakest representation of solvable Sudoku?

- Digression:
> conversion of MSO to NFA is non-elementary, but NFA to MSO is linear-time  
> what are the best data representations?  
> what about languages over the unary alphabet?  
> are there np-hard languages over the unary alphabet?  
> can the only data type in the language be {1^n: n in Nat}?  
> it seems natural that the data type for computers is { {0,1}^n: n in Nat},  
> but for set-theory based mathematics, it's Set = Empty | {Set},  
> where {} stands for... a set. So like a list, but with no order and no duplicates

- Digression:
> Second-order logic is hard, because it requires processing very complicated sets. Maybe it'd be easier if these complicated sets were given by their "generators"?

- Digression:
> when data on input is in a convenient form, a reduction is in L, but if it the input is just represented as a natural number (because every countable sequence can be numbered), no efficient algorithm exists (try proving that the algorithm would probably have to 'unpack' the structure, i.e. construct the actual structure, which it is unable to because of the memory limit)

- Homotopy Type Theory should eat itself (but so far, it’s too big to swallow); related to the limitations of the expressibility of the metalanguage:
> https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/

jak silna jest potrzebna logika by stwierdzić spójność / sprzeczność zestawu aksjomatów?
czy syntax musi być drzewem?
teoria typów metajęzyka
najsłabszy syntax, który wyrazi wszystkie poprawne programy innego języka
taki syntax jest w stanie rozwiązać problem HALT dla rozważanego języka!!
szukamy takiego metajęzyka, żeby problem stopu podjęzyka był łatwy.

10. czemu chcemy koniecznie żeby syntax był CFG? 




# Implementing the interpreter 
- first problem: do our syntax really describe a tree?
- why does all of logic and proof theory look like just talking about trees?
- why is every proof a tree
- maybe not every? recent progress: Geometry of Interaction
- In proof theory, the Geometry of Interaction (GoI) was introduced by Jean-Yves Girard shortly after his work on linear logic. In linear logic, proofs can be seen as various kinds of networks as opposed to the flat tree structures of sequent calculus.
- so can syntax not be a tree?
- hint: first-order logic is compositional. does that mean that fundamentally
  it's theorems are described by a tree?

# Relation between the language and the metalanguage {.allowframebreaks}
- this is something which I don't understand
- how strong should be the metalanguage to ,,interpret'' the language considered?
- if the syntax of the language is naturally represented by a tree, we might need
  to have a tree type in the metalanguage
- strength of the type system of the metalanguage is tightly connected with
  our chosen representation of data structures used in the language
- e.g. if the language considered operates on graphs, we can pass the graph
  as an adjacency matrix, adjacency list or even a circuit which inputs a 
  node number encoded in binary and outputs its neighbors numbers as a bitmask
- what's the relation between automatas on trees to automatas on flat representations of trees (such as normal automata)
- what's the internal ,,difficulty'' of a programming language, e.g. what is the
  simplest description of computational processes modeled by the programming languages
  and the simplest interpreter, which can take this description and execute the process?

ANSWER: best syntax is such that correctness of its parsing can be proven in 
the weakest logic / weakest arithmetic!

