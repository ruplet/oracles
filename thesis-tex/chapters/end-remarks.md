# Background of the project

This work grew out of two broader research questions:

## When should a feature be added to a programming language?  
For instance, if a language already has `while` loops, introducing `for` loops may just amount to syntactic sugar. But if the language only supports loops of the form `for i = 1 .. n` with constant `n`, then adding `while` loops may be the only way to enable non-terminating computation.  
A related - and in many ways more challenging - question concerns the required expressive power of the type system. Could a language remain practical with only integers and function types? With just integers, strings, and functions? Is a type system necessary at all?  
In the context of this thesis, for example, if functions in our language correspond to LOGSPACE functions, then by the closure of LOGSPACE under composition we are justified in adding composition and variable substitution as language features.

## Can a feature be safely added?  
Preserving semantic properties - such as guaranteed termination - while extending a language is often subtle and error-prone. This is particularly true in type systems, where even minor changes may lead to unsoundness, causing the type checker to validate ill-typed programs.  
In the setting of this thesis, the guiding question becomes: if we add a new feature as a primitive, will it still be the case that every program expresses a LOGSPACE algorithm?

While these questions are both deep and interesting, they fell outside the scope of this thesis and have not been considered further.

# References