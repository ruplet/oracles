why use descriptive complexity?
we can prove that a relation is in AC0 using this theorem:
22. importance of descriptive complexity: (https://eccc.weizmann.ac.il/resources/pdf/morioka.pdf)
Theorem 2.1. [BIS90, Imm99] A relation  is in  AC0 iff it is representable by an FO-sentence.



- One application of fixed point suffices to express any query expressible with several alternations of fixed point and negation.
> https://www.sciencedirect.com/science/article/pii/S0019995886800298?via%3Dihub

- About Grohe work on LFP and IFP + C
> - Gurevichm Shelah 1986: LFP = IFP (inflanationary fixed-point)  
> - Evenness is not definable in IFP (proof by Ehreneucht-Fraisse games)  
> - Cai, Furer, Immerman, 1992: There are polynomial-time decidable properties of graphs that are not definable in IFP + C (IFP + counting)  
> - Immerman and Lander 1989: IFP + C captures PTime on trees  
> - Grohe and Marino 1999: IFP + C captures PTime on any class of graphs of bounded treewidth  
> - Grohe 1998: IFP + C captures PTime on the class of planar graphs  
> - Grohe 2008: IFP + C captures PTime on the class of graphs that exclude K5 as a minor  
> Source: https://www.cl.cam.ac.uk/~ad260/talks/wollic-tutorial.pdf
> (Descriptive complexity and polynomial time, tutorial by Anuj Dawar on WoLLIC, Edinburgh 2008)


- Grohe 2012: (IFP + C: inflanationary FP + counting) (very cool work!)
> Let C be a class of graphs with at least one excluded minor. Then IFP+C captures PTIME on C.  
> https://dl.acm.org/doi/pdf/10.1145/2371656.2371662  
> IFP+C does not capture PTIME on the class of cubic graphs [Cai et al. 1992]

- A descriptive complexity approach to the linear time hierarchy
https://www.sciencedirect.com/science/article/pii/S0304397503001336

- Descriptive complexity theory:
  * FO + Transitive closure operator = NL, nondeterministic logarithmic space
  * FO + Least fixed point operator = P, polynomial deterministic time
  * Existential SO = NP
    
- Grädel's theorem: on the class of finite structures with a successor relation, the collection of polynomial-time decidable properties coincides with those expressible in the Horn-fragment of existential second-order logic
> https://cstheory.stackexchange.com/questions/869/is-there-a-logic-without-induction-that-captures-much-of-p?rq=1

