Logic for NC1:  
[https://deepblue.lib.umich.edu/bitstream/handle/2027.42/28501/0000298.pdf?sequence=1\&isAllowed=y](https://deepblue.lib.umich.edu/bitstream/handle/2027.42/28501/0000298.pdf?sequence=1&isAllowed=y)

Dlaczego reprezentacja wejscia ma znaczenie:  
Boolean formula evaluation is only complete for LOGSPACE if input formulae are represented as graphs  
(e.g., by the list of all edges plus gate types). It was however shown in \[2\] that the problem is complete for  
NC1 under AC0-reductions if input formulae are given by their natural string encoding.  
[https://arxiv.org/pdf/1212.6567](https://arxiv.org/pdf/1212.6567)

+ dlaczego reprezentacja ma znaczenie? bo jak to lista bitow, to struktura jest uporzadkowana. jak podajemy jakies pierdolone abstrakcyjne drzewo, to nie jest uporzadkowana i logika musi byc duzo mocniejsza zeby dalej rozwiazywac nasz problem\!

Definicja first-order redukcji:  
[https://link.springer.com/book/10.1007/3-540-28788-4](https://link.springer.com/book/10.1007/3-540-28788-4)  
rozdzial 12.3

Problem, dla ktorego moc redukcji ma znaczenie:  
[https://cstheory.stackexchange.com/a/18631](https://cstheory.stackexchange.com/a/18631)  
[https://www.cse.iitk.ac.in/users/manindra/isomorphism/puniform-ac0-iso.pdf](https://www.cse.iitk.ac.in/users/manindra/isomorphism/puniform-ac0-iso.pdf)

Pomysl: zakoduj obliczanie BC jako obwod (jeden ,konkretny). Pokaz ze ten obwod ma konkretne wlasciwosci i ze obliczanie SATa w nim nie ma szansy przejsc

Nie ma jezyka dla PTIME???? [https://link.springer.com/chapter/10.1007/978-3-030-22996-2\_19](https://link.springer.com/chapter/10.1007/978-3-030-22996-2_19)

Pomysl: pokaz ze rekursja nie zwieksza takiego niezmienika: dany bit bezpieczny nie jest przeliczany. no bo w rekurencji dopiero na samym dnie mozemy otworzyc argument bezpieczny. czyli rekurencja w pewnym sensie nie zmienia glebokosci obwodu?

Spoko przyklad kodowania NL subset NC2: po prostu zakoduj stconn jako matrix multiplicatoin jako problem NL-zupelny i to skompiluj do obwodu NC2: [http://www.cs.mun.ca/\~kol/courses/6743-f07/lec16.pdf](http://www.cs.mun.ca/~kol/courses/6743-f07/lec16.pdf) 

Kmina: pokaż że ewaluacja obliczenia w BC implikuje istnienie obwodu binarnego. Podaj upper bound na wielkość / głębokość takiego obwodu. Z istnienia lower boundu na wielkość tego obwodu z circuit complexity, znajdź sprzeczność.

1. Karchmer-Widgerson games and communication complexity lower bounds  
2. Circuit depth lower bounds and P-completeness of Circuit Value Problem  
3. relation between these two \+ TFNP: [https://arxiv.org/pdf/2202.08909](https://arxiv.org/pdf/2202.08909)   
4. Every monotone circuit for USTCONN has depth Ω(log^2(n)): Karchmer-Wigderson (1990), this implies superpolynomial (n^(Omega(log n))) lower bound on the size of any monotone formula for st-conn of undirected graphs. 2004, Reingold: USTCONN is in L. You receive as input the adjacency matrix of an undirected graph with two distinguished vertices s and t. Is there a path from s to t?

*No deterministic Turing machine accepts SAT in time ![{n^{c}}][image1] and space ![{o(n)}][image2] where ![{c \\le \\lambda .}][image3]*  
[https://rjlipton.com/2009/04/13/sat-is-not-too-easy/](https://rjlipton.com/2009/04/13/sat-is-not-too-easy/)  
Lambda \= 1.7

[https://www.cs.princeton.edu/courses/archive/spr06/cos522/circuits.pdf](https://www.cs.princeton.edu/courses/archive/spr06/cos522/circuits.pdf)   
We believe that NP does not have polynomial-sized circuits. We’ve  
seen that if true, this implies that NP 6 \= P. In the 1970s and 1980s, many  
researchers came to believe that the route to resolving P versus NP should  
go via circuit lowerbounds, since circuits seem easier to reason about than  
Turing machines. The success in this endeavor was mixed.  
Progress on general circuits has been almost nonexistent: a lowerbound  
of n is trivial for any function that depends on all its input bits. We are  
unable to prove even a superlinear circuit lowerbound for any NP problem—  
the best we can do after years of effort is 4.5n − o(n).

Napisać posta na academia stackexchange

SPOTKANIE Z UGO DAL LAGO  
Notatki ze spotkania z prof Parysem:

- 1\. z drewa ewaluacji neergaarda mozmey miec upper bound na wielkosc obwodu  
- 2\. z lower boundu na obwod wynika silny lower bound na czas wykonania, przez to ze zeby zrobic ifa w wierzcholku (obliczyc bramke and/or), musimy obliczac coraz tp wieksze poddrzewa

Monotone depth lower bounds  
For function in NP  
Pitassi, Robere ’17: [http://www.cs.utoronto.ca/\~toni/Papers/rp-stoc17.pdf](http://www.cs.utoronto.ca/~toni/Papers/rp-stoc17.pdf)

Dzięki za slajdy \- bardzo fajna prezentacja. Faktycznie jesliby sie udalo przetlumaczyc lower-boundy z teorii obwodow na jezyk algebry neergaarda to byloby dla mnie bardzo ciekawe. Jesli bysmy wiedzieli ze bramek jest sporo (czyli nie zapamietamy posrednich wynikow w logspace) \+ ze obliczenie bramki f(x,y) przewaznie wymaga zrobienia conda po x i conda po y (czyli przeliczenia na nowo calego drzewa bramek, ktorego wynikiem jest x), to dostalibysmy bardzo silny lower bound na czas obliczania wartosci obwodu. Probowalem juz to przekminic na rozne sposoby ale jeszcze malo skutecznie choc wydaje mi sie ze to powinno byc proste.

Cześć,

tak siedzę i myślę o tych algebrach BC i zauważyłem taki insight:  
w tym języku dla FLOGSPACE, funkcje bazowe modyfikują tylko bezpieczne argumenty, np.  
S\_0(: x) \= x0  
czyli jak chcemy wykonać jakiekolwiek faktyczne obliczenie, musimy wykonać je po 'bezpiecznej' stronie.  
To, w połączeniu z tym że nie możemy zduplikować argumentu bezpiecznego, oznacza tyle:  
możemy wykonywać tyle 'głupich' obliczeń na danym argumencie ile chcemy, ale jeśli chcemy  
podejrzeć argument, będziemy musieli przeliczyć funkcję od nowa.  
Tutaj ważne jest to że ostatecznie FLOGSPACE \= takie funkcje z BC które są postaci f(x:), tj.  
na początku każdy argument jest normalny i możemy go zduplikować. Czyli możemy sobie takiego x  
zduplikować parę razy, parę razy obliczyć tę samą funkcję i wtedy robić po jej wyniku ifa itp.,  
ale zdecydowanie wymaga to przeliczenia funkcji od nowa.

W kwestii L daje to takie spostrzeżenie: jeśli wykonamy ciężkie obliczenie, i chcemy po nim  
ifować, to będziemy musieli je powtórzyć o ile nie zapamiętamy wyniku. Czyli żeby wykonać  
sporo ciężkich obliczeń, albo będziemy musieli wyjechać poza LOGSPACE, albo potencjalnie wejść w  
wykładniczy czas (tak jak w naiwnym rekurencyjnym algorytmie dla Fibonacciego).

Próbuję wykazać że nie da się w tej algebrze BC rozwiązać problemu Circuit Value Problem, który jest P-zupełny (tj. na wejściu mamy opis obwodu oraz inputy). Problem z tym jest taki, że ciężko odeprzeć atak postaci 'co jak algorytm magicznie zauważy że circuit jest tautologiczny i nie wymaga żadnych obliczeń'. Do tego można by było spróbować albo wykorzystać istniejące w literaturze lower-boundy na circuit depth albo spostrzeżenie że jeśli maszynka Logspace by wykrywała wszystkie tautologie w obwodzie, to chyba rozwiązywałaby problem propositional tautology, który jest co-NP zupełny (czy jakoś tak?). Czyli wykazujemy że:  
\- istnieje taka klasa obwodów, że nie istnieje maszynka logspace, która by na każdy z nich  
  odpowiadała w czasie stałym (albo prawie stałym, np. 1/exp(n)). Do tego prawdopodobnie używamy  
  znanych obwodów które mają Omega(coś) głębokość.  
\- bierzemy jeden taki 'trudny' obwód i na jego wejściach dajemy kolejne 'trudne' obwody i tak dalej.  
  próbujemy w ten sposób stworzyć takie drzewo obwodów, że nie możemy zapamiętać wszystkich pod-wyników  
  (co by wymagało omega(log n) pamięci jeśli trudnych obwodów będzie ponad log n), a jednocześnie  
  wykorzystujemy wyniki z liści tego drzewa wykładniczo wiele razy. Skoro w algebrze Neergaarda wynik  
  podwyrażenia jest gubiony po otworzeniu go, musimy mieć ten wykładniczy blow-up  
\- zakładając że opis reprezetnacji tych obwodów będzie miał wielomianową wielkość, to może z tego by  
  wyszło że L neq P?

Trochę mi nie daje to spokoju bo myślę że ta konieczność re-obliczania podwyrażeń, która jest udowodniona przez L-zupełność algebry Neergaarda, jest właśnie tym czego nam brakuje żeby pokazać L neq P.  
Jak najbardziej wiem też że szansa że uda się ten L neq P udowodnić jest bliska zeru, jednak wartość oczekiwana dalej jest dość duża :)

Pozdrawiam  
Paweł Balawender  


[image1]: <data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAALBAMAAACEzBAKAAAAMFBMVEXo6OgAAACKiopra2vIyMipqambm5t8fHy6urotLS1dXV0ODg4fHx8+Pj7Z2dlMTEzV+d3TAAAAVUlEQVR4XmNkAAE+DSsmMOM3VwKYZshnYGBhMlJ6eJKZ4QFzs+zNYwwbH2xjCFjM4A2SZdqgyqAE0SnA8Aks8v0Awxk/EONfAgvTJRCDJ+DPMwUgAwCJIxRqOD34dAAAAABJRU5ErkJggg==>

[image2]: <data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAB0AAAARBAMAAADTf7pHAAAAMFBMVEXo6OgAAAB8fHyKioo+Pj7IyMgtLS26urpra2tdXV0ODg6pqakfHx+bm5vZ2dlMTEwXp8KbAAAAx0lEQVR4XmNgAAM+GMkE4ReByS8BUD7zBTD1zwHKD9sAUaYEoRhaoTQbAwsDk+HfC7cZmJssjtUycGYxMLgypLM6MJSqBXABzVFg4rBm0GYKYLAu2vCAgYErgennB4YNbB8YAvQZXjEw/CpgqpzAcBVoEp8ngzwDA8sCJicGXs9fBQx/DRh21zEwTWDyY/j+gR3Id2AV2sTwVYCFUZdxA8MDBsYPv28rXOCFuksb6h5+qHufQPkyUP4/iH/4QqH8z6xg6ksDAwA48jCIBoiaOwAAAABJRU5ErkJggg==>

[image3]: <data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACoAAAAOBAMAAACr0JNIAAAAMFBMVEXo6OgAAAB8fHybm5upqanZ2dktLS3IyMhdXV0ODg66urpMTExra2uKioo+Pj4fHx9N6ibVAAAAqklEQVR4XmNgQAM96AKhIIJxAZBgQghWJIFIrgcooqv5PUHUTwGwKJOJAYjnLVUJlvzDBRJlTb0AEr3Xag3V8w4kyryTEaiHWQasAQQcgZjZ1+LYCQaG//fblkEEee/JPGBgAFsBBEyPIbQRRwOQ85eBIQDE+6fwCEQx1zGBHMHJwA41kmUXkHBjYJjCrsDAomIFEYSAVAYGbd4PyCIIwAihmHcAif9uMFEAWnkfujJGWGsAAAAASUVORK5CYII=>