- Keep style of complexity classes / logics consistent:
```
na górze strony 3 jest AC^0 najpierw pogrubione a zaraz potem AC0 bez pogrubienia
```
```
Strona 4 - wokół plusa w nazwach logik raczej nie powinno być spacji.
```
```
Widzę że czasem jest L i P a czasem (zwykle) LOGSPACE i PTIME - należałoby ujednolicić.
```

- UK vs US english (analysing, analyzed)

- Watch out for separations between things
```
Też po tym pierwszym punkcie nie ma odstępu takiego jak po kolejnych.
```

- Keep the word "expressing" vs "capturing" complexity classes consistent:
```
Tytuł powinien być dokładnie taki jak zgłoszony (Practical programming languages expressing complexity classes),
ewentualnie można wnioskować o zmianę.
```

- Keep the usage of em-dash "---" and en-dashes "--" consistent and correct, watch out for hyphens ("-")!
```
Myślniki powinny być dłuższe, np w zdaniu "A related - and in many...".
Stosuje się raczej em-dash (czyli --- w Latexu) bez spacji,
alternatywny styl to en-dash (czyli -- w Latexu) ze spacjami.
```

- Vector noration: bar vs arrow over variable:
```
Połowa strony 8 "and we write f(x)=..." - tutaj coś się popsuło ze strzałkami nad f i nad x.
```

- Watch out for bad overfulls:
```
No i oczywiście linie nie powinny wystawać w prawo (str 11, 12).
```

- Don't start sentence with "i.e.", "e.g.":
```
Niezależnie od tego, o ile wiem, nie zaleca się zaczynać zdania od "I.e.", przynajmniej w formalnym tekście.
```

- Be aware when to use "\@", "\ ", "~", "\,", "\;" and the other spacing macros:
```
Rozdział 1.1, linia 2: Po "I.e." jest dłuższa spacja (podobnie jeszcze w paru miejscach).
Generalnie Latex po kropce, czyli końcu zdania stosuje większą spację niż między słowami w zdaniu,
ale tutaj końca zdania nie ma. Po takiej kropce nie kończącej zdania należy wstawić "\@" albo użyć "~"
zamiast spacji (chyba pierwsze pozwala na podział linii w tym miejscu a drugie nie).
```

- Parse the pdf and ensure that "\ref" and "\autoref" renders as the correct name, and not as just a number,
or e.g. saying that "\begin{remark}" is a "Theorem 1.1.1".
```
"in 1.7" (tuż nad rozdziałem 1.1.1, ale podobnie dalej) -> "in Section 1.7" - sama liczba wygląda słabo,
a też czasem nie wiadomo czy chodzi o numer rozdziału czy czegoś innego.
```

- Ensure the style of NCipoly is nice to read:
```
Pod Def. 1.1.7: W "NC^i_{/poly}" (i kolejnych klasach) wykładnik "i" jest mocno z prawej -
raczej niech będzie tuż przy NC.
```

- Proof-read the whole thing to ensure I'm consistent with using AC/poly vs AC.
```
Rozdział 1.2.1: Tutaj nadal o NC^0_{/poly} a nie o NC^0 (?)
```

- Also, ensure the definition of uniformity is clear in every place!

- Interesting foundings. Maybe mention in work?
```
Drugi bullet w 1.2.1 ("Explain why...") - Nie słyszałem o tym. Zaciekawiło mnie to, ale
jeszcze nie zajrzałem do cytowanych artykułów. Może w kolejnej wersji pracy wyjaśni się o co chodzi.
```
refers to:
```
1.2.1:
TODO: Explain why all sets complete underAC0reductions are already complete underNC0reductions Manindra Agrawal, Eric Allender, Impagliazzo, et al. 1997; ManindraAgrawal, Eric Allender, and Rudich 1998a.
```
second one:
```
Ostatnie zdanie na stronie 6 też jest intrygujące, jestem ciekaw o co chodzi. Bo jednak ten DLOGTIME generujący obwód nie ma dostępu do wejścia.
```
refers to:
```
TODO: Clarify what notion of uniformity should be used forNC0, given thatDLOGTIMETuring machines can do things that cannot be done by anyNC0circuit
```

- Style of ac0/poly; names of gates check consistency:
```
Rozdzał 1.8: Tutaj "AC^0/poly" pisane inaczej. Również zamiast bramek "AND" są "\land".
```

- Fix definition of AC0 reduction:
```
Rozdział 1.14, linia 4 (z czego korzysta F) - zamiast F_{i-1} miało być zapewne F_n.
```
refers to:
```
Definition IX.1.1 CN10. We say that a string function F (resp.  a number function f) isAC0-reducible toLif there is a sequence of string functionsF1,...,Fn(n⩾0)such thatFiisΣB0-definable fromL∪{F1,...,Fi−1}, fori= 1,...,nand F (resp.  f) isΣB0-definable fromL∪{F1,...,Fi−1}. A relation R isAC0-reducible toLif there is a sequenceF1,...,Fnasabove, and R is represented by aΣB0(L∪{F1,...,Fn})formula
```

- Names of logics:
```
Ważniejsze: "FO/SO without bit" brzmi dziwnie. U Immermana faktycznie to się nazywa "BIT"
(wielkimi, a nie "bit"), no ale jak ktoś tam nie zajrzy to twierdzenia nie zrozumie - lepiej
"FO without arithmetical predicates" i od razu zdanie staje się jasne.
```

- Footnotes:
```
Potem są te przypisy. Drobna sprawa, że w przypisie są zdania, ale zaczyna się małą literą.
```

- Fix bilbiography:
```
Bibliography wymaga jakichś poprawek redakcyjnych (zapewne na koniec) - np. nieraz URL dwukrotnie, albo dodatkowo w zwykłej czcionce i wystaje za stronę.
```


- Consistency: capitalized/not letter in 'Random access Turing machine' - 'Random' vs 'random', 'access', Turing vs turing etc.

- Proof-read style of enumerations. Everywhere should be `begin enumerate` instead of `begin itemize`.
And have roman style

- Inside of `begin enumerate`, use semicolons in intermedate bullets. Use small-letter after a semicolon.
    Use a dot at the end of enumeration (in last bullet)
```
Duża litera po średniku (w enumerate) - czy tak gdzieś widziałeś? Mi ten styl wydaje się dziwny, raczej bym dawał tam wszędzie małe litery.
W definicji 2.1.7 (i) wielka litera w nawiasie -> też raczej mała.
```

- Consistency: vectors: `\bar` vs `x_1, x_2, ...`
- `\dots` vs `...` etc.

- Quantifiers: use `\ldot` aftre a quantifier always! And don't use `.` instead.

- Consistency: decision problems vs decisional problems vs decisive / complexity classes etc.

- Consistency: \rightarrow vs \to, \Longleftrightarrow vs \iff etc.

- Consistency: watch out: \mathsf{Zero}(x) vs \mathsf{Zero(x)}

- mathsf vs texttt vs mathbb etc.