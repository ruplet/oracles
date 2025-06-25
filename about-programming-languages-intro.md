NAJNOWSZY POMYSL:

1. Dlaczego powinniśmy rozważać słabe języki programowania? Bo mają lepsze własności. Mogą nam pozwolić na więcej automatyzacji.  
   1. Przykład: prosty kalkulator z dodawaniem, odejmowaniem, mnożeniem, dzieleniem. Łatwo sprawdzić czy pozwoli nam wykonać nasze obliczenia. Jeśli się to nam uda, to mamy gwarancję kiedy skończy obliczenia itp.  
   2. Przykład negatywny: silnik regex wyrażający NFA. nie mamy dobrej gwarancji ile zużyje zasobów\! może spowodować DDoS taki jak miał cloudflare  
   3. Przykład: język Haskell, który poprzez ograniczanie efektów ubocznych daje użytkownikowi “gwarancję” na to że program nie zrobi czegoś bardzo niespodziewanego  
   4. Mamy też theorems for free. Albo BCK?  
2.   
3. Chcemy napisać interpreter języka programowania.   
   1. W jakim najsłabszym języku możemy go napisać? To jest pytanie o to jaka “najładniejsza” (pod względem właściwości) teoria będzie w stanie zdefiniować funkcję wyrażającą interpreter, i do tego udowodnić jej poprawność względem specyfikacji i terminację  
4. Chcemy napisać funkcję GCD(x, y). W jakiej najsłabszej teorii możemy ją zdefiniować i udowodnić?  
   1. Bardzo ważne źródło: [https://projecteuclid.org/eBooks/perspectives-in-logic/Metamathematics-of-First-Order-Arithmetic/toc/pl/1235421926](https://projecteuclid.org/eBooks/perspectives-in-logic/Metamathematics-of-First-Order-Arithmetic/toc/pl/1235421926)   
   2. Również tutaj ważne: [https://link.springer.com/article/10.1007/BF01375521](https://link.springer.com/article/10.1007/BF01375521)  
   3. Albo w metalogice pokazujemy definicję w matematyce i realizujemy z niej program, albo dowodzimy poprawności danego programu\!

   

Wstep:  
W pracy chcę odpowiedzieć na następujące pytania, naturalnie się pojawiające przy projektowaniu nowego języka programowania:

- na jakim paradygmacie powinien być oparty język programowania? odpowiedzią jest: musimy najpierw ustalić do jakiego modelu obliczeniowego chcemy kompilować. Paradygmat języka programowania powinien być bardzo blisko powiązany z cechami modelu obliczeniowego, by ułatwić rozumowanie o własnościach programu. Mamy też kompilatory pomiędzy modelami obliczeniowymi  
- czy język programowania musi być Turing-zupełny? Nie musi, a czasem nawet nie powinien. Co więcej \- uważam że zazwyczaj nie powinien. Musimy zadać sobie pytanie: czy chcemy pozwalać użytkownikowi na programowanie funkcji działających w czasie wykładniczym?  Jeśli nie, po co wprowadzać mu ryzyko na napisanie wolnej funkcji przypadkiem? Implicit Computational Complexity dostarcza nam języki programowania dla FPTIME i FLOGSPACE. Fine-grained complexity być może kiedyś dostarczy np. dla Time-O(n^2), albo Space-O(n^2)  
- czy potrzebujemy systemu typów w języku programowania? Nie\! To najważniejsze niepoprawne założenie które popełniamy. Potrzebujemy systemu specyfikacji, ale system typów wcale nie musi być najłatwiejszą ani najbardziej wszechstronną metodą umożliwienia użytkownikowi automatycznego rozumowania o cechach programu. Leslie Lamport porusza tę kwestię w swoim artykule ([https://lamport.azurewebsites.net/pubs/lamport-types.pdf](https://lamport.azurewebsites.net/pubs/lamport-types.pdf) ). Ponadto, systemy typów są bardzo trudne do poprawnego zaprojektowania, zrozumienie nawet nieszczególnie silnych systemów wymaga lat doświadczenia  
- jak szczegółowe specyfikacje chcemy umożliwić użytkownikowi? Tutaj przegląd treści zadań z Olimpiady Informatycznej i jakie warunki tam zostają postawione na kształt danych, tj. cechy spełniane przez input itd. Typowo: dany jest na wejściu n:nat, graf n-wierzchołkowy, m:nat i permutacja {1, .., m} m liczb naturalnych oznaczających coś tam. Takie opisy danych są fundamentalnie deklaratywne i idą w zgodzie z teorią typów. Logika i teoria typów dostarcza nam narzędzia do zapisywania takich specyfikacji.  
- jeśli mielibyśmy syntaktyczną charakteryzację klasy TIME(x), SPACE(y) oraz przecięcia tych dwóch klas (tj. programy które zarówno działają w czasie O(x) jak i w pamięci O(y)), to pisząc programy w tej klasie, nie musielibyśmy dbać o żadne limity czasowe ani pamięciowe przy odpalaniu programu. Olimpiada Informatyczna nie musiałaby limitować pamięci dla naszego programu, bo “by design”, ten miałby porządane asymptotyczne właściwości. Jeśli system specyfikacji byłby wystarczająco silny, nie musiałaby też testować rozwiązań poprzez testy, a ponadto \- nie przechodziłyby zrandomizowane heury  
- teraz pytania do meta-języka (języka w którym implementujemy rozważany język): jeśli chcemy, by użytkownik naszego języka mógł deklarować że coś jest grafem albo drzewem, jak silna musi być meta-teoria która pozwoli nam sprawnie wyrazić interpreter/kompilator? Czy jesteśmy w stanie wygenerować interpreter automatycznie, mając wystarczająco dokładną specyfikację języka? Czy uda nam się napisać interpreter w Coq? W Haskellu? W języku, który nie wspiera GADT, nie musząc po drodze samemu implementować GADTs (oczywiście możemy napisać interrpeter na masyznie Turinga, ale będziemy musieli na nowo odkrywać wiele kanonicznych rzeczy).  
    
- Czy Abstract Syntax Tree jest faktycznie fundamentalne? Czy jesteśmy w stanie napisać język programowania, który nie wymaga pełnego CFG ani żadnego LL(1) do parsowania, tylko np. parsuje się regexem? Oczywiście możemy napisać język programowania, którego programy są liczbą naturalną \- indeksem poprawnego programu w Pythonie. Ale kompilator takiego języka będzie “niekanoniczny” (?); będzie miał sztucznie zawyżoną złożoność  
- Kanoniczny interpreter języka programowania: kanonicznym interpreterem systemu dedukcji dla logiki jest interpreter wynikający będący obliczeniową interpretacją konstruktywnego dowodu twierdzenia o soundness logiki

Specification langs:  
can use set theory for this\!  
[https://arxiv.org/pdf/cs/9511102](https://arxiv.org/pdf/cs/9511102)  
[https://lamport.azurewebsites.net/pubs/lamport-types.pdf](https://lamport.azurewebsites.net/pubs/lamport-types.pdf)

use Prolog (ELPI) unification for Sudoku solving  
Paper o uniform-random NP witness zeby znalezc losowe, rozwiazane sudoku  
Nastepnie, poprzez unifikacje, rozumowanie wstecz (traktowanie techniki dla Sudoku jako reguly dedukcji w systemie Hilberta, wzięcie danej uzupelnionej liczby z planszy jako wyniku tej reguly dedukcji i inferencja z ktorych innych komorek mogl taki wynik wyjsc. potem, po wymazaniu, test czy dalej jest unikatowe rozwiazanie.)

Problemy, na które starałem się odpowiedzieć:

1. Jakie feature’y jest sens dodać do języka programowania?  
   1. wynik: w while-programach, jeden while wystarczy (dowód przez Kleene algebra with tests, KAT)  
   2. wynik: Closures \+ tail-call optimization \=\> continuations  
   3. Jak silne typy potrzebujemy w języku programowania?  
      1. Studium typów wymaganych przez OI jako specyfikację danych/odpowiedzi  
      2. Przecież możemy skompilować Algebraic Data Types do Systemu F\! (Scott Encodings)  
      3. Specyfikacja poprzez Dafny, a nie poprzez system typów  
2. Jakie feature’y można dodać do języka programowania?  
   1. studium ‘Counterexamples in programming language design’, w którym wskazuję kilkanaście nieoczywistych sytuacji, w których język programowania stracił pożądaną właściwość (np. rozstrzygalność inferencji typów)  
   2. Sprowadzenie dyskusji do systemów logicznych i interpretacja ‘feature’ów’ jako aksjomatów / reguł dowodzenia. Odpowiedniość Curry’ego-Howarda **(ważne: podać bardzo konkretny przykład izomorfizmu, pokazujący wpływ reguł dowodzenia itd.\!)**, obliczeniowa interpretacja aksjomatu wyboru i hipotezy continuum  
   3. Krótka wzmianka o Curry-Howard-Lambek isomorphism i computational trinitary i o tym że do niczego to nie prowadzi na ten moment\! Teoria kategorii nie jest rozwinięta w tym kierunku, ponadto Monady nie mają logicznego odpowiednika  
   4. Skoro poprzez forcing możemy wykazać niezależność aksjomatów, to powinniśmy wtedy też móc wykazać, że feature wnosi coś do języka  
   5. **Glivenko, 1929: Classical logic proves Phi iff intuitionistic logic proves \~\~Phi \- to mam sformalizowane**  
3. Bardzo pożądana cecha programów: terminują\! Ponadto: działają w określonej złożoności czasowej. Descriptive Complexity Theory  
   1. LFP logic wyraża Ptime na str. uporzadkowanych  
   2. Quest for a logic of PTIME.   
   3. czy można zrobić język programowania z twierdzenia FO \+ Transitive closure operator \= NL, nondeterministic logarithmic space ?  
4. Implicit Computational Complexity. Kiepskie wyniki charakteryzujące różne klasy, ale zawierające explicit boundy albo działające tylko dla klas decyzyjnych. Czym w ogóle jest klasa problemów funkcyjnych NP \- FNP? TFNP.  
   1. Praca Bellantoniego i Cooka  
   2. **Praca Neergaarda \+ moje odświeżenie kodu**, żeby dało się go odpalić dzisiaj; poprawa, żeby interpreter odzwierciedlał paper; nowy e-mail autora, może nowy paper autora?  
   3. Prace Dal Lago i Schoppa: **IntML (dzięki mnie dodali licencję\!)** \+ moje odświeżenie kodu, może wziąć gotowe programy od Dal Lago?  
   4. Prace Ugo Dal Lago o kolejnych klasach, np. safe tree recursion dla PSPACE  
5. Circuit complexity: Safe recursive evaluation implies an upper bound on the depth of a corresponding circuit   
6. Weryfikacja formalna. Praca Forstera i Ciaffaglionego \+ moje poprawki do tego drugiego. Sytuacja w weryfikacji jest kiepska, ale może Dafny przyjdzie z pomocą?

SZERZEJ:

Przegląd PSPACE zupelnych rzczy:  
mamy tauto w Coq (LJT\*) i itauto w Lean  
[https://leanprover-community.github.io/mathlib\_docs/tactic/itauto.html](https://leanprover-community.github.io/mathlib_docs/tactic/itauto.html)  
oba sa oparte na pracy Dyckhoffa:  
To jest paper na ktorym to bazuje, jest tez podsumowanie innych algorytmow do tego problemu\! w tym cytowanie statmanna, ktory wykazal ze problem jest pspace-zupelny oraz algorytmu Hudelmaiera, ktory dziala w DSPACE(n log n)\! [https://www.cs.cmu.edu/\~fp/courses/15317-f08/cmuonly/dyckhoff92.pdf](https://www.cs.cmu.edu/~fp/courses/15317-f08/cmuonly/dyckhoff92.pdf) 

jest też MINLOG, ktory ma dostarczac kontrmodel kripkego ponoc  
[https://link.springer.com/chapter/10.1007/3-540-69778-0\_29\#preview](https://link.springer.com/chapter/10.1007/3-540-69778-0_29#preview)  
[https://www.mathematik.uni-muenchen.de/\~logik/minlog/](https://www.mathematik.uni-muenchen.de/~logik/minlog/)

oraz inne repo dostarczajace kontrmodele:  
[https://members.loria.fr/DGalmiche/files/=papers/EICNCL2018/EICNCL2018\_paper\_2.pdf](https://members.loria.fr/DGalmiche/files/=papers/EICNCL2018/EICNCL2018_paper_2.pdf)  
[https://github.com/ferram/jtabwb\_provers/](https://github.com/ferram/jtabwb_provers/)

Relacja jezyka i metajezyka:  
Sa 3 jezyki (modele): a) definicja modelu o ktorym bedziemy wnioskowac b) model, w ktorym zadajemy pytanie o własności pierwszego modelu c) model, w którym jesteśmy w stanie udowodnić pytanie zadane w drugim modelu nt. pierwszego

Ten drugi oczywiście jest przynajmniej tak samo silny jak pierwszy, a trzeci \- przynajmniej tak samo jak drugi.  
Przykład: możemy zapisać maszynę Turinga jako piątke \<przejscia, alfabet, itd.\> czyli jako podzbior N^k  
mozemy zdefiniować, ze maszyna Turinga, po dostaniu jakiejś taśmy na wejściu, wyrazi jakąś funkcję częściową, albo zadać pytanie czy ją wyrazi  
i możemy próbować odpowiedzieć na takie pytanie \- dla maszyn turinga, każde nietrywialne pytanie z tw. Rice’a jest nierozstrzygalne, tj. musimy miec silniejszy model niz maszyny turinga zeby na nie odpowiedziec

Sekcje:

1. Jakie cechy można dodawać do języka programowania, tak żeby nie tracił pożądanych własności?  
   1. Nie można zrobić języka z typami zależnymi i kontynuacjami  
   2. Closures \+ tail-call optimization \=\> continuations  
   3. You can implement SK calculus in Haskell, so that type inference doesn’t terminate  
   4. mnóstwo podobnych wyników do a)  
   5. Spory branch mojego czytania: sprowadzenie systemu typów do logiki, by móc użyć silnych wyników z logiki  
   6.   Glivenko, 1929: Classical logic proves Phi iff intuitionistic logic proves \~\~Phi \- to mam sformalizowane  
   7. ale jak się mają efekty / monady do logiki? Nie mają\!  
   8. a jak się mają inne aksjomaty z matematyki do obliczeń? Implementation of forcing in Coq as a program transformation and show a proof of the negation of CH  \- zrobiłem cały przedmiot Set Theory, żeby zrozumieć forcing  
   9. podobne wyniki, tj. np. odzwierciedlenie Axiom of Choice w curry-howard isomorphism  
2. Descriptive complexity theory, czy można zrobić język programowania z twierdzenia FO \+ Transitive closure operator \= NL, nondeterministic logarithmic space ?  
3. Jak silne typy potrzebujemy w języku programowania? Przecież możemy skompilować Algebraic Data Types do Systemu F\! (Scott Encodings)  
4. Implicit Computational Complexity\! problem logiki dla PTIME na strukturach uporządkowanych i nieuporządkowanych\!  
5. Least Fixed Point logic captures PTIME on ordered structures \- can you make a programming language out of it?  
6. Papier Bellantoniego-Cooka, Neergarda  
7. Liczne prace zawierające (kiepskie) charakteryzacje klas złożoności decyzyjnych / zawierające explicit boundy  
8. Prace Ugo Dal Lago np. safe recursion dla \#P, PSPACE etc.  
9. Kod i zapomniany paper Neergaarda \- odświeżyłem go  
10. Język IntML zaprogramowany przez Ugo Dal Lago \- chcę dodać do niego lepszą dokumentację / odświeżyć go żeby dało się odpalić  
11. Aspekt formalizacji języków \- czytałem o tym jak pracować z maszynami Turinga w Coq, doprowadziłem do porządku dowód nierozstrzygalności HALT. Sytuacja nie jest najlepsza, ale może wystarczy nam weryfikacja w Dafny?  
12. Pożądanym środowiskiem do rozwijania minimalistycznych języków programowania jest Logical Framework. Najlepszym przykładem takiego środowiska jest Isabelle lub Isabelle/Pure, bazowa logika Isabelle. Możemy w takim frameworku definiować różne inne logiki, nie musząc polegać na / rozumieć bazowej logiki np. Coqa lub Leana, które są bardzo skomplikowane