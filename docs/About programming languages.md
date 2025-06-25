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

   