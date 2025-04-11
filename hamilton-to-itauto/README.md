# hamilton-to-itauto

Encoding a graph to an Intuitionistic Propositional Logic formula, which is a tautology
if and only if the input graph has a Hamilton cycle. Then using Lean's `itauto` tactic
or Rocq's `tauto` to find the proof of being a tautology. The proof encodes a Hamilton cycle,
i.e. you can extract the Hamilton cycle by parsing the proof appropriately.

Source of algo: https://www.mimuw.edu.pl/~urzy/Litt/zelit4tg2.pdf

Goals for now:
- strengthen the reduction of Hamilton to BCK logic
- implement a tactic for BCK logic, which calls an external SAT solver to prove (because BCK logic is NP-complete)
- bck logic can be nicely implemented in Isabelle, that's in another repo
- this SAT-solver hammer for BCK will have to be implemented on the level of an Isabelle tactic
- compile mine reduction from Hamilton to my representation of BCK logic, use the hammer to find cycle
- the goal is not to show how to solve hamilton, as it can be readily translated to sat, but to show how to use theorem BCK = NP and that it should be represented as a tactic. and that BCK can be implemented in Isabelle or another logical / metamathematical framework.

Please take a look here, there is a Hamilton formula expressed in Lean
with description how to extract a Hamilton proof from it:
(the same example is in HamiltonToItauto/Lean_Example_with_notes.lean)

https://live.lean-lang.org/#codez=PQWgBAggrgLg9gWwIYwJYGMkBssE8wDmApgHZEBOKRAJmADJFIlgBmqWRrc5YAEkgnbxm6XOg5gAkgAUAwl3IIoWJGBDAAUKgQAHbjDABZFAAssqAEYA6ACpJ0adFcl3YcDRoBuScqiQWJAApPAH0ARnCwAC4waXI4HQBKLx8/AM5g8JCSOBhImLiE5O9ffyDQiIAmaNj4pJTS9LBMiJy86oK64tSyjIqQgGYawvqStPKstsHhrobxvqydXwQifNqiud7mgjhsAAYZjbGtzMq1ke7GibOpsMPRnqbTkI71h6uFm9yX+8v55tCZyGnSOj2u2W+wLefxOgJCS20qzuIPe/0CO2wyOhmyeoQG51mx1xgwheSxFxxE3xrwpRKppJ+KJhxPxUNpYIW+KmbMJHIBJIRKwJoI+212WBpvNF6PFPI2GhgJiI3CICDAqB06BCLG4ShU0Q0YEIsrAgCTCZotSLmuG3M1gPEMu7mjFYMKJO0uvbu82BZ5O+2Tb7+h2253it0e8Veu2+h3BwNku02oORzHe437dOW0MB/H+y3Va0vBmF3Ml1MS9MuiM+5OJosRfNw0v9KYtkltiuVKvhrMhlNFs5Nknt1rfdtfdpdntpmOtgcBsdTovUudZIaDhkbsvcisDGeVteTq0B4+jn614vb+d5a8dyF7g/dtdchf95eni/81lJhPTTe7mG2D7tOFYHFEAC8GgWPgqAwEgbgeAAxAiJAGBqWo6ooyhIB4IDgEq5BEAANGAuBwFAYCYMwRAAB4wJQDhgIqnD8IIWDCFRYgSDBYB0QIqAkIJBDMUqrBQCQDioHAzAWHA1C4Bo+HMXAYAAO4mBgJjqpq2q6jhfHeFgUBUAAzipVhKeApk6EQ6CoGwmA4LgpHkZR8EANacKoWBwHAHnqZp6DaUgpmmVAuhoDJ5mBCYeykSYYQJQA7KRVjpe6PicE5HC0OpcHaaZiDeeQBARaQMCmVZ6rMCxYByQppEsURYBZa1WBFUaZBqWASyqqgplEOZiUAGwjdURAwE4YBQINtCha1pXlWhpmkRYsCiUNJVENVbTqro+hMDAVhgAAQhtGmkGRFFgINnBEFYBAnRBAB8YAmMleHgPxugSFhrVyZ4RBRNVLASYukQ3pDWTVFDsPrhDu6ep+dx1tDZzw2en5DGjQzVmWYSGmo4BGu+0OrmT8M/mTePitULpDHF713CY1QmIzAAs70AKzvSN73Je9AAc70AJxgK9RPKYl4nMIlByJSzYTVK9PPM0rBxg3LyUjaL/MfbrgsG6LIuqyY4uJWzOsmwLuv81rAvJXsIsfU7FvJclYQHGbeweEa0sUCRrUsDAFDtVgm1gMggmy4tBCrddlEmEgQMS29TC0Cxct3A78vq2l6VS+AcFR4wJDmYqKCJ1R2ARzLakFbdxWy1JMmteZPhlSsaEnQAyqpbk1zgzP5YqTcrIqwnEUXgVaaXTDmYPs2cH1giDSPEEWv08bHvGr71hmroHl6M+dYPSxwKnyOzcJENJU3i7qhXYk5NQ2UmHAg3MDHbDkKZBj/yIDoAAhEAA
