---
layout: post
title: About Sudoku
---

## Main question
Can you write an efficient computer program, which will output a random, uniquely solvable
Sudoku puzzle? What about a random, solvable Rubik's cube state? I.e. sample from
the uniform distribution over all valid Sudoku puzzles (2 ways: a) sample from solved Sudoku grids,
then proceed to just remove some entries, but it might render the solution to not be unique, b)
sample from the set of solvable, unfinished sudoku grids)

## About Rubik's Cube
Language for Rubik's Cube?
a) sequence of moves from the solved state to the current state
b) mere labels; to check if can be solved, the problem is equivalent to [3926446]
https://math.stackexchange.com/a/3926446/876802

solving Rubik's Cube requires O(n^2) moves:
https://arxiv.org/pdf/1106.5736.pdf

finding an optimal Rubik solution is NPC:
https://arxiv.org/abs/1706.06708

how to tell if Rubik's cube is solvable?:
https://math.stackexchange.com/questions/127577/how-to-tell-if-a-rubiks-cube-is-solvable

is Sudoku group uglier than Rubik's Cube's?
https://en.wikipedia.org/wiki/Mathematics_of_Sudoku#The_sudoku_symmetry_group

Schreier-Sims algorithm for Sudoku correctness checking?
Some discussion here: http://forum.enjoysudoku.com/sudoku-symmetry-group-minimal-spec-t35573-75.html

Knuth proving Schreier-Sims is polynomial time: (w.r.t. what?)
https://arxiv.org/pdf/math/9201304.pdf


## Syntax for Sudoku
Can we design such a syntactical language, so that it'll only be possible
to write down in it a valid solution to a Sudoku, and all the valid Sudoku
solutions will be possible to write in it?

## The number of completed Sudokus of size n^2 x n^2
First thing I looked at was literature about counting the number of valid
Sudoku solutions, as in enumerative combinatorics, one often has to
somehow classify the objects in question in order to count them.
What I learned:
- this problem is open and no general solution is known. Solutions for grid
sizes 0, 1, 4, 9 are only known: https://oeis.org/A107739
- there is roughly 6 * 10^21 distinct solutions to the 9x9 grid: https://people.math.sc.edu/girardi/sudoku/enumerate.pdf
- the authors (Felgenhauer, Jarvis, 2005) came up with a few reductions (such
as parametrizing a solution by the permutation (1, ..., 9) so that numbers in
the first box are increasing from 1 to 9), but then had to resort to
a brute-force search of the remaining possible values.
- (Russel, Jarvis 2006: http://www.afjarvis.org.uk/sudoku/russell_jarvis_spec2.pdf) here they analyzed the number of valid solutions modulo some solution-preserving symmetries. They found it's ~5 bilion using Burnside's lemma. But the Burnside's lemma is non-constructive. By using this approach we could design a language in which a valid operation is applying one of the solution-preserving symmetries (such as relabeling the numbers), but we would have to start with a valid solution - and no classification is known for the 5B starting points; http://www.afjarvis.org.uk/sudoku/sudgroup.html
- Aviv and Ilan Adlers (father and son) found out that the symmetries considered
above are truly all the symmetries which preserve solutions: https://adler.ieor.berkeley.edu/ilans_pubs/suduko_2008.pdf

## Advanced sudoku-solving techniques
- Phistomefel Ring:
  * Numberphile video: https://www.youtube.com/watch?v=pezlnN4X52g
  * https://masteringsudoku.com/phistomefel-ring/

## Generating Sudoku boards
Is it likely we will ever be able to reliably generate Sudokus? It seems unlikely. No example is known of a problem L which is NP-complete, but #L is not #P-complete. As generalized Sudoku is an NP-complete problem, the number of valid solutions is likely a #P-complete problem, and thus at least as hard as NP. So generating Sudokus is probably as difficult as solving them and
a backtracking algorithm which checks a solution by trying to solve it, seems optimal.

But: maybe we can use some sort of kernelization?
Also, we don't have to generate n^2 x n^2 Sudokus in general - 9x9 is
totally fine.
