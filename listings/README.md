The `dafny-lexer.py` is from: [https://github.com/Locke/pygments-dafny.git](https://github.com/Locke/pygments-dafny.git)

The `dafny-example.tex` file
was obtained with:

```
python3 -m venv .venv
. .venv/bin/activate
pip install Pygments==2.19.2

# Generate the pygments defaults.
pygmentize -S default -f latex > pygments-default.tex

python -m pygments -x -l "dafnylexer.py:DafnyLexer" -f latex -O encoding=utf8 -o dafny-example.tex dafny-example.dfy
python -m pygments -x -l "lean.py:Lean4Lexer" -f latex -O encoding=utf8 -o lean-example.tex lean-example.lean
python -m pygments -l prolog -f latex -O encoding=utf8 -o prolog-example.tex prolog-example.pl
python -m pygments -l haskell -f latex -O encoding=utf8,linenos=true -o haskell-linear-example.tex Linear.hs
python -m pygments -l c -f latex -O encoding=utf8,nowrap -o example-c-proving.tex example-c-proving.c
```

Take a look at how do I then include the resulting `.tex` in my project.
First, in the preamble in `driver.tex`, I define:
```
\usepackage{xcolor}
\usepackage{fancyvrb}
\input{listings/pygments-default.tex}
% this is for nice list of listings, bypassing the listings package because
% we compile to TeX anyway, not using pygments from latex
\usepackage{caption}
% Define a "listing" type (non-verbatim) with its own list:
\DeclareCaptionType[fileext=lol]{rawlisting}[Listing][List of Listings]
```

In `formalized-semantics.tex`, there is:
```
\begin{rawlisting}
\input{listings/dafny-example.tex}
\caption{Dafny example}\label{lst:dafny-example}
\end{rawlisting}
```

In `driver.tex`, next to `\tableofcontents`, I add:
```
\listofrawlistings{}
```
