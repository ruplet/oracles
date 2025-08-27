How to run

1. Install GHCup: https://www.haskell.org/ghcup/install/

As of August 2025, you should run the below as non-root/non-admin user:
```
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

2. In the same directory as `bce.cabal`, run
```
cabal update
cabal build
cabal run
```

This should look like:
```
$ cabal run
+++ OK, passed 100 tests.
+++ OK, passed 100 tests.
[...]
+++ OK, passed 100 tests.
```
