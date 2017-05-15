Artifact accompanying ICFP paper __Normalization by Evaluation for Sized Dependent Types__

Sit -- Checking dependent types with sized natural numbers
==========================================================

Installation with docker
------------------------

If you have a `docker` installation, you can get and test `Sit` by the command on the shell:
```shell
docker run theowinterhalter/icfp-sit
```
You should see something like this:
```
Unable to find image 'theowinterhalter/icfp-sit:latest' locally
latest: Pulling from theowinterhalter/icfp-sit
cd0a524342ef: ... Pull complete
dd5f938bc637: ... Pull complete
cb90bb83bdab: ... Pull complete
a1e5cf9ae1e4: ... Pull complete
12fbf6ef4b99: ... Pull complete
b6a6d86e767f: ... Pull complete
6dc027e33bb0: ... Pull complete
Digest: sha256:9f1ff6ab7cfdc0de82df61fac6a0b6cbd34d62de7a8e5596d4217a5a4fa95772
Status: Downloaded newer image for theowinterhalter/icfp-sit:latest
Checking Eq : forall (A : Set) (a b : A) -> Set1
Checking Eq = \ A a b -> (P : A -> Set) -> P a -> P b
...
```

Installation from Hackage
-------------------------

If you have `ghc >= 7.8` and `cabal >= 1.24`, you can install `Sit` from `hackage.haskell.org`:
```shell
cabal update
cabal install Sit
cd $HOME/.cabal/share/x86_64-linux-ghc-7.10.3/Sit-0.2017.5.1/test
Sit.bin Test.agda
```
This assumes that your `.cabal/bin` is in the `PATH`.
You also have to adjust the path in the `cd` command above to your system.

Installation from the supplied tarball
--------------------------------------

With GHC, you can also install from the supplied tarball:
```shell
tar xzf Sit-0.2017.2.26.tar.gz
cd Sit-0.2017.2.26
make
```
