# soas-quine

Generating quines via E-unification for second-order abstact syntax.

> :warning: Disclaimer: this is a very early work-in-progress.

## About

In this project, we aim to apply E-unification to generate fixpoints and [quines](<https://en.wikipedia.org/wiki/Quine_(computing)>) (programs that "produce" themselves in some sense). The inspiration for this project is [«miniKanren, live and untagged: quine generation via relational interpreters (programming pearl)»](https://doi.org/10.1145/2661103.2661105)[^6]. Indeed, miniKanren's logical engine
is based on unification, but in the paper they handle bound variables explicitly. The idea in this project is to delegate that part to the framework based on second-order syntax. In theory, that should significantly reduce the problem specification for quine generation.

Specifically, we aim to

1. Implement the general unification procedure from [«E-unification for Second-Order Abstract Syntax»](https://doi.org/10.4230/LIPIcs.FSCD.2023.10)[^1],
   perhaps with some optimizations, using the free scoped monad representation[^2].

2. Specify a dialect of LISP in second-order abstract syntax and formulate the problem of generating quines using second-order constraints.

3. Press <kbd>Run</kbd> and enjoy free generation of quines.

A, perhaps, oversimplified version of a quine is the fixpoint combinator in (untyped) λ-calculus. After encoding the untyped calculus in second-order abstract syntax, fixpoint combinators can be generated as solutions to the $E$-unification problem $\exists F. \forall f. \mathsf{app}(F[], f) \equiv_E \mathsf{app}(f, \mathsf{app}(F[], f))$ where $F$ is the (nullary) parametrised metavariable that we are solving for, $\mathsf{app}$ is the explicit constructor for function application, and $E$ — the set of axioms of untyped λ-calculus (specifically, just the $\beta$-equivalence in this case).

Unfortunately, the straightforward plan above has a few major issues that are not resolved yet:

1. The implemented E-unification algorithm is **very** inefficient.
   This is expected, and while we are aware of many optimizations (e.g. we could borrow a lot from [«Efficient Full Higher-Order Unification»](https://doi.org/10.4230/LIPIcs.FSCD.2020.5)[^3]), we hope that for this project we only need a handful of specific
   improvements to reduce the search space sufficiently.

2. Applying (at least well-known) higher-order unification (even as oracles) seems infeasible,
   since those algorithms work
   in a setting with strong normalization properties (or at least assuming
   that relevant solutions can be found under such assumptions). For example,
   Huet's preunification[^4], Miller's pattern unification[^5], or the aforementioned [«Efficient Full Higher-Order Unification»](https://doi.org/10.4230/LIPIcs.FSCD.2020.5)[^3]
   all work in a simply-typed setting which forbids fixpoints as solutions (because fixpoints wouldn't be well-typed).

## Quickstart

We are using the [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/) (or simply Stack) for this project.
To (re)build the project and run the default entry point, simply use

```sh
stack run
```

You may want to comment/uncomment sample unification problems in [`Main.hs`](soas-quine/app/Main.hs) for different sample runs.

More documentation may come in the future!

[^1]:
    Nikolai Kudasov. _E-Unification for Second-Order Abstract Syntax._ In 8th International Conference on Formal Structures for Computation and Deduction (FSCD 2023). Leibniz International Proceedings in Informatics (LIPIcs), Volume 260, pp. 10:1-10:22, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2023)
    <https://doi.org/10.4230/LIPIcs.FSCD.2023.10>

[^2]: Nikolai Kudasov. _Free Monads, Intrinsic Scoping, and Higher-Order Preunification._ To appear in TFP 2024. <https://arxiv.org/abs/2204.05653>
[^3]:
    Petar Vukmirović, Alexander Bentkamp, and Visa Nummelin. Efficient Full Higher-Order Unification. In 5th International Conference on Formal Structures for Computation and Deduction (FSCD 2020). Leibniz International Proceedings in Informatics (LIPIcs), Volume 167, pp. 5:1-5:17, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2020)
    <https://doi.org/10.4230/LIPIcs.FSCD.2020.5>

[^4]: Huet, Gérard. _Unification in typed lambda calculus._ International Symposium on Lambda-Calculus and Computer Science Theory. Berlin, Heidelberg: Springer Berlin Heidelberg, 1975. <https://doi.org/10.1007/BFb0029526>
[^5]: Dale Miller. _A logic programming language with lambda-abstraction, function variables, and simple unification._ Journal of Logic and Computation 1(4), 497–536 (1991) <https://doi.org/10.1093/logcom/1.4.497>
[^6]: William E. Byrd, Eric Holk, and Daniel P. Friedman. 2012. MiniKanren, live and untagged: quine generation via relational interpreters (programming pearl). In Proceedings of the 2012 Annual Workshop on Scheme and Functional Programming (Scheme '12). Association for Computing Machinery, New York, NY, USA, 8–29. <https://doi.org/10.1145/2661103.2661105>
