## Hoare Triples
The goal of this project is to define semantics and Hoare triples for a certain programming language and prove soundness of Hoare logic for those definitions. It follows chapter 14 of ,,Formal Reasoning About Programs'' by Adam Chlipala, but we use Agda instead of Coq. The only external library used is [PLFA](https://plfa.github.io/)'s standard library.

The code is divided into three main parts:

1. Definition of syntax for the language, which is formally defined as follows:
     - `Numbers n in N`
     - `Variables x in String`
     - `Expressions e :: n | x | e + e |  e - e |  e * e | *{e}`
     - `Booleanexpressions b :: e = e | e < e`
     - `Commands c :: skip | x <- e | *{e} <- e | c ; c | if b then c else c | {a}while b do c | assert(a)`

1. Definition of big-step semantics for the language, which mostly follows usual operational semantics for imperative languages. The unusual parts are:
    - dereference operator `*{e}` which is used to access the value of a variable pointed to by `e`, we can treat `*` as a global infinite array,
    - `assert(a)` command which requires that a general assertion about the whole state of the program holds,
    - `{a}while b do c` differs from the usual command because we add an assertion `a`, that must hold before the loop starts and after it ends. The invariant is added mostly as a technicality to make the proof of soundness easier,
    - there are two assignment commands `x <- e` and `*{e} <- e` which are used to assign values to variables and to the variables pointed to by `e` respectively.

1. Definition of Hoare triples and a proof of soundness of Hoare logic defined before (which means Theorem 14.2 from the book).
