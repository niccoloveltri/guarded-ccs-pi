# Formalizing CCS and π-Calculus in Guarded Cubical Agda

Dependent type theories with guarded recursion have shown themselves suitable for the development of denotational semantics of programming languages. In particular, Ticked Cubical Type Theory (TCTT) has been used
to show that, for guarded labelled transition systems (GLTS), interpretation into the denotational semantics maps bisimilar processes to equal values. In
fact the two notions are proved equivalent, allowing one to reason about equality in place of bisimilarity.

We extend that result to the Calculus of Communicating Systems (CCS) and the π-calculus. For the latter, we pick early congruence as the syntactic notion of equivalence between processes, showing that denotational models
based on guarded recursive types can handle the dynamic creation of channels that goes beyond the scope of GLTSs. 

Hence we present fully abstract denotational models for CCS and the early π-calculus, formalized as an extended example for Guarded Cubical Agda: a novel implementation of Ticked Cubical Type Theory based on
Cubical Agda.

--- 

The file [Main.agda](https://github.com/niccoloveltri/guarded-ccs-pi/blob/main/Main.agda) imports the whole development.

The code typechecks using Agda version 2.6.4. It requires the installation of the [cubical](https://github.com/agda/cubical) library.
