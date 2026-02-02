# FreeCP - CP with context-free session types

Formalization of FreeCP, a version of CP with **context-free**
session types.

## Overview

### Global Modules

* [Axioms](Axioms.agda)
  * postulate the **extensionality** axiom. This is necessary to prove the equality
    of renamings, unfoldings and substitutions, which are all represented as functions.
* [Main](Main.agda)
  * imports everything

### Types

* [Type.Base](Type/Base.agda)
  * representation of recursive, polymorphic, context-free session types
  * duality is an **involution**
  * definition of `void` type
* [Type.Renaming](Type/Renaming.agda)
  * definition of **renaming** of recursion type variables
* [Type.Unfolding](Type/Unfolding.agda)
  * definition of recursive type **unfolding**
  * duality and unfolding commute
  * renaming can be expressed as an unfolding
  * independent unfoldings commute
* [Type.Equality](Type/Equality.agda)
  * definition **heterogeneous iso-recursive equality** of types
  * heterogeneous equality implies propositional equality for same-indexed types
  * renaming preserves heterogeneous equality
* [Type.Substitution](Type/Substitution.agda)
  * definition of **substitution** for polymorphic type variables
  * composition of substitutions
  * duality and substitution commute
  * unfolding and substitution commute
* [Type.Transitions](Type/Transitions.agda)
  * definition of **labelled transition system** for context-free session types
  * the LTS is **deterministic**
  * ε transitions lead to `skip`
  * transitions are preserved by duality, unfoldings and substitutions
* [Type.Equivalence](Type/Equivalence.agda)
  * coinductive definition of **bisimulation** for ground session types
  * definition of **type equivalence** ≈ as bisimulation for all substitutions
  * ≈ is an equivalence relation
  * duality, substitutions, transitions preserve ≈
  * a recursive type and its unfolding are equivalent
* [Type.Kind](Type/Kind.agda)
  * definition of **kind** and of sequential kind composition
  * properties of sequential kind composition
  * duality and substitutions preserve kind
  * soundness and completeness of the kinding system
* [Type.HeadNormalForm](Type/HeadNormalForm.agda)
  * definition of **head normal form**
  * definition of "**visible**" type (transition-enabled type)
  * **decidability of visibility**
  * existence of (equivalent) head normal form for every type

### Typing Contexts

* [Context.Base](Context/Base.agda)
  * definition of **typing context** and of **context splitting**
  * splitting is commutative and associative, units of splitting
  * definition of **separating conjunction** and **magic wand**
  * definition of **context equivalence**
  * substitutions preserve context splitting
* [Context.Permutations](Context/Permutations.agda)
  * definition of **context permutation**
  * basic properties of permutations
  * substitutions preserve permutations

### Processes

* [Process.Base](Process/Base.agda)
  * intrinsically-typed representation of processes and typing rules
  * permutations and substitutions preserve typing
* [Process.Congruence](Process/Congruence.agda)
  * definition of **pre-congruence** relation
  * pre-congruence preserves typing and measure
* [Process.Reduction](Process/Reduction.agda)
  * definition of **reduction** relation and its reflexive, transitive closure
  * reduction preserves typing up to type equivalence
  * reduction decreases measure
* [Process.DeadlockFreedom](Process/DeadlockFreedom.agda)
  * classification of threads and definition of canonical cut
  * definition of *alive* process
  * well-typed processes are **deadlock free**
* [Process.Termination](Process/Termination.agda)
  * proof of **strong termination**
  * definition of normalisation function for processes
