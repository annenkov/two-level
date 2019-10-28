## Lean Formalisation of Two-Level Type Theory

Requires Lean 2 (version 0.2.0) to compile.

Lean 2 installation instructions in Ubuntu : https://github.com/leanprover/lean2/blob/master/doc/make/ubuntu-12.04-detailed.md

Alternatively, use `Docker` image: https://github.com/annenkov/2ltt-docker
The image contains Lean 2, our development and Emacs with `lean-mode`, allowing to navigate through the development and compile it.

# Contents

| File | |
|--------------------|:--------------------------------------------------------------------:
| fibrant.lean       | implementation of the two-level type theory
| fibrantlimits.lean | a proof of the theorem that every Reedy fibrant diagram on a category with finite type of objects has a fibrant limit
| finite.lean        | facts about finite sets and categories
| inverse.lean       | definition of inverse categories
| limit.lean         | definition of limits and construction of limits in category of pretypes
| matching.lean      | definition of the matching object
| pullbacks.lean     | definition of a pullback, constructed explicitly and using the limit of a diagram along with a proof these definitions are equivalent. Proof of the Lemma 7 (pullback of a fibration along f is a fibration)
| simplicial.lean    | initial definition of semi-simplicial types (work in progress)
| facts.lean         | some auxiliary lemmas which we could not find in the standard library

# Compilation

Use ```make``` to compile the project, or run ```linja``` directly.
