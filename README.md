## Lean Formalisation of Two-Level Type Theory

Requires Lean 2 (version 0.2.0) to compile.

# Contents

| File | |
|--------------------|:--------------------------------------------------------------------:
| fibrant.lean       | implementation of the two-level type theory
| fibrantlimits.lean | proof of Theorem 10 (every Reedy fibrant diagram has a fibrant limit)
| finite.lean        | facts about finite sets and categories
| inverse.lean       | definition of inverse categories
| limit.lean         | definition of limits and construction of limits in category of pretypes.
| matching.lean      | definition of the matching object
| pullbacks.lean     | definition of a pullback, constructed explicitly and using the limit of a diagram along with a proof these definitions are equivalent. Proof of the Lemma 7 (pullback of a fibration along f is a fibration)
| simplicial.lean    | initial definition of semi-simplicial types (work in progress)
| facts.lean         | some auxiliary lemmas which we could not find in the standard library

# Compilation

Use ```make``` to compile the project, or run ```linja``` directly.
