# Lean Formalisation of Two-Level Type Theory

Files in the `2ltt` directory:

| File | |
|--------------------|:--------------------------------------------------------------------:
| fibrant.lean        | implementation of the two-level type theory
| finite.lean         | facts about finite sets and categories
| limit.lean          | definition of limits and construction of limits in category of pretypes
| inverse.lean        | definition of inverse categories
| pullbacks.lean      | definition of a pullback, constructed explicitly and using the limit of a diagram along with a proof these definitions are equivalent. Proof of that fibrations are closed under pullbacks.
| matching.lean       | definition of the matching object
| matching_facts.lean | facts about the matching object from the category C with one object removed
| fibrantlimits_aux.lean  | auxiliary lemmas for the proof of the fibrant limits theorem including equivalences forming the core of the proof
| fibrantlimits.lean  | a proof of the theorem that every Reedy fibrant diagram on a category with finite type of objects has a fibrant limit
| simplicial.lean     | initial definition of semi-simplicial types (work in progress)
| facts.lean          | some auxiliary lemmas which we could not find in the standard library
| types/*             | examples of reasoning in the inner (fibrant) theore. Mainly, ported from Lean 2 HoTT library.

## Compilation

Requires Lean 2 (version 0.2.0) to compile.

Lean 2 installation instructions in Ubuntu : https://github.com/leanprover/lean2/blob/master/doc/make/ubuntu-12.04-detailed.md

After installing Lean 2, in the terminal, go to the directory containing the development and use ```make``` to compile the project, or run go to the `2ltt` folder and run ```linja``` directly.

Use your favorite editor to navigate the source code (see some hints about emacs lean-mode blow).

### Using Docker

Alternatively, use `Docker` image. The image is based on Ubuntu and contains Lean 2, our development and Emacs with `lean-mode`, allowing to navigate through the development and compile it.

Steps to build a Docker image:
* In the terminal, go to the directory containing the development and run `make docker`
* After building step is complete (this might take some time), run `make run-image` to connect your current terminal session to the container.
* In the container, type `emacs /root/2ltt/fibrantlimits.lean` to start editing `fibrantlimits.lean` with the lean-mode in Emacs.


### Interacting with the Lean development in the Docker image

As we have said before, the docker image comes with Emacs and lean-mode. The lean-mode provides syntax highlighting and allows to interactively develop proofs. 
Use <kbd>C-c C-g</kbd> to show goal in tactic proof, <kbd>C-c C-p</kbd> to print information about identifier, <kbd>C-c C-t</kbd> to show type, and <kbd>C-c C-l</kbd> to comple a lean file.

Alternatively, one can use the command line to compile the project or individual files:

* After executing `make run-image`, change directory (in the Ubuntu's command line) to our Lean development `cd /root/2ltt`.
* Run `make clean` to clean previously compiled files
* Run `make` again to rebuild the project.
* Individual files can be compiled using `lean <filename.lean>`.

The image comes with the preinstalled `nano` editor that can be used to view/edit the source files (but without syntax highlighting). Other editors can be installed, if required, using the `apt-get` command. For example, `apt-get install vim`.

