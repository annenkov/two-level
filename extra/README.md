# A docker image for 2LTT development

A docker image for the two-level type theory formalisation in Lean: https://github.com/annenkov/two-level

Steps to build
==============

* Clone this repo.
* Install `docker`.
* In the terminal, go to the directory you cloned this repo and run (notice `.` at the end) `docker build -t lean-image .`
* After building step is complete (this might take some time), run `docker run -it lean-image` to connect your current terminal session to the container.
* In the container, type `emacs ~/two-level/fibrantlimits.lean` to start editing `fibrantlimits.lean` with the lean-mode in Emacs.

Interacting with the Lean development
=====================================

As we have said before, the docker image comes with Emacs and lean-mode. The lean-mode provides syntax highlighting and allows to interactively develop proofs. 
Use <kbd>C-c C-g</kbd> to show goal in tactic proof, <kbd>C-c C-p</kbd> to print information about identifier, <kbd>C-c C-t</kbd> to show type, and <kbd>C-c C-l</kbd> to comple a lean file.

Alternatively, one can use the command line to compile the project or individual files:

* After executing `docker run -it lean-image`, change directory to our Lean development `cd ~/two-level`.
* Run `make clean` to clean previously compiled files
* Run `make` again to rebuild the project.
* Individual files can be compiled using `lean <filename.lean>`.

The image comes with the preinstalled `nano` editor that can be used to view/edit the source files (but without syntax highlighting). Other editors can be installed, if required, using the `apt-get` command. For example, `apt-get install vim`.
