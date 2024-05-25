<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Notes on Algebra

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/motrellin/comoalg/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/motrellin/comoalg/actions/workflows/docker-action.yml


[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://motrellin.github.io/comoalg/./docs/toc.html


This projects aims to state some standard algebraic concepts.
It should also serve as a personal collection of notes.


## Meta

- Author(s):
  - Max Ole Elliger (initial)
- License: [GNU General Public License v3.0 or later](LICENSE)
- Compatible Coq versions: Developed for 8.19.0
- Additional dependencies: none
- Coq namespace: `CoMoAlg`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Notes on Algebra
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-comoalg
```

To instead build and install manually, do:

``` shell
git clone --recurse-submodules https://github.com/motrellin/comoalg.git
cd comoalg
make all  # or make -j <number-of-cores-on-your-machine> all
make install
```
