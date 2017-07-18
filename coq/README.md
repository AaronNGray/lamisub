# Coq Formalization of "Unifying Typing and Subtyping"

## Getting Started Guide

The repository consists of Coq proofs of the paper. Its correctness can
be checked by the Coq theorem prover (version 8.6). The repository
passes the test if all Coq files can be compiled without any error
messages, which indicates Coq proofs are machine-checked without
issues. The following guide is to prepare the environment to compile
(i.e. check) Coq files.

We put main lemmas proved across the Coq files altogether in the index
file [`Index.v`](Index.v) for easy searching. Notice that there is no `admit`
or `Admitted` tactics in our Coq proofs, which are used to skip proof
goals leading to incomplete proofs. This can be verified by executing
the following Unix shell command in the unpacked repository folder:

    ls *.v | xargs grep -y admit

There should be no output, which means there is no `admit` or
`Admitted` found in Coq proofs.

The repository supports to build
with [*Docker*](https://www.docker.com/), a lightweight and
cross-platform virtualization software, which can provide all
necessary build tools easily. We recommend to test the repository using
Docker, but we also provide a guide for non-Docker users who prefer
the traditional environment.

You may need a recent Docker version (>= 1.8). The installation of
Docker is omitted in this guide, which can be found on the [Docker's
official website](https://www.docker.com/community-edition#/download).

### Guide via pre-built Docker image (simplest, recommended)

This guide works with any platform with Docker installed, including
Windows and macOS.

1. Download the pre-built Docker image from Docker Hub:

        docker pull ypyang/lamisub

    The image to download is ~300 megabytes.

2. Start a shell from the image:

        docker run -it --rm ypyang/lamisub

3. Test the repository:

        make distclean && make
    
    The compilation will finish in several minutes. It takes ~3
    minutes on an Intel Core i7-6500U laptop.

### Guide via self-building Docker image

This guide works with any platform with Docker and Unix command line
utilities. For Windows, you may need Msys2 or Cygwin to support
commands like `tar` and `make`.

1. Unpack and change directory to the repository package:

        wget https://bitbucket.org/ypyang/oopsla17/get/master.tar.gz
        tar zxvf master.tar.gz
        cd ypyang-oopsla17-*/coq

2. Build Docker image from the repository:

        make dockerbuild

    This command will automatically download all necessary build tools
    and compile (i.e. test) the repository. If you want to check the
    content of the image, you can start a shell from the image by the
    following command:

        make docker


### Guide without Docker:

The dependencies for compilation are as follows:

- Coq 8.6
- GNU Make
- Perl 5
- Ott 0.25 (**optional**, requires Git and OCaml)

We use the latest Debian stable release (9.0, Stretch) as an
example. Steps are similar for other Linux distros, Unix-like systems
(e.g., macOS and BSD) and Cygwin (for Windows).

1. Install prerequisites (Coq 8.6, GNU Make, Perl 5):

        sudo apt-get update
        sudo apt-get install coq make perl

2. Compile the Ott tool (**optional**, requires OCaml and Git):

        sudo apt-get install ocaml-nox git
        git clone https://github.com/ott-lang/ott.git
        cd ott && git checkout 0.25 && make world
        sudo cp bin/ott /usr/local/bin/

    Ott tool is for generating Coq definition files (`*_ott.v`) from
    Ott source files (`*.ott`). The repository already contains
    pre-generated Coq definitions.

3. Unpack and change directory to the repository package:

        wget https://bitbucket.org/ypyang/oopsla17/get/master.tar.gz
        tar zxvf master.tar.gz
        cd ypyang-oopsla17-*/coq

4. Test the repository (without re-generating definition files):

        make

    or optionally if you have Ott tool compiled for re-generating all
    Coq definition files:

        make distclean && make


## Step by Step Instructions

The repository contains all proofs (except for the completeness theorem
over System $F_\leq$ in Section 6) which are mechanized and
machine-checked in the Coq theorem prover. Main results of the paper
are organized in the index file [`Index.v`](Index.v). There are proofs for 3
variants of the $\lambda I_\leq$ calculus, namely `Main`, `Recur` and
`Full`, which are also used as prefixes to name files:

- The `Main` variant is the exact type system introduced in the paper
  (Section 3 and 4).
- The `Recur` variant adds general recursion and an invariant
  subtyping rule for recursive types:

        G |- A : *
        G, x<:Top:A |- e : A
        ---------------------------------
        G |- (/x:A . e) <: (/x:A . e) : A

    which corresponds to the discussion in "Recursion and Recursive
    Types" of Section 7.
- The `Full` variant uses a full contravariant subtyping rule for Pi
  types, which subsumes the subtyping rule of universal types in Full
  System $F$:

        G |- A' <: A : *             G |- e' <: e : A
        G, x<:e':A' |- B <: B' : *
        G, x<:e:A |- B : *               G |- A : *
        G |- e : A                       G |- e' : A'
        ----------------------------------------------
        G |- (Pi x<:e:A . B) <: (Pi x<:e':A' . B') : *

    This variant corresponds to the discussion in "Full
    Contravariance of Function Types" of Section 7 (revised version).

Each variant contains 1 Ott definition and 3 Coq files (`@` stands for
the name of variant):

- `@.ott` is the Ott definition of type systems which is written in
  readable ASCII text, including syntax (Section 3.1), operational
  semantics (Section 3.2) and static semantics (Section 3.3). For
  details of Ott syntax, please refer to
  its [website](http://www.cl.cam.ac.uk/~pes20/ott/)
  or [developer page](https://github.com/ott-lang/ott).

- `@_ott.v` is the Coq definition file generated from `@.ott` file
  using *locally nameless representation*.
- `@_Infra.v` is the infrastructure file, which contains basic
  supporting lemmas for locally nameless representation.
- `@_Proofs.v` is proofs for the metatheory (Section 4), including
  transitivity and type safety.

There are two more files starting with `Alg` which are proofs for the
algorithmic system (Section 5). `Alg_Aux.v` is an auxiliary system
with separate definitions of typing and subtyping. `Alg_Proofs.v`
contains the definition of algorithmic system (in the extended paper). The
results of soundness and completeness to the declarative system
(Section 5) can be found at the end of the file.

The folder `tlc` contains the "TLC" Coq library written by Arthur
Charguéraud, et al. for supporting locally nameless
representation. Detailed version and license information is included
in [`tlc/README.md`](tlc/README.md).

For the concrete correspondence between the system and Coq
implementation, please refer to Appendix A of the paper.
