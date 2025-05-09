# Binding Technique Expriments

This repository contains experiments with different (automatic) binding techniques (`ott + lngen`, `autosubst2`) in proving simple properties (type safety) for some simple type systems (STLC, System F, Fsub).

## Overview

`README.v` is a comprehensive entry file that lists all the mechanized properties.

`*/autosubst2/language.sig` contains the syntax definition for `autosubst2`, and `*/autosubst2/def_as2.v` contains the generated Coq definitions.

`*/lngen/language.ott` contains the syntax definition for `ott + lngen`, and `*/lngen/def_ott.v` contains the definitions the generated Coq definitions and `*/lngen/prop_ln.v` contains the generated Coq properties.

## Usage

### Dependency

(Recommended): use `opam switch` to create a new opam environment.

- `coq-8.19.2`

```bash
opam pin add coq 8.19.2
```

- [`Metalib`](https://github.com/plclub/metalib) (tested on version dev)

```bash
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-metalib
```

- [`CoqHammer`](https://github.com/lukaszcz/coqhammer) (tested on version 1.3.2)

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer-tactics
```

(The following dependencies are not required if you only want to check the proofs.)

- [`ott`](https://github.com/ott-lang/ott)  (tested on version 0.34)

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ott
```

- [`lngen`](https://github.com/plclub/lngen) (tested on version 0.3.2)

Please follow the instruction in its repository.

- [`autosubst-ocaml`](https://github.com/uds-psl/autosubst-ocaml) (tested on version 1.1)

```bash
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam install coq-autosubst-ocaml
```

### Proof-checking

The Coq definitions generated by `ott + lngen` and `autosubst2` are already provided in the repository. You can run the following commands to check the proofs without installing them:

- Run `make coq-only` to check the proof.

### Regenerating Defs

If you would like to regenerate the definitions using `language.ott` and `language.sig`, you can run the following commands:

- Run `make ott` and `make lngen` to regenerate the Coq definitions using `ott + lngen`.

- Run `make autosubst2` to regenerate the Coq definitions using `autosubst2`.
