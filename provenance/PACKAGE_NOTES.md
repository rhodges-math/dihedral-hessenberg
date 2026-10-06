# Source scope and verification

This repository contains the 711-module Lean library `Schubert`: 74 modules of
`Schubert/Splines/` (generalized splines), 265 modules of `Schubert/Dihedral/` (dihedral groups,
their roots, invariants and representations), 69 modules of `Schubert/FiniteGroupCharacters/`
(graded representations of finite groups) and 303 modules of `Schubert/DihedralSplines/` (the
paper). The modules of `Schubert/Splines/`, `Schubert/Dihedral/` and
`Schubert/FiniteGroupCharacters/` never import `Schubert/DihedralSplines/`, and `Schubert/Splines/`
does not import `Schubert/Dihedral/`. All local imports are included, and every module is in the
import closure of `Schubert.DihedralSplines.Audit`. Mathlib (`b2bf051`) and Tau Ceti (`48fe7a5`)
are pinned public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged, except
`Schubert/DihedralSplines/Audit.lean`, which is generated for this release from the statement
index: for every statement of the paper listed in `docs/STATEMENTS.md`, it prints the signature and
the axioms of each declaration that formalizes it. `LOCAL_MODULES.json` records, for every module,
the path and hash in this release, with `origin_kind` `unchanged` (710) or `generated` (1).

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of the
  `Schubert` modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of `Schubert/DihedralSplines/Audit.lean`.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.
