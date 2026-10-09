# Source scope and verification

This repository contains the 711-module Lean library `DihedralHessenberg`: 74 modules of
`DihedralHessenberg/Splines/` (generalized splines), 265 modules of `DihedralHessenberg/Dihedral/`
(dihedral groups, their roots, invariants and representations), 69 modules of
`DihedralHessenberg/FiniteGroupCharacters/` (graded representations of finite groups) and 303
modules of `DihedralHessenberg/Paper/` (the paper). The modules of `DihedralHessenberg/Splines/`,
`DihedralHessenberg/Dihedral/` and `DihedralHessenberg/FiniteGroupCharacters/` never import
`DihedralHessenberg/Paper/`, and `DihedralHessenberg/Splines/` does not import
`DihedralHessenberg/Dihedral/`. All local imports are included, and every module is in the import
closure of `DihedralHessenberg.Paper.Audit`. Mathlib (`b2bf051`) and Tau Ceti (`48fe7a5`) are pinned
public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged, except
`DihedralHessenberg/Paper/Audit.lean`, which is generated for this release from the statement
index: for every statement of the paper listed in `docs/STATEMENTS.md`, it prints the signature and
the axioms of each declaration that formalizes it. `LOCAL_MODULES.json` records, for every module,
the path and hash in this release, with `origin_kind` `unchanged` (710) or `generated` (1).

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of the
  `DihedralHessenberg` modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of `DihedralHessenberg/Paper/Audit.lean`.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.
