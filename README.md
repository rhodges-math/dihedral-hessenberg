# Lean verification of *Dot actions and Hessenberg spaces for dihedral groups*

This repository, `rhodges-math/dihedral-hessenberg`, contains a Lean 4
formalization of *Dot actions and Hessenberg spaces for dihedral groups*
(Jonathan Boretsky, Reuven Hodges, Nathan Lesnevich, Tyrrell McAllister, and
Joseph Pappe, 2026).

It formalizes the whole paper. For the dihedral group $I_2(n)$, $n \ge 3$, and
every Hessenberg space $H$, it proves that the module of splines
$\mathcal{M}_H$ is free over $\mathbb{C}[x,y]$, with palindromic rank
generating function $P_H(q) = \sum_w q^{\ell_H(w)}$ and Hilbert series
$P_H(q)/(1-q)^2$ (Theorem 1); it constructs an explicit homogeneous flow-up
basis, each element of which is a Schubert spline or is given by the displayed
product formula (Theorem 2); and it determines the left and right dot action
representations $\mathrm{L}_H$ and $\mathrm{R}_H$ in the graded representation
ring of $I_2(n)$ (Theorem 3). Every other statement of the paper is formalized
as well: its lemmas, propositions, corollaries, definitions, displayed
equations, examples and remarks, and the claims made in its prose and figures,
103 statements in all, listed in [docs/STATEMENTS.md](docs/STATEMENTS.md).

These results are proved with no hypotheses beyond Lean's standard axioms. The
development uses Lean **4.35.0-rc3**, a pinned version of **Mathlib**, and the
**Tau Ceti** library. Lean 4.35.0-rc3 is a release candidate; the pin may move
to the stable Lean 4.35.0 release.

Three of its four libraries are independent of the paper and may be of use
beyond it: generalized splines, the dihedral groups with their roots,
invariants and representations, and graded representations of finite groups;
see [Libraries](#libraries).

## AI assistance and verification

**I used GPT-6.1 Sol and Claude Opus 5.5 to help construct the Lean files.** I
reviewed all definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics, including the results of
the paper listed below.

The development was compiled with Lean, and the axiom dependencies of every
declaration were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main results

The entry point is
[Schubert/DihedralSplines/Main.lean](Schubert/DihedralSplines/Main.lean), which
imports every result of the paper; [docs/STATEMENTS.md](docs/STATEMENTS.md)
lists each statement of the paper with its Lean counterparts.

```lean
import Schubert.DihedralSplines.Main

open Schubert.DihedralSplines

#check HessenbergIdeal.poincare_hilbert    -- Theorem 1
#check FlowupSpline.basis_explicit         -- Theorem 2
#check HessenbergIdeal.Left.graded_class   -- Theorem 3, left representation
#check HessenbergIdeal.Right.graded_class  -- Theorem 3, right representation
```

### The objects

- **The group.** `DihedralGroup n` is Mathlib's dihedral group of order $2n$,
  with simple reflections $s_1$ = `sr 0` and $s_2$ = `sr 1`. It is a Coxeter
  group of rank two (`Schubert.Dihedral.coxeterSystem`), with its length
  function and Bruhat order (`Schubert.Dihedral.BruhatLE`).
- **The roots.** The group acts on $\mathbb{R}^2$ and on $\mathbb{C}[x,y]$ as in
  Section 2 of the paper. The positive roots are the unit vectors with
  $\alpha_{2k+1}$ at angle $k\pi/n$ and $\alpha_{2k+2}$ at angle
  $(n-1-k)\pi/n$, the embedding of Example 2.3, so that
  $(s_1s_2)^ks_1 = s_{\alpha_{2k+1}}$ and $(s_2s_1)^ks_2 = s_{\alpha_{2k+2}}$.
  A root $\gamma$ has the linear form $t_\gamma$.
- **Hessenberg spaces.** `HessenbergIdeal n hthree` is a lower order ideal of
  the root poset of Definition 2.6 (the order by the real cone of the simple
  roots) that contains both simple roots.
- **Splines.** `ideal.toRootSubset.Spline` is the algebra of functions
  $\rho : I_2(n) \to \mathbb{C}[x,y]$ with $t_{w(\alpha)} \mid \rho(w) -
  \rho(ws_\alpha)$ for all $w$ and all $\alpha \in H$. It has the two
  $\mathbb{C}[x,y]$-module structures of Equations (4) and (5) (`leftAlgebra`,
  by constant splines, and `rightAlgebra`, by orbit splines), the grading by
  homogeneous splines (`piece`), and the dot action
  $(w\cdot\rho)(v) = w(\rho(w^{-1}v))$ (`dot`).
- **The dot action representations.** $\mathrm{L}_H$ and $\mathrm{R}_H$
  (`RootSubset.Left.Quotient`, `RootSubset.Right.Quotient`) are the quotients
  of the splines by the left and by the right coordinate splines, graded and
  with the action induced by the dot action.

### Theorem 1: freeness, rank generating function and Hilbert series

```lean
theorem HessenbergIdeal.poincare_hilbert :
    (letI := ideal.toRootSubset.leftAlgebra hthree;
      Module.Free CoordinatePolynomial ideal.toRootSubset.Spline) ∧
    (letI := ideal.toRootSubset.rightAlgebra hthree;
      Module.Free CoordinatePolynomial ideal.toRootSubset.Spline) ∧
    Left.rankPolynomial ideal = ideal.lengthPolynomial ∧
    Right.rankPolynomial ideal = ideal.lengthPolynomial ∧
    ideal.lengthPolynomial.reverse = ideal.lengthPolynomial ∧
    ideal.hilbertSeries = ((ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ 2).val
```

Here `lengthPolynomial` is $P_H(q) = \sum_{w} q^{\ell_H(w)}$, where
$\ell_H(w)$ is the number of roots of $H$ sent to negative roots by $w$. The
rank generating functions `Left.rankPolynomial` and `Right.rankPolynomial` are
the Hilbert polynomials of the quotients
$\mathcal{M}_H/(x,y)\mathcal{M}_H$ for the two module structures, and
`hilbertSeries` is $\sum_d \dim_{\mathbb{C}} (\mathcal{M}_H)_d\, q^d$. The
module is free for both structures.

### Theorem 2: the flow-up basis

```lean
theorem FlowupSpline.basis_explicit :
    ∃ values : DihedralGroup n → ideal.toRootSubset.Spline,
      (∀ vertex, values vertex = spline ideal vertex) ∧
      (letI := ideal.toRootSubset.leftAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          ∀ vertex, vectors vertex = values vertex) ∧
      (letI := ideal.toRootSubset.rightAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          ∀ vertex, vectors vertex = values vertex) ∧
      ∀ vertex, values vertex ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) ∧
        ideal.toRootSubset.degree (values vertex) = ideal.toRootSubset.length vertex ∧
        (values vertex = ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree vertex) ∨
          Nonempty (BoundaryForm ideal vertex (values vertex)))
```

The basis consists of the flow-up splines $\overline{\rho}_w$ constructed
recursively in Theorem 4.5 (`FlowupSpline.spline`); it is a basis for both
module structures, and $\overline{\rho}_w$ is homogeneous of degree
$\ell_H(w)$. Each $\overline{\rho}_w$ is a Schubert spline, or a
`BoundaryForm`: a set $G_w$ that contains $w$ and lies in its Bruhat upper
ideal, and nonzero constants $d^w(v)$, with
$\overline{\rho}_w(v) = d^w(v) \prod_{\alpha \in H,\ vs_\alpha \notin G_w}
t_{v(\alpha)}$ for $v \in G_w$ and $\overline{\rho}_w(v) = 0$ otherwise.

### Theorem 3: the dot action representations

```lean
theorem HessenbergIdeal.Left.graded_class (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : Odd ideal.carrier.ncard → ideal.IsDominant alpha) :
    let half := ideal.carrier.ncard / 2
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      if Even ideal.carrier.ncard then
        (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half),
          (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
        PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep + TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half) -
            TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)))
      else
        (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half + 1),
          (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
        (PowerSeries.X ^ half + PowerSeries.X ^ (half + 1)) * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half))

theorem HessenbergIdeal.Right.graded_class (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : Odd ideal.carrier.ncard → ideal.IsDominant alpha) :
    let half := ideal.carrier.ncard / 2
    RootSubset.Right.gradedClass ideal.toRootSubset hthree =
      if Even ideal.carrier.ncard then
        ideal.coClass +
        PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep + TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half) -
            TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)))
      else
        ideal.coClass + PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half)) +
        PowerSeries.X ^ (half + 1) * PowerSeries.C
          (TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half))
```

`gradedClass` is the series $\sum_d [(\mathrm{L}_H)_d]\, q^d$ (respectively
for $\mathrm{R}_H$) of classes of the graded pieces in the representation ring
of $I_2(n)$ (`TauCeti.repRing`, the split Grothendieck ring of
finite-dimensional complex representations, in which equality of classes is
isomorphism). `alpha.cosetFDRep` is the permutation representation
$C_\alpha$ on the cosets of $\langle s_\alpha \rangle$;
`Frequency.partialSum n h` is $\mathsf{P}_h = \mathbb{1} \oplus V_1 \oplus
\dots \oplus V_h$; `ideal.coClass` is $\mathsf{Co}_H$ of Lemma 7.2; and
`IsDominant` is the $H$-dominant simple root of Definition 6.2. The case
$H = \Phi^+$, excluded by Theorem 3, is Propositions 3.8 and 3.9.

## Libraries

The Lean library `Schubert` is divided into four parts. The first three are
general and do not import the fourth.

- [`Schubert/Splines/`](Schubert/Splines) (74 files): generalized splines on
  graphs whose edges are labelled by ideals, polynomial and reflection-labelled
  graphs of a group acting on polynomials, the spline algebra with its grading
  and its constant and orbit module structures, the dot action, upper
  triangular and flow-up families and their bases, minimal generating sets, and
  Hilbert series.
- [`Schubert/Dihedral/`](Schubert/Dihedral) (265 files): the dihedral groups as
  Coxeter groups of rank two (presentation, reduced words, length, Bruhat
  order), their realization on the plane, roots, inversion sets and root
  depth, the action on polynomials, the invariants and their freeness, the
  coinvariant algebra and its graded representation, the double coinvariant
  algebra and the fixed field of the action, and the irreducible and coset
  permutation representations.
- [`Schubert/FiniteGroupCharacters/`](Schubert/FiniteGroupCharacters) (69
  files): graded representations of finite groups and their classes in the
  representation ring, characters of graded pieces, equivariant sections and
  tensor products with polynomial rings, and permutation representations.
- [`Schubert/DihedralSplines/`](Schubert/DihedralSplines) (303 files): the
  splines of Hessenberg spaces for $I_2(n)$ and every result of the paper.

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.35.0-rc3 automatically, and
`lake-manifest.json` pins Mathlib, Tau Ceti and their public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean Schubert/DihedralSplines/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper first
has Lake build the Tau Ceti modules used here, then recompiles all **711 local
Lean modules** in dependency order, and exits with a nonzero status if a
module fails. With three jobs the full build takes about an hour and a half on
a laptop.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints, for every statement of the paper in turn, the signatures of
the Lean declarations that formalize it, with their hypotheses, and their
transitive axiom dependencies. The expected axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes and the local import completeness:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `Schubert/Splines/`, `Schubert/Dihedral/`, `Schubert/FiniteGroupCharacters/`:
  the general libraries described above, each with an entry point `Main.lean`.
- `Schubert/DihedralSplines/`: the paper. The files beginning with `Paper`
  define the objects of Section 2 (splines, module structures, grading, dot
  action, quotients); `Flowup*` construct the flow-up basis of Section 4;
  `Schubert*` treat the Schubert case of Section 3; `*Class`, `Quotient*` and
  `Coinvariant*` compute the representations of Sections 6 and 7; `Triangle*`,
  `Square*`, `Pentagon*` and `Hexagon*` are the examples.
- `Schubert/DihedralSplines/Main.lean`: imports every result of the paper.
- `Schubert/DihedralSplines/Audit.lean`: the audit described above.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE).
Redistributions must retain the [NOTICE](NOTICE) file. If you use or adapt
this code, please cite the paper and this repository; citation metadata is in
[CITATION.cff](CITATION.cff). The repository contains no third-party source
files; Mathlib, Tau Ceti and their dependencies are downloaded by Lake and keep
their own licenses (see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)).
