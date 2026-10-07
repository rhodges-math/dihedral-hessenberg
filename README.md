# Lean verification of *Dot actions and Hessenberg spaces for dihedral groups*

This repository, `rhodges-math/dihedral-hessenberg`, contains a Lean 4
formalization of *Dot actions and Hessenberg spaces for dihedral groups*
(Jonathan Boretsky, Reuven Hodges, Nathan Lesnevich, Tyrrell McAllister, and
Joseph Pappe, 2026).

All results of the paper are formalized. For the dihedral group $I\_2(n)$,
$n \ge 3$, and every Hessenberg space $H$, the formalization proves that the
module of splines
$\mathcal{M}\_H$ is free over $\mathbb{C}\[x,y\]$, with palindromic rank
generating function $P\_H(q) = \sum\_w q^{\ell\_H(w)}$ and Hilbert series
$P\_H(q)/(1-q)^2$ (Theorem 1); it constructs an explicit homogeneous flow-up
basis, each element of which is a Schubert spline or is given by the displayed
product formula (Theorem 2); and it determines the left and right dot action
representations $\mathrm{L}\_H$ and $\mathrm{R}\_H$ in the graded representation
ring of $I\_2(n)$ (Theorem 3). Every other statement of the paper is formalized
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

#check HessenbergIdeal.poincare_hilbert
#check FlowupSpline.basis_explicit
#check HessenbergIdeal.Left.graded_class
#check HessenbergIdeal.Right.graded_class
#check Pentagon.not_permutation
```

Names below are relative to the namespace `Schubert`. Throughout, `n : ℕ`
comes with a proof `hthree : 3 ≤ n`, and a Hessenberg space $H$ is
`ideal : DihedralSplines.HessenbergIdeal n hthree`, whose set of roots is
`ideal.toRootSubset`.

### Notation

The group acts on $\mathbb{R}^2$ and on $\mathbb{C}\[x,y\]$ as in Section 2 of
the paper. The positive roots are the unit vectors with $\alpha\_{2k+1}$ at angle
$k\pi/n$ and $\alpha\_{2k+2}$ at angle $(n-1-k)\pi/n$, the embedding of
Example 2.3, so that $(s\_1s\_2)^ks\_1=s\_{\alpha\_{2k+1}}$ and
$(s\_2s\_1)^ks\_2=s\_{\alpha\_{2k+2}}$.

| Paper | Lean |
| --- | --- |
| $I\_2(n)$, $s\_1$, $s\_2$ | `DihedralGroup n` (Mathlib), `DihedralGroup.sr 0`, `DihedralGroup.sr 1` |
| $\ell(w)$, the Bruhat order $u \le v$ | `Dihedral.length n hthree w`, `Dihedral.BruhatLE n hthree u v` |
| $\Phi^+$, the root $\alpha\_i$ | `Dihedral.positiveRoots n`, `Dihedral.positiveRoot n i` (with `i = 0, …, n-1` for $\alpha\_1,\dots,\alpha\_n$) |
| $s\_\gamma$, $t\_\gamma$ for $\gamma \in \Phi^+$ | `γ.reflection`, `γ.form`, for `γ : Dihedral.PositiveRoot n` |
| $\mathbb{C}\[x,y\]$, its action $f \mapsto w(f)$ | `Dihedral.CoordinatePolynomial`, `Dihedral.polynomialAction n w` |
| The root poset (Definition 2.6) | `DihedralSplines.RootOrder n hthree` |
| A Hessenberg space $H$ | `DihedralSplines.HessenbergIdeal n hthree` |
| $\ell\_H(w)$, $P\_H(q)$ | `ideal.toRootSubset.length w`, `ideal.lengthPolynomial` |
| $\mathcal{M}\_H$ | `ideal.toRootSubset.Spline` |
| The module structures (4) and (5) | `Dihedral.RootSubset.leftAlgebra`, `Dihedral.RootSubset.rightAlgebra` |
| $(\mathcal{M}\_H)\_d$ | `ideal.toRootSubset.piece d` |
| $w \cdot \overline{\rho}$ | `ideal.toRootSubset.dot hthree w ρ` |
| $\mathrm{L}\_H$, $\mathrm{R}\_H$ | `Dihedral.RootSubset.Left.Quotient`, `Dihedral.RootSubset.Right.Quotient` |

### Theorem 1: freeness, rank generating function and Hilbert series

For $n \ge 3$ and every Hessenberg space $H$, the module $\mathcal{M}\_H$ is free
over $\mathbb{C}\[x,y\]$; its rank generating function is palindromic and equal to

$$
P\_H(q)=\sum\_{w\in I\_2(n)}q^{\ell\_H(w)},
$$

where $\ell\_H(w)$ is the number of roots in $H$ sent to $\Phi^-$ by $w$; and

$$
\mathrm{Hilb}(\mathcal{M}\_H;q)=\frac{P\_H(q)}{(1-q)^2}.
$$

This is proved for both module structures of the paper: multiplication by
constant splines (Equation (4)) and by orbit splines (Equation (5)). The rank
generating function is the generating function of the dimensions of the graded
pieces of $\mathcal{M}\_H/(x,y)\mathcal{M}\_H$, which for a free module counts
the basis elements in each degree, and the Hilbert series is the formal power
series $\sum\_d \dim\_{\mathbb{C}}(\mathcal{M}\_H)\_d\\,q^d$.

These declarations are in `Schubert.DihedralSplines`
([FlowupBasis.lean](Schubert/DihedralSplines/FlowupBasis.lean),
[FlowupHilbert.lean](Schubert/DihedralSplines/FlowupHilbert.lean)).

| Declaration | Result |
| --- | --- |
| `HessenbergIdeal.poincare_hilbert` | All of Theorem 1, for both module structures |
| `FlowupSpline.Left.free`, `FlowupSpline.Right.free` | $\mathcal{M}\_H$ is free |
| `FlowupSpline.Left.rank_eq`, `FlowupSpline.Right.rank_eq` | The rank generating function is $P\_H(q)$ |
| `HessenbergIdeal.lengthPolynomial_reverse` | $P\_H$ is palindromic |
| `HessenbergIdeal.hilbertSeries_formula` | $\mathrm{Hilb}(\mathcal{M}\_H;q)=P\_H(q)/(1-q)^2$ |
| `HessenbergIdeal.hilbertSeries_coeff` | The coefficients of the Hilbert series are the dimensions of the $(\mathcal{M}\_H)\_d$ |
| `HessenbergIdeal.lengthPolynomial_even`, `HessenbergIdeal.lengthPolynomial_odd` | The explicit forms of $P\_H$ in Corollary 4.7 |

### Theorem 2: the flow-up basis

There is a homogeneous basis $\lbrace\overline{\rho}\_w \mid w \in I\_2(n)\rbrace$
of $\mathcal{M}\_H$, with $\deg \overline{\rho}\_w = \ell\_H(w)$, such that each
$\overline{\rho}\_w$ is either a Schubert spline or has the form

$$
\overline{\rho}\_w(v)=
\begin{cases}
d^w(v)\displaystyle\prod\_{\alpha\in H,\ vs\_\alpha\notin G\_w} t\_{v(\alpha)}, & v\in G\_w,\\
0, & v\notin G\_w,
\end{cases}
$$

where $G\_w$ contains $w$ and is contained in its Bruhat upper ideal, and
$d^w(v)\in\mathbb{C}^\times$ for every $v\in G\_w$.

The basis is the family of flow-up splines $\overline{\rho}\_w$ constructed
recursively in Theorem 4.5: at each $w \ne e, w\_0$ the construction follows the
simple left ascent $s\_\alpha$ of $w$ and takes a restricted Schubert spline, a
divided difference $\partial\_\alpha$, or a dot translate $s\_\alpha \cdot$,
according to the cases of the theorem. It is a basis for both module
structures. The Schubert splines are the splines $\overline{\sigma}\_w$ of the
case $H = \Phi^+$, which are splines for every $H$. The second alternative is
recorded by the structure `DihedralSplines.BoundaryForm`, which carries the set
$G\_w$, the constants $d^w(v)$ and the displayed formula. For $n = 5$ and
$H = \lbrace\alpha\_1,\alpha\_2,\alpha\_3\rbrace$, the ten splines displayed in
Example 4.6 are exactly the splines of this construction
(`Pentagon.generator_eq_spline`).

These declarations are in `Schubert.DihedralSplines`
([FlowupExplicitBasis.lean](Schubert/DihedralSplines/FlowupExplicitBasis.lean),
[FlowupRecursion.lean](Schubert/DihedralSplines/FlowupRecursion.lean),
[FlowupEquations.lean](Schubert/DihedralSplines/FlowupEquations.lean)).

| Declaration | Result |
| --- | --- |
| `FlowupSpline.basis_explicit` | All of Theorem 2, for both module structures |
| `FlowupSpline.spline` | The flow-up spline $\overline{\rho}\_w$ |
| `FlowupSpline.spline_one`, `spline_top`, `spline_low`, `spline_high`, `spline_no_edge` | The cases of the recursion of Theorem 4.5 |
| `FlowupSpline.Left.basis`, `FlowupSpline.Right.basis` | The bases, with `basis_apply` identifying their vectors |
| `FlowupSpline.homogeneous`, `FlowupSpline.degree` | $\overline{\rho}\_w$ is homogeneous of degree $\ell\_H(w)$ |
| `FlowupSpline.support`, `FlowupSpline.diagonal` | $\overline{\rho}\_w$ vanishes off the Bruhat upper ideal of $w$ and $\overline{\rho}\_w(w)\ne0$ |
| `FlowupSpline.shape`, `BoundaryForm.formula`, `BoundaryForm.coefficient_ne` | Each $\overline{\rho}\_w$ is a Schubert spline or has the displayed form |
| `FlowupSpline.block_shape` | The supports $G\_w$ of Proposition 5.3 |
| `Pentagon.generator_eq_spline`, `Pentagon.operator_formulas` | Example 4.6 |

| Paper | Lean |
| --- | --- |
| $\overline{\rho}\_w$ | `FlowupSpline.spline ideal w` |
| $\overline{\sigma}\_w$, as a spline for $H$ | `ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree w)` |
| $\partial\_\alpha$ | `HessenbergIdeal.dividedDifference` |
| $G\_w$, $d^w$ | the fields `vertices` and `coefficient` of `BoundaryForm ideal w (FlowupSpline.spline ideal w)` |

### Theorem 3: the dot action representations

Let $H \subsetneq \Phi^+$ be a Hessenberg space containing the simple roots
$\lbrace\alpha,\beta\rbrace$, let $h = \lfloor |H|/2 \rfloor$, and if $|H|$ is
odd let $\alpha$ be the $H$-dominant simple root. Then, in the graded
representation ring of $I\_2(n)$,

$$
\mathrm{L}\_H \cong
\begin{cases}
(1+q)(1+q+\cdots+q^{2h-1})\\,\mathbf{1} \oplus q^h\bigl(C\_\alpha \oplus C\_\beta - \mathsf{P}\_h - \mathsf{P}\_{h-1}\bigr), & |H| = 2h,\\
(1+q)(1+q+\cdots+q^{2h})\\,\mathbf{1} \oplus (q^h+q^{h+1})\bigl(C\_\alpha - \mathsf{P}\_h\bigr), & |H| = 2h+1,
\end{cases}
$$

$$
\mathrm{R}\_H \cong
\begin{cases}
\mathsf{Co}\_H \oplus q^h\bigl(C\_\alpha \oplus C\_\beta - \mathsf{P}\_h - \mathsf{P}\_{h-1}\bigr), & |H| = 2h,\\
\mathsf{Co}\_H \oplus q^h\bigl(C\_\alpha - \mathsf{P}\_h\bigr) \oplus q^{h+1}\bigl(C\_\beta - \mathsf{P}\_h\bigr), & |H| = 2h+1.
\end{cases}
$$

Here $\mathrm{L}\_H$ and $\mathrm{R}\_H$ are the quotients of $\mathcal{M}\_H$ by
the left and by the right coordinate splines, graded by degree, with the
action induced by the dot action. The formalization states each formula as an
equality of power series $\sum\_d \[(\mathrm{L}\_H)\_d\]\\,q^d$ with coefficients
in the representation ring `TauCeti.repRing ℂ (DihedralGroup n)`, the split
Grothendieck ring of finite-dimensional complex representations; two graded
representations have equal series exactly when they are isomorphic in every
degree (`FiniteGroupCharacters.gradedClass_eq_iff_iso`). The hypotheses are
those of the paper: $H$ is proper, $\alpha,\beta$ are the two simple roots in
either order, and $\alpha$ is $H$-dominant when $|H|$ is odd. The case
$H = \Phi^+$ is Propositions 3.8 and 3.9, below.

These declarations are in `Schubert.DihedralSplines`
([QuotientClass.lean](Schubert/DihedralSplines/QuotientClass.lean)).

| Declaration | Result |
| --- | --- |
| `HessenbergIdeal.Left.graded_class` | The formula for $\mathrm{L}\_H$ (Theorem 6.4) |
| `HessenbergIdeal.Right.graded_class` | The formula for $\mathrm{R}\_H$ (Theorem 7.3) |
| `HessenbergIdeal.Left.graded_class_even`, `graded_class_odd`, and the same for `Right` | The two cases $\lvert H\rvert = 2h$ and $\lvert H\rvert = 2h+1$ |
| `HessenbergIdeal.Left.class_palindromic` | The classes of $(\mathrm{L}\_H)\_d$ and $(\mathrm{L}\_H)\_{\lvert H\rvert-d}$ agree |
| `HessenbergIdeal.dominant_even`, `HessenbergIdeal.dominant_odd_unique` | Both simple roots are $H$-dominant when $\lvert H\rvert$ is even, and exactly one is when $\lvert H\rvert$ is odd (Remark 6.3) |

| Paper | Lean |
| --- | --- |
| $\sum\_d \[(\mathrm{L}\_H)\_d\]\\,q^d$, $\sum\_d \[(\mathrm{R}\_H)\_d\]\\,q^d$ | `Dihedral.RootSubset.Left.gradedClass`, `Dihedral.RootSubset.Right.gradedClass` |
| $\mathbf{1}$, $V\_j$ | the trivial representation, `Dihedral.frequencyFDRep n j` |
| $C\_\gamma$, the permutation representation on the cosets of $\langle s\_\gamma\rangle$ | `γ.cosetFDRep` |
| $\mathsf{P}\_h = \mathbf{1} \oplus V\_1 \oplus \cdots \oplus V\_h$ | `Dihedral.Frequency.partialSum n h` |
| $\mathsf{Co}\_H$ (Lemma 7.2) | `DihedralSplines.HessenbergIdeal.coClass ideal` |
| $\alpha$ is $H$-dominant (Definition 6.2) | `DihedralSplines.HessenbergIdeal.IsDominant ideal α` |

### The Schubert case

For $H = \Phi^+$, Section 3 of the paper treats the Schubert splines
$\overline{\sigma}\_w$ from first principles. They are defined by the recursion
of Equation (11) and given explicitly by Theorem 3.4,

$$
\overline{\sigma}\_w(v) = d^w(v) \prod\_{s\_\gamma v < v,\ s\_\gamma v \not\ge w} t\_\gamma,
\qquad d^w(v) \in \mathbb{C}^\times \text{ if } w \le v,\quad d^w(v) = 0 \text{ otherwise}.
$$

They form a homogeneous basis of $\mathcal{M}\_{\Phi^+}$ (Proposition 3.5), and
$\mathrm{Hilb}(\mathcal{M}\_{\Phi^+};q) = (1+q)(1+q+\cdots+q^{n-1})/(1-q)^2$
(Corollary 3.6). The map
$\Psi\colon \mathbb{C}\[x,y\]\otimes\_{\mathbb{C}\[x,y\]^{I\_2(n)}}\mathbb{C}\[x,y\]\to\mathcal{M}\_{\Phi^+}$,
$\Psi(f\otimes h)(w) = f\\,w(h)$, is an isomorphism of graded algebras under
which the dot action is $u\cdot(f\otimes h) = u(f)\otimes h$ (Lemma 3.7).
Consequently $\mathrm{L}\_{\Phi^+}$ is a sum of trivial representations, one in
degree $\ell(w)$ for each $w$ (Proposition 3.8), and $\mathrm{R}\_{\Phi^+}$ is
the coinvariant algebra (Proposition 3.9).

| Declaration | Result |
| --- | --- |
| `DihedralSplines.SchubertSpline.spline`, `SchubertSpline.spline_step` | $\overline{\sigma}\_w$ and the recursion (11) |
| `SchubertSpline.rational_formula`, `SchubertSpline.support_exact` | Theorem 3.4 |
| `SchubertSpline.left_basis`, `SchubertSpline.right_basis` | Proposition 3.5 |
| `SchubertSpline.hilbert_formula` | Corollary 3.6 |
| `DihedralSplines.borelEquiv`, `borelEquiv_tmul`, `borelEquiv_dot` | Lemma 3.7 |
| `HessenbergIdeal.Left.full_piece_iso`, `SchubertSpline.left_class_geometric` | Proposition 3.8 |
| `SchubertSpline.right_piece_iso`, `SchubertSpline.rightTrace_formula` | Proposition 3.9, with the graded trace $\frac{(1-q^2)(1-q^n)}{\det(I-qV\_1(g))}$ |

### Corollary 6.11: the left representation need not be a permutation representation

For $n = 5$ and $H = \lbrace\alpha\_1,\alpha\_2,\alpha\_3\rbrace$, forgetting the
grading, $\mathrm{L}\_H \cong \mathbf{1}^{\oplus 6} \oplus V\_2^{\oplus 2}$, whose
character at the rotation $r$ is $5-\sqrt5$. The formalization proves that
$\mathrm{L}\_H$ is not isomorphic to the permutation representation
$\mathbb{C}\[X\]$ of any finite $I\_2(5)$-set $X$ (`Pentagon.not_permutation`),
together with the decomposition (`Pentagon.whole_iso`) and the character value
(`Pentagon.rotation_character`)
([PentagonRepresentation.lean](Schubert/DihedralSplines/PentagonRepresentation.lean)).

### Every other statement

The remaining lemmas, propositions, corollaries, definitions, displayed
equations, examples and remarks, and the statements made in the prose and
figures of the paper, are listed with their Lean declarations in
[docs/STATEMENTS.md](docs/STATEMENTS.md).

## Libraries

The Lean library `Schubert` is divided into four parts. The first three are
general and do not import the fourth, which contains the paper.

### The Splines library

[Schubert/Splines/](Schubert/Splines) (namespace `Splines`, 74 files) develops
generalized splines. On a graph whose edges are labelled by ideals of a
commutative ring, a spline is a function on the vertices whose values at the
two ends of each edge differ by an element of its label. For a group acting on
a polynomial ring and a set of reflections, the reflection graphs carry the
constant and orbit module structures, the grading, the dot action and the two
quotients by the coordinate splines. The library proves that triangular
families are bases, finiteness over Noetherian rings, uniqueness of supported
splines of minimal degree, and the facts on minimal generating sets and
Hilbert series that the paper uses.

| Declaration | Result |
| --- | --- |
| `Splines.IdealLabeledGraph.Spline` | The splines on a graph with ideal labels |
| `Splines.IdealLabeledGraph.linearIndependent_of_triangular` | A triangular family of splines with nonzero diagonal is linearly independent |
| `Splines.IdealLabeledGraph.triangularBasis` | A triangular family whose diagonal entries divide the residual values is a basis |
| `Splines.IdealLabeledGraph.spline_finite` | The splines on a finite graph form a finite module over a Noetherian ring |
| `Splines.ReflectionGraphData.leftSpline_finite`, `rightSpline_finite` | Finiteness for both module structures of reflection splines |
| `Splines.ReflectionGraphData.dot` | The dot action on reflection splines |
| `Splines.IdealLabeledGraph.eq_of_base_eq_of_minimal_supported` | A supported spline of minimal degree is determined by its value at one vertex |
| `Splines.minimal_generators_finite` | Minimal generating sets of a module with a finite basis are finite |
| `Splines.galoisTensorEquiv` | $L \otimes\_K L \cong \prod\_{g\in G} L$ for a finite Galois extension $L/K$ with group $G$ |

### The Dihedral library

[Schubert/Dihedral/](Schubert/Dihedral) (namespace `Dihedral`, 265 files)
develops the dihedral groups $I\_2(n)$, $n \ge 3$, as Mathlib's
`DihedralGroup n`: the Coxeter presentation, reduced words, the length function
and the Bruhat order; the realization on $\mathbb{R}^2$ and $\mathbb{C}^2$,
roots, reflections and inversion sets; the action on $\mathbb{C}\[x,y\]$, its
invariants, the coinvariant algebra and its graded representation; and the
irreducible and coset permutation representations.

| Declaration | Result |
| --- | --- |
| `Dihedral.coxeterSystem` | $I\_2(n)$ is the Coxeter group of rank two generated by $s\_1, s\_2$ |
| `Dihedral.bruhatLE_iff_exists_sublist` | The Bruhat order is the subword order |
| `Dihedral.Invariants.eq_generator_adjoin` | The invariant algebra is generated by invariants of degrees $2$ and $n$ |
| `Dihedral.basicInvariants_algebraicIndependent`, `Dihedral.nonempty_invariantPolynomialEquiv` | These invariants are algebraically independent, and the invariant algebra is a polynomial ring |
| `Dihedral.Invariants.polynomial_free`, `Dihedral.Invariants.polynomial_finrank` | $\mathbb{C}\[x,y\]$ is free of rank $2n$ over the invariants |
| `Dihedral.Coinvariant.regular_iso` | The coinvariant algebra is the regular representation |
| `Dihedral.irreducible_classification`, `Dihedral.irreducible_dimension` | Every irreducible complex representation is isomorphic to exactly one of the listed irreducibles, of dimension one or two |
| `Dihedral.PositiveRoot.coset_odd_iso`, `Dihedral.PositiveRoot.coset_even_iso` | The decomposition of $C\_\gamma$ into irreducibles (Equation (3)) |
| `Dihedral.self_dual` | Every finite-dimensional complex representation is self-dual |

### The FiniteGroupCharacters library

[Schubert/FiniteGroupCharacters/](Schubert/FiniteGroupCharacters) (namespace
`FiniteGroupCharacters`, 69 files) develops graded representations of finite
groups: their graded characters and their classes in the representation ring
of Tau Ceti, equivariant sections, permutation representations spanned by
independent orbits, and tensor products with polynomial rings.

| Declaration | Result |
| --- | --- |
| `FiniteGroupCharacters.gradedClass` | The series $\sum\_d \[V\_d\]\\,q^d$ of a graded representation |
| `FiniteGroupCharacters.gradedClass_eq_iff_iso` | Equal series exactly when the graded pieces are isomorphic |
| `FiniteGroupCharacters.gradedClass_eq_iff` | In characteristic zero, equal series exactly when the graded characters are equal |
| `FiniteGroupCharacters.equivariant_section` | A surjective intertwiner of a finite group of invertible order has an equivariant section |
| `FiniteGroupCharacters.class_eq_of_multiplicities` | A complete family of simple representations determines classes by multiplicities |
| `FiniteGroupCharacters.PermutationSpan.iso` | An independent equivariant family spans a copy of its permutation representation |

### The paper

[Schubert/DihedralSplines/](Schubert/DihedralSplines) (namespace
`DihedralSplines`, 303 files) contains the splines of Hessenberg spaces for
$I\_2(n)$ and every result of the paper, as described above.

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
this code, please cite this repository; citation metadata is in
[CITATION.cff](CITATION.cff). The repository contains no third-party source
files; Mathlib, Tau Ceti and their dependencies are downloaded by Lake and keep
their own licenses (see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)).
