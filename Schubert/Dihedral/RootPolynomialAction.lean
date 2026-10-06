import Mathlib.Algebra.Prime.Lemmas
import Schubert.Dihedral.RootPolynomial
import Schubert.Dihedral.RotationAction

/-!
# Root polynomial properties under the dihedral action

Algebra automorphisms preserve nonvanishing, distinct complex lines, nonassociation,
and the absence of common nonunit divisors among positive-root polynomials.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Images of root polynomials under the dihedral action do not vanish. -/
theorem polynomialAction_rootPolynomial_ne_zero (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (index : PositiveRootIndex n) :
    polynomialAction n element (rootPolynomial n index) ≠ 0 := by
  intro hzero
  apply rootPolynomial_ne_zero n index
  apply (polynomialAction n element).injective
  simpa only [map_zero] using hzero

/-- Proportional action images of root polynomials have the same root index. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.Form.action_scalar_injective (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (first second : PositiveRootIndex n) (scalar : ℂ)
    (heq : polynomialAction n element (rootPolynomial n first) =
      MvPolynomial.C scalar * polynomialAction n element (rootPolynomial n second)) :
    first = second := by
  apply rootPolynomial_scalar_mul_imp_index_eq n first second scalar
  have hinverse := congrArg (polynomialAction n element).symm heq
  have hconstant : (polynomialAction n element).symm (MvPolynomial.C scalar) =
      MvPolynomial.C scalar := by
    simpa only [MvPolynomial.algebraMap_eq] using
      (polynomialAction n element).symm.commutes scalar
  simpa only [map_mul, hconstant, AlgEquiv.symm_apply_apply] using hinverse

/-- Distinct root polynomials remain nonproportional after a common dihedral action. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.Form.action_nonproportional (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (first second : PositiveRootIndex n)
    (hne : first ≠ second) (scalar : ℂ) :
    polynomialAction n element (rootPolynomial n first) ≠
      MvPolynomial.C scalar * polynomialAction n element (rootPolynomial n second) := by
  intro heq
  exact hne (_root_.Schubert.Dihedral.IndexedRoots.Form.action_scalar_injective
    n element first second scalar heq)

/-- Distinct root polynomials remain nonassociated after a common dihedral action. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.Form.action_nonassociate (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (first second : PositiveRootIndex n)
    (hne : first ≠ second) :
    ¬ Associated (polynomialAction n element (rootPolynomial n first))
      (polynomialAction n element (rootPolynomial n second)) := by
  intro hassociated
  apply rootPolynomial_not_associated n first second hne
  simpa only [AlgEquiv.symm_apply_apply] using
    hassociated.map (polynomialAction n element).symm

/-- Distinct root polynomials retain no common nonunit divisor after a common action. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (first second : PositiveRootIndex n)
    (hne : first ≠ second) :
    IsRelPrime (polynomialAction n element (rootPolynomial n first))
      (polynomialAction n element (rootPolynomial n second)) := by
  apply IsRelPrime.of_map (polynomialAction n element).symm
  simpa only [AlgEquiv.symm_apply_apply] using rootPolynomial_isRelPrime n first second hne

end Schubert.Dihedral
