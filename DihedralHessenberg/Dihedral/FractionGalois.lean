import DihedralHessenberg.Dihedral.PolynomialGalois
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-! # Fraction fields of the dihedral invariant extension -/

noncomputable section
namespace Schubert.Dihedral

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Extend the polynomial automorphisms to the field of fractions. -/
@[instance_reducible]
def fractionMulAction (n : ℕ) [NeZero n] :
    MulSemiringAction (DihedralGroup n) (FractionRing CoordinatePolynomial) := by
  let := polynomialMulAction n
  exact IsFractionRing.mulSemiringAction (DihedralGroup n) CoordinatePolynomial _

/-- The fraction action retains the polynomial action on embedded polynomials. -/
theorem fractionMulAction_map (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    letI := fractionMulAction n
    element • algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial) polynomial =
      algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial)
        (polynomialAction n element polynomial) := by
  let := polynomialMulAction n
  let := fractionMulAction n
  let : SMulDistribClass (DihedralGroup n) CoordinatePolynomial
      (FractionRing CoordinatePolynomial) :=
    IsFractionRing.smulDistribClass (DihedralGroup n) CoordinatePolynomial _
  exact (algebraMap.coe_smul' element polynomial (FractionRing CoordinatePolynomial)).symm

/-- The fraction-field extension has the dihedral group as its Galois group. -/
theorem fraction_isGaloisGroup (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    IsGaloisGroup (DihedralGroup n) (FractionRing (invariantSubalgebra n))
      (FractionRing CoordinatePolynomial) := by
  let := polynomialMulAction n
  let := fractionMulAction n
  let : SMulDistribClass (DihedralGroup n) CoordinatePolynomial
      (FractionRing CoordinatePolynomial) :=
    IsFractionRing.smulDistribClass (DihedralGroup n) CoordinatePolynomial _
  let : IsGaloisGroup (DihedralGroup n) (invariantSubalgebra n) CoordinatePolynomial :=
    polynomial_isGaloisGroup n
  have : IsScalarTower (invariantSubalgebra n)
      (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial) :=
    FractionRing.isScalarTower_liftAlgebra (invariantSubalgebra n)
      (FractionRing CoordinatePolynomial)
  exact IsGaloisGroup.to_isFractionRing (DihedralGroup n) (invariantSubalgebra n)
    CoordinatePolynomial (FractionRing (invariantSubalgebra n))
    (FractionRing CoordinatePolynomial)

/-- The extension of fraction fields is Galois. -/
theorem fraction_isGalois (n : ℕ) [NeZero n] :
    IsGalois (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  let := fraction_isGaloisGroup n
  exact IsGaloisGroup.isGalois (DihedralGroup n)
    (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial)

/-- Fixed fractions are exactly the embedded fractions of invariant polynomials. -/
theorem fraction_fixed (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    Set.range (algebraMap (FractionRing (invariantSubalgebra n))
      (FractionRing CoordinatePolynomial)) =
      {value | ∀ element : DihedralGroup n, element • value = value} := by
  let := fractionMulAction n
  let := fraction_isGaloisGroup n
  ext value
  constructor
  · rintro ⟨fraction, rfl⟩
    exact fun element => smul_algebraMap element fraction
  · exact fun hfixed => Algebra.IsInvariant.isInvariant value hfixed

end Schubert.Dihedral
