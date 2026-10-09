import DihedralHessenberg.Splines.PolynomialDegree
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Residual divisibility from homogeneous label products

Pairwise relatively prime nonzero homogeneous labels have the degree of their product
prescribed by the sum of their degrees. A diagonal with no larger total degree,
divisible by every label, divides every other simultaneous label multiple.
-/

namespace Schubert.Splines

universe u v w

variable {K : Type u} {P : Type v} {I : Type w} [Field K]

/-- A diagonal of no larger label-product degree divides every label multiple. -/
theorem _root_.Schubert.Splines.HomogeneousDivisibility.diagonal_dvd
    (indices : Finset I) (labels : I → MvPolynomial P K) (degrees : I → ℕ)
    (diagonal value : MvPolynomial P K)
    (hlabels : ∀ index ∈ indices, (labels index).IsHomogeneous (degrees index))
    (hlabelsNonzero : ∀ index ∈ indices, labels index ≠ 0)
    (hrelPrime : (indices : Set I).Pairwise (fun first second =>
      IsRelPrime (labels first) (labels second)))
    (hdiagonal : diagonal.totalDegree ≤ ∑ index ∈ indices, degrees index)
    (hdiagonalNonzero : diagonal ≠ 0)
    (hdividesDiagonal : ∀ index ∈ indices, labels index ∣ diagonal)
    (hdividesValue : ∀ index ∈ indices, labels index ∣ value) :
    diagonal ∣ value := by
  have hproductHomogeneous := MvPolynomial.IsHomogeneous.prod indices labels degrees hlabels
  have hproductNonzero : (∏ index ∈ indices, labels index) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hlabelsNonzero
  have hdegree : diagonal.totalDegree ≤ (∏ index ∈ indices, labels index).totalDegree := by
    rw [hproductHomogeneous.totalDegree hproductNonzero]
    exact hdiagonal
  have hproductDiagonal := Finset.prod_dvd_of_isRelPrime hrelPrime hdividesDiagonal
  have hproductValue := Finset.prod_dvd_of_isRelPrime hrelPrime hdividesValue
  exact (_root_.Schubert.Splines.PolynomialDegree.associated_of_dvd_degree_le
    hproductDiagonal hdiagonalNonzero hdegree).symm.dvd.trans hproductValue

end Schubert.Splines
