import Schubert.DihedralSplines.FlowupBasis
import Schubert.DihedralSplines.SplineHilbert
import Schubert.Splines.HilbertSeries
import Schubert.DihedralSplines.LengthPolynomialSymmetry

/-! # The full Hilbert series of geometric Hessenberg splines -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

omit [NeZero n] in
/-- Root transport preserves each polynomial-homogeneous spline submodule. -/
theorem piece_map (degree : ℕ) :
    (ideal.toRootSubset.piece degree).map ideal.splineEquiv.toLinearMap =
      (hessenbergGraph ideal.indexed).homogeneousPiece degree := by
  ext value
  constructor
  · rintro ⟨original, hhomogeneous, heq⟩
    rw [← heq]
    exact hhomogeneous
  · intro hhomogeneous
    exact ⟨ideal.splineEquiv.symm value, hhomogeneous, ideal.splineEquiv.apply_symm_apply value⟩

/-- Root transport restricts to an equivalence of the homogeneous spline pieces. -/
def pieceEquiv (degree : ℕ) : ideal.toRootSubset.piece degree ≃ₗ[ℂ]
    (hessenbergGraph ideal.indexed).homogeneousPiece degree :=
  (ideal.splineEquiv.toLinearEquiv.submoduleMap (ideal.toRootSubset.piece degree)).trans
    (LinearEquiv.ofEq _ _ (ideal.piece_map degree))

/-- The full spline degree dimension is the shifted two-variable polynomial convolution. -/
theorem piece_finrank (degree : ℕ) :
    Module.finrank ℂ (ideal.toRootSubset.piece degree) =
      ∑ vertex : DihedralGroup n,
        if ideal.toRootSubset.length vertex ≤ degree then
          degree - ideal.toRootSubset.length vertex + 1 else 0 := by
  classical
  rw [(ideal.pieceEquiv degree).finrank_eq]
  let family := FlowupSpline.family ideal
  rw [IndexedSpline.Piece.finrank_of_triangular ideal.indexed family.backend
    family.backend_support family.backend_diagonal family.backend_bound degree]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [← ideal.length_indexed]

/-- The formal Hilbert series has the homogeneous-piece dimensions as coefficients. -/
def hilbertSeries : PowerSeries ℚ :=
  PowerSeries.mk fun degree => (Module.finrank ℂ (ideal.toRootSubset.piece degree) : ℚ)

omit [NeZero n] in
/-- Every coefficient is the dimension of the corresponding spline degree piece. -/
theorem hilbertSeries_coeff (degree : ℕ) :
    PowerSeries.coeff degree ideal.hilbertSeries =
      (Module.finrank ℂ (ideal.toRootSubset.piece degree) : ℚ) := by
  simp [hilbertSeries]

/-- The complete Hilbert series is the sum of the shifted binary-polynomial Hilbert kernels. -/
theorem hilbertSeries_sum :
    ideal.hilbertSeries =
      (∑ vertex : DihedralGroup n,
        (PowerSeries.X : PowerSeries ℚ) ^ ideal.toRootSubset.length vertex) *
        (PowerSeries.invOneSubPow ℚ 2).val := by
  classical
  rw [← Schubert.Splines.Hilbert.finite_series]
  apply PowerSeries.ext
  intro degree
  rw [ideal.hilbertSeries_coeff, PowerSeries.coeff_mk, ideal.piece_finrank]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro vertex _
  split_ifs <;> simp

/-- The full Hilbert series has denominator precisely the square of one minus the variable. -/
theorem hilbertSeries_denominator :
    ideal.hilbertSeries * (1 - PowerSeries.X) ^ 2 =
      ∑ vertex : DihedralGroup n,
        (PowerSeries.X : PowerSeries ℚ) ^ ideal.toRootSubset.length vertex := by
  rw [ideal.hilbertSeries_sum, mul_assoc, Schubert.Splines.Hilbert.kernel_mul_denominator,
    mul_one]

/-- The H-length polynomial embeds as the sum of its degree monomials. -/
theorem lengthPolynomial_series :
    ((ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) : PowerSeries ℚ) =
      ∑ vertex : DihedralGroup n,
        (PowerSeries.X : PowerSeries ℚ) ^ ideal.toRootSubset.length vertex := by
  change Polynomial.coeToPowerSeries.ringHom
    (ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) = _
  simp [lengthPolynomial, Polynomial.map_sum]

/-- The full Hilbert series is P_H times the inverse square of one minus the variable. -/
theorem hilbertSeries_formula :
    ideal.hilbertSeries = ((ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ 2).val := by
  rw [ideal.lengthPolynomial_series]
  exact ideal.hilbertSeries_sum

/-- Multiplying the full Hilbert series by the displayed denominator gives exactly P_H. -/
theorem hilbertSeries_rank :
    ideal.hilbertSeries * (1 - PowerSeries.X) ^ 2 =
      ((ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) : PowerSeries ℚ) := by
  rw [ideal.lengthPolynomial_series]
  exact ideal.hilbertSeries_denominator

/-- Both polynomial modules are free, with palindromic P_H and the full Hilbert series. -/
theorem poincare_hilbert :
    (letI := ideal.toRootSubset.leftAlgebra hthree;
      Module.Free CoordinatePolynomial ideal.toRootSubset.Spline) ∧
    (letI := ideal.toRootSubset.rightAlgebra hthree;
      Module.Free CoordinatePolynomial ideal.toRootSubset.Spline) ∧
    Left.rankPolynomial ideal = ideal.lengthPolynomial ∧
    Right.rankPolynomial ideal = ideal.lengthPolynomial ∧
    ideal.lengthPolynomial.reverse = ideal.lengthPolynomial ∧
    ideal.hilbertSeries = ((ideal.lengthPolynomial.map (Nat.castRingHom ℚ)) : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ 2).val :=
  ⟨FlowupSpline.Left.free ideal, FlowupSpline.Right.free ideal,
    FlowupSpline.Left.rank_eq ideal, FlowupSpline.Right.rank_eq ideal,
    ideal.lengthPolynomial_reverse, ideal.hilbertSeries_formula⟩

end Schubert.DihedralSplines.HessenbergIdeal
