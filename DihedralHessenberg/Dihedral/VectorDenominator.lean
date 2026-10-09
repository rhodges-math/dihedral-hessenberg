import DihedralHessenberg.Dihedral.PlaneDeterminant
import Mathlib.RingTheory.PowerSeries.Basic

/-! # The determinant denominator of the planar action -/

noncomputable section
namespace Schubert.Dihedral

/-- The determinant of identity minus the variable times the plane operator. -/
def vectorDenominator (n : ℕ) [NeZero n] (element : DihedralGroup n) : Polynomial ℂ :=
  Matrix.det ((1 : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) -
    (Polynomial.X : Polynomial ℂ) • (LinearMap.toMatrix (Pi.basisFun ℂ (Fin 2))
      (Pi.basisFun ℂ (Fin 2)) (vectorRepresentation n element)).map Polynomial.C)

/-- The planar determinant denominator is its trace and determinant quadratic. -/
theorem vectorDenominator_trace (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    vectorDenominator n element = 1 -
      Polynomial.C ((vectorRepresentation n).character element) * Polynomial.X +
      Polynomial.C (LinearMap.det (vectorRepresentation n element)) * Polynomial.X ^ 2 := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2)),
    ← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 2))]
  rw [Matrix.det_fin_two]
  simp [vectorDenominator, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two,
    Matrix.map_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- Every rotation denominator has its cosine trace coefficient. -/
theorem vectorDenominator_r (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    vectorDenominator n (.r coordinate) = 1 -
      Polynomial.C (2 * (Real.cos (2 * Real.pi * coordinate.val / n) : ℂ)) *
        Polynomial.X + Polynomial.X ^ 2 := by
  rw [vectorDenominator_trace, vectorRepresentation_character_r, vectorRepresentation_det_r]
  simp

/-- Every reflection has the standard determinant denominator. -/
theorem vectorDenominator_sr (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    vectorDenominator n (.sr coordinate) = 1 - Polynomial.X ^ 2 := by
  rw [vectorDenominator_trace, vectorRepresentation_character_sr,
    vectorRepresentation_det_sr]
  simp
  ring

/-- At identity the determinant denominator is the squared linear factor. -/
theorem vectorDenominator_one (n : ℕ) [NeZero n] :
    vectorDenominator n 1 = (1 - Polynomial.X) ^ 2 := by
  change vectorDenominator n (.r 0) = _
  rw [vectorDenominator_r]
  norm_num [Polynomial.C_ofNat]
  ring

/-- The determinant denominator has constant coefficient one. -/
theorem vectorDenominator_constant (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    (vectorDenominator n element).coeff 0 = 1 := by
  rw [vectorDenominator_trace]
  simp

end Schubert.Dihedral
