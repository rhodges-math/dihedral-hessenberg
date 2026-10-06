import Schubert.Dihedral.FundamentalEigenvalues
import Schubert.Dihedral.Invariants

/-! # The polynomial action in auxiliary coordinates

The existing change of coordinates transports the action to diagonal scaling for
rotation and to negative interchange for the first simple reflection.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Rotation after the auxiliary coordinate change is diagonal substitution. -/
theorem _root_.Schubert.Dihedral.AuxiliaryAction.action_rotation_axialEquiv (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) (polynomial : CoordinatePolynomial) :
    polynomialAction n (rotation n) (auxiliaryCoordinateEquiv polynomial) =
      auxiliaryCoordinateEquiv (MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then
          MvPolynomial.C ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹) *
            MvPolynomial.X 0
        else MvPolynomial.C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) *
          MvPolynomial.X 1) polynomial) := by
  have hequal : (polynomialAction n (rotation n)).toAlgHom.comp
      auxiliaryCoordinateEquiv.toAlgHom = auxiliaryCoordinateEquiv.toAlgHom.comp
      (MvPolynomial.aeval (fun coordinate : Fin 2 => if coordinate = 0 then
        MvPolynomial.C ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹) *
          MvPolynomial.X 0
        else MvPolynomial.C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) *
          MvPolynomial.X 1)) := by
    ext coordinate : 1
    fin_cases coordinate
    · simpa [AlgHom.comp_apply, auxiliaryCoordinateEquiv, auxiliaryCoordinateHom] using
        polynomialAction_rotation_auxiliaryU n hthree
    · simpa [AlgHom.comp_apply, auxiliaryCoordinateEquiv, auxiliaryCoordinateHom] using
        polynomialAction_rotation_auxiliaryV n hthree
  exact DFunLike.congr_fun hequal polynomial

/-- The first simple reflection becomes negative interchange of the two variables. -/
theorem _root_.Schubert.Dihedral.AuxiliaryAction.action_s1_axialEquiv (n : ℕ) [NeZero n]
    (polynomial : CoordinatePolynomial) :
    polynomialAction n (firstSimpleReflection n) (auxiliaryCoordinateEquiv polynomial) =
      auxiliaryCoordinateEquiv (MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then -MvPolynomial.X 1 else -MvPolynomial.X 0) polynomial) := by
  have hequal : (polynomialAction n (firstSimpleReflection n)).toAlgHom.comp
      auxiliaryCoordinateEquiv.toAlgHom = auxiliaryCoordinateEquiv.toAlgHom.comp
      (MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then -MvPolynomial.X 1 else -MvPolynomial.X 0)) := by
    ext coordinate : 1
    fin_cases coordinate
    · simpa [AlgHom.comp_apply, auxiliaryCoordinateEquiv, auxiliaryCoordinateHom] using
        polynomialAction_firstSimple_auxiliaryU n
    · simpa [AlgHom.comp_apply, auxiliaryCoordinateEquiv, auxiliaryCoordinateHom] using
        polynomialAction_firstSimple_auxiliaryV n
  exact DFunLike.congr_fun hequal polynomial

end Schubert.Dihedral
