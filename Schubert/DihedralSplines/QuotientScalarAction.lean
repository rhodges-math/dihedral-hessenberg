import Schubert.DihedralSplines.FullLeftAction

/-! # Polynomial scalars in the coordinate quotients -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
open Schubert.DihedralSplines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- Polynomial scalars act on quotient classes through their constant coefficient. -/
theorem quotientMap_smul (polynomial : CoordinatePolynomial) (value : selected.Spline) :
    letI := selected.leftAlgebra hthree
    quotientMap selected hthree (polynomial • value) =
      polynomial.constantCoeff • quotientMap selected hthree value := by
  let := selected.leftAlgebra hthree
  change quotientMap selected hthree (selected.constantHom hthree polynomial * value) = _
  rw [map_mul, constant_map]
  exact (Algebra.smul_def polynomial.constantCoeff (quotientMap selected hthree value)).symm

end Left
namespace Right

/-- Orbit-coordinate classes evaluate the polynomial constant coefficient. -/
theorem orbit_map (polynomial : CoordinatePolynomial) :
    quotientMap selected hthree (selected.orbitHom hthree polynomial) =
      algebraMap ℂ (Quotient selected hthree) polynomial.constantCoeff := by
  let map : CoordinatePolynomial →ₐ[ℂ] Quotient selected hthree :=
    (quotientMap selected hthree).comp (selected.orbitHom hthree)
  have hzero (coordinate : Fin 2) : map (MvPolynomial.X coordinate) = 0 :=
    coordinate_zero selected hthree coordinate
  exact Schubert.Splines.QuotientFinite.apply_eq_constantCoeff
    (K := ℂ) (P := Fin 2) (A := Quotient selected hthree) map hzero polynomial

/-- Orbit polynomial scalars act on quotient classes through their constant coefficient. -/
theorem quotientMap_smul (polynomial : CoordinatePolynomial) (value : selected.Spline) :
    letI := selected.rightAlgebra hthree
    quotientMap selected hthree (polynomial • value) =
      polynomial.constantCoeff • quotientMap selected hthree value := by
  let := selected.rightAlgebra hthree
  change quotientMap selected hthree (selected.orbitHom hthree polynomial * value) = _
  rw [map_mul, orbit_map]
  exact (Algebra.smul_def polynomial.constantCoeff (quotientMap selected hthree value)).symm

end Right
end Schubert.Dihedral.RootSubset
