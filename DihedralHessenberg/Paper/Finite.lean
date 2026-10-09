import DihedralHessenberg.Splines.ReflectionNoetherian
import DihedralHessenberg.Splines.SplineInfinitude
import DihedralHessenberg.Paper.Quotient

/-! # Unconditional finite generation and finite quotients of Hessenberg splines -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- Hessenberg splines are finitely generated under constant polynomial scalars. -/
theorem hessenbergLeftSpline_finite :
    Module.Finite CoordinatePolynomial (HessenbergSpline ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralReflectionData n hthree).leftSpline_finite
    (ideal.roots : Set (PositiveRootIndex n))

/-- Hessenberg splines are finitely generated under orbit polynomial scalars. -/
theorem hessenbergRightSpline_finite :
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
      (dihedralReflectionData n hthree).rightAlgebra
      (ideal.roots : Set (PositiveRootIndex n))
    Module.Finite CoordinatePolynomial (HessenbergSpline ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
    (dihedralReflectionData n hthree).rightAlgebra (ideal.roots : Set (PositiveRootIndex n))
  exact (dihedralReflectionData n hthree).rightSpline_finite
    (ideal.roots : Set (PositiveRootIndex n))

/-- The whole left Hessenberg quotient is finite without a triangular family. -/
theorem leftHessenbergQuotient_finite : Module.Finite ℂ (LeftHessenbergQuotient ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralReflectionData n hthree).leftQuotient_finite
    (ideal.roots : Set (PositiveRootIndex n))

/-- The whole right Hessenberg quotient is finite without a triangular family. -/
theorem rightHessenbergQuotient_finite : Module.Finite ℂ (RightHessenbergQuotient ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralReflectionData n hthree).rightQuotient_finite
    (ideal.roots : Set (PositiveRootIndex n))

/-- The constant polynomial embedding makes Hessenberg splines infinite-dimensional over ℂ. -/
theorem hessenbergSpline_not_moduleFinite : ¬Module.Finite ℂ (HessenbergSpline ideal) :=
  (dihedralReflectionData n hthree).spline_not_moduleFinite
    (ideal.roots : Set (PositiveRootIndex n))

end Schubert.DihedralSplines
