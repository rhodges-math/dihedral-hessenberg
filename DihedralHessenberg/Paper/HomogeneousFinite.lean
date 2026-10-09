import DihedralHessenberg.Splines.HomogeneousGenerators
import DihedralHessenberg.Paper.Grading

/-! # Homogeneous finite generators for Hessenberg splines -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- Hessenberg splines have finite homogeneous generators for the left scalars. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.homogeneous_generators :
    ∃ generators : Finset (HessenbergSpline ideal),
      Submodule.span CoordinatePolynomial (generators : Set (HessenbergSpline ideal)) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree,
          value ∈ (hessenbergGraph ideal).homogeneousPiece degree := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralGradedReflectionData n hthree).exists_left_homogeneous_generators
    (ideal.roots : Set (PositiveRootIndex n))

/-- Hessenberg splines have finite homogeneous generators for the right scalars. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.homogeneous_generators :
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
      (dihedralReflectionData n hthree).rightAlgebra
        (ideal.roots : Set (PositiveRootIndex n))
    ∃ generators : Finset (HessenbergSpline ideal),
      Submodule.span CoordinatePolynomial (generators : Set (HessenbergSpline ideal)) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree,
          value ∈ (hessenbergGraph ideal).homogeneousPiece degree := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
    (dihedralReflectionData n hthree).rightAlgebra
      (ideal.roots : Set (PositiveRootIndex n))
  exact (dihedralGradedReflectionData n hthree).exists_right_homogeneous_generators
    (ideal.roots : Set (PositiveRootIndex n))

end Schubert.DihedralSplines
