import Schubert.Dihedral.PolynomialGrading
import Schubert.DihedralSplines.Spline
import Schubert.Splines.GradedReflectionGraph
import Schubert.Splines.FinitePolynomialGrading

/-! # Homogeneous degrees of dihedral Hessenberg splines

The root labels have degree one and the dihedral polynomial action preserves each
homogeneous degree. Thus the reflection spline data has homogeneous edge ideals,
and its dot action preserves pointwise homogeneous spline values.
-/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The dihedral reflection data together with its polynomial homogeneity proofs. -/
def dihedralGradedReflectionData (n : ℕ) (hthree : 3 ≤ n) :
    GradedReflectionGraphData ℂ (Fin 2) (DihedralGroup n) (PositiveRootIndex n) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact {
    toReflectionGraphData := dihedralReflectionData n hthree
    label_homogeneous := rootPolynomial_isHomogeneous n
    action_homogeneous := fun element _ _ hpolynomial =>
      polynomialAction_isHomogeneous n element hpolynomial }

/-- Forgetting the grading gives the dihedral reflection data. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.gradedData_toData (n : ℕ) (hthree : 3 ≤ n) :
    (dihedralGradedReflectionData n hthree).toReflectionGraphData =
      dihedralReflectionData n hthree :=
  rfl

/-- Each Hessenberg edge ideal is homogeneous in the polynomial grading. -/
theorem hessenbergGraph_label_homogeneous {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree)
    (edge : DihedralGroup n × {index : PositiveRootIndex n // index ∈ ideal.roots}) :
    ((hessenbergGraph ideal).label edge).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) :=
  (dihedralGradedReflectionData n hthree).edgeIdeal_homogeneous
    (ideal.roots : Set (PositiveRootIndex n)) edge

/-- The dot action on Hessenberg splines preserves each homogeneous degree piece. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.dot_mem_homogeneousPiece {n : ℕ} {hthree : 3 ≤
  n}
    (ideal : HessenbergSpace n hthree) (element : DihedralGroup n) (degree : ℕ)
    (value : HessenbergSpline ideal)
    (hvalue : value ∈ (hessenbergGraph ideal).homogeneousPiece degree) :
    (dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n)) element value ∈
      (hessenbergGraph ideal).homogeneousPiece degree :=
  (dihedralGradedReflectionData n hthree).dot_mem_homogeneousPiece
    (ideal.roots : Set (PositiveRootIndex n)) element degree value hvalue

/-- Every Hessenberg spline has a unique finite decomposition into homogeneous splines. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.homogeneousPiece_isInternal {n : ℕ} {hthree :
  3 ≤ n}
    (ideal : HessenbergSpace n hthree) :
    DirectSum.IsInternal (hessenbergGraph ideal).homogeneousPiece := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (hessenbergGraph ideal).homogeneousPiece_isInternal
    (hessenbergGraph_label_homogeneous ideal)

/-- The homogeneous polynomial grading on the Hessenberg spline algebra. -/
@[instance_reducible]
def hessenbergGradedAlgebra {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) :
    GradedAlgebra (hessenbergGraph ideal).homogeneousPiece := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (hessenbergGraph ideal).gradedAlgebra (hessenbergGraph_label_homogeneous ideal)

end Schubert.DihedralSplines
