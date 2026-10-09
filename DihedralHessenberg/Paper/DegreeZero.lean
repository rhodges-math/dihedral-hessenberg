import DihedralHessenberg.Paper.HessenbergConnectivity
import DihedralHessenberg.Paper.GradedQuotient
import DihedralHessenberg.Dihedral.RootPolynomialAction
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Degree-zero Hessenberg splines are constant -/

namespace Schubert.Splines

variable {K P : Type*} [CommRing K] [IsDomain K]

/-- A nonzero linear label dividing a homogeneous constant difference forces equality. -/
theorem _root_.Schubert.Splines.DegreeZero.eq_of_linear_dvd_sub
    {label first second : MvPolynomial P K}
    (hlabel : label.IsHomogeneous 1) (hnonzero : label ≠ 0)
    (hfirst : first.IsHomogeneous 0) (hsecond : second.IsHomogeneous 0)
    (hdivides : label ∣ first - second) : first = second := by
  by_contra hne
  have hdifference : first - second ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨factor, hfactor⟩ := hdivides
  have hfactorNonzero : factor ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hdifference hfactor
  have hdegree := (hfirst.sub hsecond).totalDegree hdifference
  rw [hfactor, MvPolynomial.totalDegree_mul_of_isDomain hnonzero hfactorNonzero,
    hlabel.totalDegree hnonzero] at hdegree
  omega

end Schubert.Splines

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- Every homogeneous degree-zero Hessenberg spline has equal vertex values. -/
theorem hessenbergSpline_degree_zero_vertex_eq (value : HessenbergSpline ideal)
    (hvalue : value ∈ (hessenbergGraph ideal).homogeneousPiece 0) (vertex : DihedralGroup n) :
    (value : DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) 1 := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply ideal.eq_identity_of_eq_on_reflection_edges
    (value : DihedralGroup n → CoordinatePolynomial) ?_ vertex
  intro element index hindex
  apply _root_.Schubert.Splines.DegreeZero.eq_of_linear_dvd_sub
    (polynomialAction_isHomogeneous n element (rootPolynomial_isHomogeneous n index))
    (polynomialAction_rootPolynomial_ne_zero n element index)
    (hvalue element) (hvalue (element * rootReflection index))
  exact hessenbergSpline_condition ideal value element index hindex

/-- Every degree-zero Hessenberg spline is a scalar constant. -/
theorem hessenbergSpline_degree_zero_eq_scalar (value : HessenbergSpline ideal)
    (hvalue : value ∈ (hessenbergGraph ideal).homogeneousPiece 0) :
    ∃ scalar : ℂ, value = algebraMap ℂ (HessenbergSpline ideal) scalar := by
  refine ⟨((value : DihedralGroup n → CoordinatePolynomial) 1).coeff 0, ?_⟩
  apply Subtype.ext
  funext vertex
  rw [hessenbergSpline_degree_zero_vertex_eq ideal value hvalue vertex]
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by
    exact Nat.eq_zero_of_le_zero (hvalue 1).totalDegree_le)

/-- The dot action fixes every homogeneous degree-zero Hessenberg spline. -/
theorem hessenbergSpline_dot_degree_zero (value : HessenbergSpline ideal)
    (hvalue : value ∈ (hessenbergGraph ideal).homogeneousPiece 0)
    (element : DihedralGroup n) :
    (dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n))
      element value = value := by
  obtain ⟨scalar, rfl⟩ := hessenbergSpline_degree_zero_eq_scalar ideal value hvalue
  exact ((dihedralReflectionData n hthree).dotEquiv
    (ideal.roots : Set (PositiveRootIndex n)) element).commutes scalar

/-- Every left quotient degree-zero element is a scalar class. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.degree_zero_eq_scalar (value :
  LeftHessenbergQuotient ideal)
    (hvalue : value ∈ leftHessenbergQuotientPiece ideal 0) :
    ∃ scalar : ℂ, value = algebraMap ℂ (LeftHessenbergQuotient ideal) scalar := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := hessenbergGradedAlgebra ideal
  obtain ⟨spline, hspline, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff
    (hessenbergGraph ideal).homogeneousPiece (leftHessenbergIdeal ideal)).mp hvalue
  obtain ⟨scalar, rfl⟩ := hessenbergSpline_degree_zero_eq_scalar ideal spline hspline
  exact ⟨scalar, (Ideal.Quotient.mkₐ ℂ (leftHessenbergIdeal ideal)).commutes scalar⟩

/-- Every right quotient degree-zero element is a scalar class. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.degree_zero_eq_scalar (value :
  RightHessenbergQuotient ideal)
    (hvalue : value ∈ rightHessenbergQuotientPiece ideal 0) :
    ∃ scalar : ℂ, value = algebraMap ℂ (RightHessenbergQuotient ideal) scalar := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := hessenbergGradedAlgebra ideal
  obtain ⟨spline, hspline, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff
    (hessenbergGraph ideal).homogeneousPiece (rightHessenbergIdeal ideal)).mp hvalue
  obtain ⟨scalar, rfl⟩ := hessenbergSpline_degree_zero_eq_scalar ideal spline hspline
  exact ⟨scalar, (Ideal.Quotient.mkₐ ℂ (rightHessenbergIdeal ideal)).commutes scalar⟩

/-- The left quotient degree-zero dot representation fixes every vector. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation_zero_apply (element
  : DihedralGroup n)
    (value : leftHessenbergQuotientPiece ideal 0) :
    _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation ideal 0 element value =
      value := by
  apply Subtype.ext
  change (dihedralGradedReflectionData n hthree).leftQuotientDotEquiv
    (ideal.roots : Set (PositiveRootIndex n)) element value.val = value.val
  obtain ⟨scalar, hscalar⟩ :=
    _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.degree_zero_eq_scalar ideal
      value.val value.property
  rw [hscalar]
  exact ((dihedralGradedReflectionData n hthree).leftQuotientDotEquiv
    (ideal.roots : Set (PositiveRootIndex n)) element).commutes scalar

/-- The right quotient degree-zero dot representation fixes every vector. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation_zero_apply (element
  : DihedralGroup n)
    (value : rightHessenbergQuotientPiece ideal 0) :
    _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation ideal 0 element value =
      value := by
  apply Subtype.ext
  change (dihedralGradedReflectionData n hthree).rightQuotientDotEquiv
    (ideal.roots : Set (PositiveRootIndex n)) element value.val = value.val
  obtain ⟨scalar, hscalar⟩ :=
    _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.degree_zero_eq_scalar ideal
      value.val value.property
  rw [hscalar]
  exact ((dihedralGradedReflectionData n hthree).rightQuotientDotEquiv
    (ideal.roots : Set (PositiveRootIndex n)) element).commutes scalar

end Schubert.DihedralSplines
