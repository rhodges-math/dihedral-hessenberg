import Schubert.Splines.GradedReflectionGraph

/-! # Degree compatibility of both polynomial scalar structures -/

namespace Schubert.Splines.GradedReflectionGraphData

variable {K P W T : Type*} [CommRing K] [Group W]
variable (data : GradedReflectionGraphData K P W T)

/-- A homogeneous constant spline has the degree of its scalar polynomial. -/
theorem constantSpline_mem_homogeneousPiece (selected : Set T) {degree : ℕ}
    {scalar : MvPolynomial P K} (hscalar : scalar.IsHomogeneous degree) :
    data.toReflectionGraphData.constantSpline selected scalar ∈
      data.homogeneousPiece selected degree := fun _ => hscalar

/-- A homogeneous orbit spline has the degree of its scalar polynomial. -/
theorem orbitSpline_mem_homogeneousPiece (selected : Set T) {degree : ℕ}
    {scalar : MvPolynomial P K} (hscalar : scalar.IsHomogeneous degree) :
    data.toReflectionGraphData.orbitSpline selected scalar ∈
      data.homogeneousPiece selected degree :=
  fun vertex => data.action_homogeneous vertex degree scalar hscalar

/-- Left multiplication by a homogeneous scalar adds degrees. -/
theorem leftScalar_mem_homogeneousPiece (selected : Set T) {scalarDegree valueDegree : ℕ}
    {scalar : MvPolynomial P K} (hscalar : scalar.IsHomogeneous scalarDegree)
    {value : data.toReflectionGraphData.Spline selected}
    (hvalue : value ∈ data.homogeneousPiece selected valueDegree) :
    data.toReflectionGraphData.leftScalar selected scalar value ∈
      data.homogeneousPiece selected (scalarDegree + valueDegree) :=
  fun vertex => hscalar.mul (hvalue vertex)

/-- Right multiplication by a homogeneous scalar adds degrees. -/
theorem rightScalar_mem_homogeneousPiece (selected : Set T) {scalarDegree valueDegree : ℕ}
    {scalar : MvPolynomial P K} (hscalar : scalar.IsHomogeneous scalarDegree)
    {value : data.toReflectionGraphData.Spline selected}
    (hvalue : value ∈ data.homogeneousPiece selected valueDegree) :
    data.toReflectionGraphData.rightScalar selected scalar value ∈
      data.homogeneousPiece selected (scalarDegree + valueDegree) :=
  fun vertex => (data.action_homogeneous vertex scalarDegree scalar hscalar).mul (hvalue vertex)

end Schubert.Splines.GradedReflectionGraphData
