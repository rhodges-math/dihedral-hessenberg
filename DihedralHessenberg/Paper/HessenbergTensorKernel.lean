import DihedralHessenberg.FiniteGroupCharacters.TensorKernelDegree
import DihedralHessenberg.Paper.SplineTensorAugmentation
import DihedralHessenberg.Paper.HessenbergTensorPiece
import DihedralHessenberg.Dihedral.InvariantsBasic

/-! # Homogeneous coordinate-ideal tensor actions -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The diagonal action on the positive scalar tensor part in one total degree. -/
def positiveRepresentation (degree : ℕ) := by
  let := ideal.toRootSubset.leftAlgebra hthree
  exact positiveTensorPieceRepresentation (polynomialRepresentation n)
    (RootSubset.Left.representation ideal.toRootSubset hthree)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.quotientBasis ideal.toRootSubset hthree (FlowupSpline.Left.basis ideal))
    (fun element polynomial => polynomialAction_constantCoeff n element polynomial)
    (fun element _ _ hpoly => polynomialAction_isHomogeneous n element hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Left.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue) degree

/-- The coordinate projection kernel is the positive scalar tensor representation. -/
theorem positive_kernel_equiv (degree : ℕ) :
    Nonempty (Representation.Equiv (positiveRepresentation ideal degree)
      (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree).ker.toRepresentation) := by
  let := ideal.toRootSubset.leftAlgebra hthree
  let basis := FlowupSpline.Left.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Left.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  obtain ⟨equivalence, hdegrees, hpure⟩ := RootSubset.Left.tensor_free_augmentation
    ideal.toRootSubset hthree basis ideal.toRootSubset.length hbasis
  let projection : (ideal.toRootSubset.splineRepresentation hthree).IntertwiningMap
      (RootSubset.Left.representation ideal.toRootSubset hthree) :=
    { toLinearMap := (RootSubset.Left.quotientMap ideal.toRootSubset hthree).toLinearMap
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        exact (RootSubset.Left.dot_map ideal.toRootSubset hthree element value).symm }
  let sourcePiece : Subrepresentation (ideal.toRootSubset.splineRepresentation hthree) :=
    { toSubmodule := ideal.toRootSubset.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        ideal.toRootSubset.dot_mem_piece hthree element degree value hvalue }
  let quotientPiece : Subrepresentation
      (RootSubset.Left.representation ideal.toRootSubset hthree) :=
    { toSubmodule := RootSubset.Left.piece ideal.toRootSubset hthree degree
      apply_mem_toSubmodule := fun element value hvalue => RootSubset.Left.dot_mem_piece
        ideal.toRootSubset hthree element degree value hvalue }
  exact tensor_kernel_degree_equiv (polynomialRepresentation n)
    (RootSubset.Left.representation ideal.toRootSubset hthree)
    (ideal.toRootSubset.splineRepresentation hthree)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.quotientBasis ideal.toRootSubset hthree basis)
    (fun element polynomial => polynomialAction_constantCoeff n element polynomial)
    (fun element _ _ hpoly => polynomialAction_isHomogeneous n element hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Left.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue)
    degree equivalence projection hpure sourcePiece quotientPiece
    (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree) (fun _ => rfl)
    (hdegrees degree)

end Left


namespace Right

/-- The diagonal action on the positive scalar tensor part in one total degree. -/
def positiveRepresentation (degree : ℕ) := by
  let := ideal.toRootSubset.rightAlgebra hthree
  exact positiveTensorPieceRepresentation
    (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (RootSubset.Right.representation ideal.toRootSubset hthree)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.quotientBasis ideal.toRootSubset hthree (FlowupSpline.Right.basis ideal))
    (fun _ _ => rfl)
    (fun _ _ _ hpoly => hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Right.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue) degree

/-- The coordinate projection kernel is the positive scalar tensor representation. -/
theorem positive_kernel_equiv (degree : ℕ) :
    Nonempty (Representation.Equiv (positiveRepresentation ideal degree)
      (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree).ker.toRepresentation) :=
    by
  let := ideal.toRootSubset.rightAlgebra hthree
  let basis := FlowupSpline.Right.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Right.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  obtain ⟨equivalence, hdegrees, hpure⟩ := RootSubset.Right.tensor_free_augmentation
    ideal.toRootSubset hthree basis ideal.toRootSubset.length hbasis
  let projection : (ideal.toRootSubset.splineRepresentation hthree).IntertwiningMap
      (RootSubset.Right.representation ideal.toRootSubset hthree) :=
    { toLinearMap := (RootSubset.Right.quotientMap ideal.toRootSubset hthree).toLinearMap
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        exact (RootSubset.Right.dot_map ideal.toRootSubset hthree element value).symm }
  let sourcePiece : Subrepresentation (ideal.toRootSubset.splineRepresentation hthree) :=
    { toSubmodule := ideal.toRootSubset.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        ideal.toRootSubset.dot_mem_piece hthree element degree value hvalue }
  let quotientPiece : Subrepresentation
      (RootSubset.Right.representation ideal.toRootSubset hthree) :=
    { toSubmodule := RootSubset.Right.piece ideal.toRootSubset hthree degree
      apply_mem_toSubmodule := fun element value hvalue => RootSubset.Right.dot_mem_piece
        ideal.toRootSubset hthree element degree value hvalue }
  exact tensor_kernel_degree_equiv (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (RootSubset.Right.representation ideal.toRootSubset hthree)
    (ideal.toRootSubset.splineRepresentation hthree)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.quotientBasis ideal.toRootSubset hthree basis)
    (fun _ _ => rfl)
    (fun _ _ _ hpoly => hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Right.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue)
    degree equivalence projection hpure sourcePiece quotientPiece
    (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree) (fun _ => rfl)
    (hdegrees degree)

end Right

end Schubert.DihedralSplines.HessenbergIdeal
