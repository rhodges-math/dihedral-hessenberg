import DihedralHessenberg.FiniteGroupCharacters.TensorPieceAction
import DihedralHessenberg.FiniteGroupCharacters.RestrictEquiv
import DihedralHessenberg.Paper.HessenbergTensorFree
import DihedralHessenberg.Paper.LowDegreeSplineRestriction

/-! # Homogeneous tensor equivalences of Hessenberg spline actions -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The diagonal tensor action on its ordinary total-degree submodule. -/
def tensorRepresentation (degree : ℕ) :
    Representation ℂ (DihedralGroup n)
      (tensorPiece (P := Fin 2) (RootSubset.Left.piece ideal.toRootSubset hthree) degree) :=
  tensorPieceRepresentation (polynomialRepresentation n)
    (RootSubset.Left.representation ideal.toRootSubset hthree)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (fun element _ _ hpolynomial => polynomialAction_isHomogeneous n element hpolynomial)
    (fun element scalarDegree vector hvector =>
      RootSubset.Left.dot_mem_piece ideal.toRootSubset hthree element scalarDegree vector hvector)
    degree

/-- Graded tensor freeness restricts to an equivalence in every homogeneous degree. -/
theorem tensor_piece_equiv (degree : ℕ) :
    Nonempty (Representation.Equiv (tensorRepresentation ideal degree)
      (ideal.toRootSubset.splinePieceRepresentation hthree degree)) := by
  obtain ⟨equivalence, hdegrees, _⟩ := tensor_free ideal
  let sourcePiece : Subrepresentation
      (Representation.tprod (polynomialRepresentation n)
        (RootSubset.Left.representation ideal.toRootSubset hthree)) :=
    { toSubmodule := tensorPiece (RootSubset.Left.piece ideal.toRootSubset hthree) degree
      apply_mem_toSubmodule := fun element value hvalue =>
        tensor_piece_stable (polynomialRepresentation n)
          (RootSubset.Left.representation ideal.toRootSubset hthree)
          (RootSubset.Left.piece ideal.toRootSubset hthree)
          (fun element _ _ hpolynomial => polynomialAction_isHomogeneous n element hpolynomial)
          (fun element scalarDegree vector hvector =>
            RootSubset.Left.dot_mem_piece ideal.toRootSubset hthree
              element scalarDegree vector hvector) element degree value hvalue }
  let targetPiece : Subrepresentation (ideal.toRootSubset.splineRepresentation hthree) :=
    { toSubmodule := ideal.toRootSubset.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        ideal.toRootSubset.dot_mem_piece hthree element degree value hvalue }
  exact ⟨restrictEquiv equivalence sourcePiece targetPiece (hdegrees degree)⟩

/-- The homogeneous tensor representation is finite-dimensional. -/
def tensorFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup
      (tensorPiece (P := Fin 2) (RootSubset.Left.piece ideal.toRootSubset hthree) degree) :=
    Submodule.addCommGroup _
  let : Module ℂ
      (tensorPiece (P := Fin 2) (RootSubset.Left.piece ideal.toRootSubset hthree) degree) :=
    Submodule.module _
  let := ideal.splinePiece_finite degree
  let equivalence := Classical.choice (tensor_piece_equiv ideal degree)
  let := Module.Finite.of_surjective equivalence.toLinearEquiv.symm.toLinearMap
    equivalence.toLinearEquiv.symm.surjective
  exact FDRep.of (tensorRepresentation ideal degree)

end Left

namespace Right

/-- The diagonal tensor action on its ordinary total-degree submodule. -/
def tensorRepresentation (degree : ℕ) :
    Representation ℂ (DihedralGroup n)
      (tensorPiece (P := Fin 2) (RootSubset.Right.piece ideal.toRootSubset hthree) degree) :=
  tensorPieceRepresentation (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (RootSubset.Right.representation ideal.toRootSubset hthree)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (fun _ _ _ hpolynomial => hpolynomial)
    (fun element scalarDegree vector hvector =>
      RootSubset.Right.dot_mem_piece ideal.toRootSubset hthree element scalarDegree vector hvector)
    degree

/-- Graded tensor freeness restricts to an equivalence in every homogeneous degree. -/
theorem tensor_piece_equiv (degree : ℕ) :
    Nonempty (Representation.Equiv (tensorRepresentation ideal degree)
      (ideal.toRootSubset.splinePieceRepresentation hthree degree)) := by
  obtain ⟨equivalence, hdegrees, _⟩ := tensor_free ideal
  let sourcePiece : Subrepresentation
      (Representation.tprod (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
        (RootSubset.Right.representation ideal.toRootSubset hthree)) :=
    { toSubmodule := tensorPiece (RootSubset.Right.piece ideal.toRootSubset hthree) degree
      apply_mem_toSubmodule := fun element value hvalue =>
        tensor_piece_stable (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
          (RootSubset.Right.representation ideal.toRootSubset hthree)
          (RootSubset.Right.piece ideal.toRootSubset hthree)
          (fun _ _ _ hpolynomial => hpolynomial)
          (fun element scalarDegree vector hvector =>
            RootSubset.Right.dot_mem_piece ideal.toRootSubset hthree
              element scalarDegree vector hvector) element degree value hvalue }
  let targetPiece : Subrepresentation (ideal.toRootSubset.splineRepresentation hthree) :=
    { toSubmodule := ideal.toRootSubset.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        ideal.toRootSubset.dot_mem_piece hthree element degree value hvalue }
  exact ⟨restrictEquiv equivalence sourcePiece targetPiece (hdegrees degree)⟩

/-- The homogeneous tensor representation is finite-dimensional. -/
def tensorFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup
      (tensorPiece (P := Fin 2) (RootSubset.Right.piece ideal.toRootSubset hthree) degree) :=
    Submodule.addCommGroup _
  let : Module ℂ
      (tensorPiece (P := Fin 2) (RootSubset.Right.piece ideal.toRootSubset hthree) degree) :=
    Submodule.module _
  let := ideal.splinePiece_finite degree
  let equivalence := Classical.choice (tensor_piece_equiv ideal degree)
  let := Module.Finite.of_surjective equivalence.toLinearEquiv.symm.toLinearMap
    equivalence.toLinearEquiv.symm.surjective
  exact FDRep.of (tensorRepresentation ideal degree)

end Right

end Schubert.DihedralSplines.HessenbergIdeal
