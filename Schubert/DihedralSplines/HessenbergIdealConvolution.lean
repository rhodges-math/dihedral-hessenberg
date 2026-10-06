import Schubert.DihedralSplines.HessenbergTensorKernel
import Schubert.FiniteGroupCharacters.PositiveTensorCharacter
import Schubert.DihedralSplines.HessenbergConvolution

/-! # Convolution of homogeneous coordinate-ideal kernels -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The homogeneous coordinate-projection kernel with its inherited dot action. -/
def removedFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let kernel := (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  exact FDRep.of kernel.toRepresentation

/-- Each removed-ideal degree character is the convolution over strictly positive scalar degrees. -/
theorem removed_piece_character (degree : ℕ) (element : DihedralGroup n) :
    (removedFDRep ideal degree).character element =
      ∑ split : Fin degree,
        (polynomialPieceRepresentation n (split.val + 1)).character element *
          (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
            (degree - (split.val + 1))).character element := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := ideal.toRootSubset.leftAlgebra hthree
  let := RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree
  let basis := FlowupSpline.Left.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Left.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hquotient := RootSubset.Left.quotientBasis_mem_piece ideal.toRootSubset hthree
    basis ideal.toRootSubset.length hbasis
  let kernel := (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  let positive := positiveTensor (P := Fin 2) ⊓
    tensorPiece (P := Fin 2) (RootSubset.Left.piece ideal.toRootSubset hthree) degree
  let : AddCommGroup ↥positive := Submodule.addCommGroup _
  let : Module ℂ ↥positive := Submodule.module _
  obtain ⟨equivalence⟩ := positive_kernel_equiv ideal degree
  change kernel.toRepresentation.character element = _
  rw [← congrFun (Representation.char_iso equivalence) element]
  exact positive_tensor_piece_character (polynomialRepresentation n)
    (RootSubset.Left.representation ideal.toRootSubset hthree)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.quotientBasis ideal.toRootSubset hthree basis)
    ideal.toRootSubset.length hquotient
    (fun element polynomial => polynomialAction_constantCoeff n element polynomial)
    (fun element _ _ hpoly => polynomialAction_isHomogeneous n element hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Left.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue) degree element

end Left


namespace Right

/-- The homogeneous coordinate-projection kernel with its inherited dot action. -/
def removedFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let kernel := (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  exact FDRep.of kernel.toRepresentation

/-- Each removed-ideal degree character is the convolution over strictly positive scalar degrees. -/
theorem removed_piece_character (degree : ℕ) (element : DihedralGroup n) :
    (removedFDRep ideal degree).character element =
      ∑ split : Fin degree,
        (Representation.trivial ℂ (DihedralGroup n)
          (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (split.val + 1))).character element *
          (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
            (degree - (split.val + 1))).character element := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := ideal.toRootSubset.rightAlgebra hthree
  let := RootSubset.Right.gradedAlgebra ideal.toRootSubset hthree
  let basis := FlowupSpline.Right.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Right.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hquotient := RootSubset.Right.quotientBasis_mem_piece ideal.toRootSubset hthree
    basis ideal.toRootSubset.length hbasis
  let kernel := (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  let positive := positiveTensor (P := Fin 2) ⊓
    tensorPiece (P := Fin 2) (RootSubset.Right.piece ideal.toRootSubset hthree) degree
  let : AddCommGroup ↥positive := Submodule.addCommGroup _
  let : Module ℂ ↥positive := Submodule.module _
  obtain ⟨equivalence⟩ := positive_kernel_equiv ideal degree
  change kernel.toRepresentation.character element = _
  rw [← congrFun (Representation.char_iso equivalence) element]
  exact positive_tensor_piece_character
    (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (RootSubset.Right.representation ideal.toRootSubset hthree)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.quotientBasis ideal.toRootSubset hthree basis)
    ideal.toRootSubset.length hquotient
    (fun _ _ => rfl)
    (fun _ _ _ hpoly => hpoly)
    (fun element scalarDegree value hvalue => RootSubset.Right.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree value hvalue) degree element

end Right

end Schubert.DihedralSplines.HessenbergIdeal
