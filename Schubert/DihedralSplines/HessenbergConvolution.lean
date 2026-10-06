import Schubert.DihedralSplines.HessenbergTensorPiece
import Schubert.FiniteGroupCharacters.TensorPieceCharacter
import Schubert.DihedralSplines.GeometricQuotientBasis
import Schubert.DihedralSplines.QuotientRepresentation
import Schubert.DihedralSplines.OrbitScalarRepresentation

/-! # Degreewise convolution of the Hessenberg spline representations -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The finite-dimensional homogeneous spline action. -/
def splineFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  exact FDRep.of (V := ideal.toRootSubset.piece degree)
    (ideal.toRootSubset.splinePieceRepresentation hthree degree)

namespace Left

/-- Homogeneous spline characters are the convolution of their factor actions. -/
theorem spline_piece_character (degree : ℕ) (element : DihedralGroup n) :
    letI : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
    letI : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
    (ideal.toRootSubset.splinePieceRepresentation hthree degree).character element =
      ∑ split : Fin (degree + 1),
        (polynomialPieceRepresentation n split.val).character element *
          (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
            (degree - split.val)).character element := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
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
  let : AddCommGroup (tensorPiece (P := Fin 2)
      (RootSubset.Left.piece ideal.toRootSubset hthree) degree) := Submodule.addCommGroup _
  let : Module ℂ (tensorPiece (P := Fin 2)
      (RootSubset.Left.piece ideal.toRootSubset hthree) degree) := Submodule.module _
  obtain ⟨equivalence⟩ := tensor_piece_equiv ideal degree
  rw [← congrFun (Representation.char_iso equivalence) element]
  exact tensor_piece_character (polynomialRepresentation n)
    (RootSubset.Left.representation ideal.toRootSubset hthree)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.quotientBasis ideal.toRootSubset hthree basis)
    ideal.toRootSubset.length hquotient (fun element _ _ hpoly => polynomialAction_isHomogeneous n
      element hpoly)
    (fun element scalarDegree vector hvector => RootSubset.Left.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree vector hvector) degree element

/-- Each spline degree is a finite biproduct of tensor factors. -/
theorem degree_tensor_iso (degree : ℕ) : Nonempty (splineFDRep ideal degree ≅
    ⨁ fun split : Fin (degree + 1) => polynomialPieceFDRep n split.val ⊗
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree (degree - split.val)) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [finiteSum_character]
  change (ideal.toRootSubset.splinePieceRepresentation hthree degree).character element = _
  rw [spline_piece_character]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  rw [FDRep.char_tensor, Pi.mul_apply]
  simp only [RootSubset.Left.pieceFDRep_character]
  rfl

end Left

namespace Right

/-- Homogeneous spline characters are the convolution of their factor actions. -/
theorem spline_piece_character (degree : ℕ) (element : DihedralGroup n) :
    letI : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
    letI : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
    (ideal.toRootSubset.splinePieceRepresentation hthree degree).character element =
      ∑ split : Fin (degree + 1),
        ((fun degree => Representation.trivial ℂ (DihedralGroup n)
          (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree)) split.val).character element *
          (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
            (degree - split.val)).character element := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
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
  let : AddCommGroup (tensorPiece (P := Fin 2)
      (RootSubset.Right.piece ideal.toRootSubset hthree) degree) := Submodule.addCommGroup _
  let : Module ℂ (tensorPiece (P := Fin 2)
      (RootSubset.Right.piece ideal.toRootSubset hthree) degree) := Submodule.module _
  obtain ⟨equivalence⟩ := tensor_piece_equiv ideal degree
  rw [← congrFun (Representation.char_iso equivalence) element]
  exact tensor_piece_character (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (RootSubset.Right.representation ideal.toRootSubset hthree)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.quotientBasis ideal.toRootSubset hthree basis)
    ideal.toRootSubset.length hquotient (fun _ _ _ hpoly => hpoly)
    (fun element scalarDegree vector hvector => RootSubset.Right.dot_mem_piece
      ideal.toRootSubset hthree element scalarDegree vector hvector) degree element

/-- Each spline degree is a finite biproduct of tensor factors. -/
theorem degree_tensor_iso (degree : ℕ) : Nonempty (splineFDRep ideal degree ≅
    ⨁ fun split : Fin (degree + 1) => trivialPolynomialPiece n split.val ⊗
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree (degree - split.val)) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [finiteSum_character]
  change (ideal.toRootSubset.splinePieceRepresentation hthree degree).character element = _
  rw [spline_piece_character]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  rw [FDRep.char_tensor, Pi.mul_apply]
  simp only [RootSubset.Right.pieceFDRep_character]
  rfl

/-- Each spline degree splits using the orbit scalar subalgebra. -/
theorem degree_orbit_tensor_iso (degree : ℕ) : Nonempty (splineFDRep ideal degree ≅
    ⨁ fun split : Fin (degree + 1) =>
      RootSubset.Right.scalarPieceFDRep ideal.toRootSubset hthree split.val ⊗
        RootSubset.Right.pieceFDRep ideal.toRootSubset hthree (degree - split.val)) := by
  apply FDRep.nonempty_iso_of_character_eq
  have hcharacter := FDRep.char_iso (degree_tensor_iso ideal degree).some
  rw [finiteSum_character] at hcharacter
  rw [hcharacter, finiteSum_character]
  apply Finset.sum_congr rfl
  intro split _
  rw [FDRep.char_tensor, FDRep.char_tensor]
  congr 1
  have hscalar : Nonempty (trivialPolynomialPiece n split.val ≅
      RootSubset.Right.scalarPieceFDRep ideal.toRootSubset hthree split.val) := by
    apply TauCeti.nonempty_fdRepIso_iff.mpr
    exact ⟨RootSubset.Right.scalarPieceActionEquiv ideal.toRootSubset hthree split.val⟩
  exact FDRep.char_iso hscalar.some

end Right

end Schubert.DihedralSplines.HessenbergIdeal
