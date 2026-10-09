import DihedralHessenberg.Paper.FlowupHilbert
import DihedralHessenberg.Splines.PolynomialSplineFinite
import DihedralHessenberg.Paper.HessenbergLowDegree
import DihedralHessenberg.Paper.RootFullDegree
import DihedralHessenberg.Paper.SplineRestriction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Low-degree comparison with full geometric splines -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Each spline degree piece is finite-dimensional. -/
theorem splinePiece_finite (degree : ℕ) : Module.Finite ℂ (ideal.toRootSubset.piece degree) := by
  let := (hessenbergGraph ideal.indexed).homogeneousPiece_finite degree
  exact Module.Finite.equiv (ideal.pieceEquiv degree).symm

/-- Function restriction gives a linear map of the degree pieces. -/
def fullPieceMap (degree : ℕ) :
    (RootSubset.full n).piece degree →ₗ[ℂ] ideal.toRootSubset.piece degree where
  toFun value := ⟨ideal.toRootSubset.restrictFull value.val, value.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero n] in
/-- Restriction retains all values and is injective on each degree. -/
theorem fullPieceMap_injective (degree : ℕ) : Function.Injective (ideal.fullPieceMap degree) := by
  intro first second heq
  apply Subtype.ext
  exact ideal.toRootSubset.restrict_injective (RootSubset.full n) ideal.toRootSubset.positive
    (congrArg Subtype.val heq)

/-- Below half the selected cardinality, full and selected pieces have equal dimensions. -/
theorem fullPiece_finrank (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree < half) :
    Module.finrank ℂ ((RootSubset.full n).piece degree) =
      Module.finrank ℂ (ideal.toRootSubset.piece degree) := by
  rw [ideal.piece_finrank]
  change Module.finrank ℂ ((full n hthree).toRootSubset.piece degree) = _
  rw [(full n hthree).piece_finrank]
  apply Finset.sum_congr rfl
  intro vertex _
  change (if (RootSubset.full n).length vertex ≤ degree then
    degree - (RootSubset.full n).length vertex + 1 else 0) =
    if ideal.toRootSubset.length vertex ≤ degree then
      degree - ideal.toRootSubset.length vertex + 1 else 0
  rw [RootSubset.length_full]
  by_cases hlength : length n hthree vertex ≤ half
  · rw [ideal.length_below_half half hhalf vertex hlength]
  · have hlarge := ideal.half_le_length half hhalf vertex (by omega)
    have hleft : ¬length n hthree vertex ≤ degree := by omega
    have hright : ¬ideal.toRootSubset.length vertex ≤ degree := by omega
    simp only [hleft, hright, ite_false]

/-- Every selected homogeneous spline below the threshold is already a full spline. -/
theorem fullPieceMap_surjective (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree < half) :
    Function.Surjective (ideal.fullPieceMap degree) := by
  let : Module.Finite ℂ (ideal.toRootSubset.piece degree) := ideal.splinePiece_finite degree
  let : Module.Finite ℂ ((RootSubset.full n).piece degree) :=
    (full n hthree).splinePiece_finite degree
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℂ) (V := (RootSubset.full n).piece degree)
    (V₂ := ideal.toRootSubset.piece degree)
    (ideal.fullPiece_finrank half hhalf degree hdegree)
    (f := ideal.fullPieceMap degree)).mp (ideal.fullPieceMap_injective degree)


end Schubert.DihedralSplines.HessenbergIdeal
