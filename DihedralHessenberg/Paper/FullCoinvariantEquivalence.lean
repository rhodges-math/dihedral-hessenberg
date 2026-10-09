import DihedralHessenberg.Paper.FullCoinvariantProjection
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.GeometricQuotientBasis
import DihedralHessenberg.Paper.PaperQuotientFinite
import DihedralHessenberg.Paper.PaperModuleFinite
import DihedralHessenberg.Dihedral.CoinvariantBasis
import DihedralHessenberg.Dihedral.AxialLength
import DihedralHessenberg.Paper.CoinvariantPieceMap

/-! The full right coordinate quotient has the exact coinvariant dimension. -/

noncomputable section
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- The full right coordinate quotient has the exact coinvariant dimension. -/
theorem fullRightQuotient_finrank (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Module.finrank ℂ (RootSubset.Right.Quotient (RootSubset.full n) hthree) = 2 * n := by
  let := (RootSubset.full n).rightAlgebra hthree
  let := (HessenbergIdeal.full n hthree).toRootSubset.rightAlgebra hthree
  let originalBasis : Module.Basis (DihedralGroup n) CoordinatePolynomial
      (RootSubset.full n).Spline := FlowupSpline.Right.basis (HessenbergIdeal.full n hthree)
  rw [Module.finrank_eq_card_basis
    (RootSubset.Right.quotientBasis (RootSubset.full n) hthree originalBasis), DihedralGroup.card]

/-- Full constant coinvariants exhaust the full right coordinate quotient. -/
theorem fullCoinvariantMap_surjective (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.Surjective ((RootSubset.full n).coinvariantMap hthree) := by
  let := coinvariantAlgebra_finite n
  let := RootSubset.Right.quotient_finite (RootSubset.full n) hthree
  have hdimension : Module.finrank ℂ (CoinvariantAlgebra n) =
      Module.finrank ℂ (RootSubset.Right.Quotient (RootSubset.full n) hthree) := by
    rw [coinvariantAlgebra_finrank n hthree, fullRightQuotient_finrank n hthree]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension
    (f := ((RootSubset.full n).coinvariantMap hthree).toLinearMap)).mp
      (fullCoinvariantMap_injective n hthree)

/-- The coinvariant algebra is the full right coordinate quotient. -/
def fullCoinvariantEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    CoinvariantAlgebra n ≃ₐ[ℂ] RootSubset.Right.Quotient (RootSubset.full n) hthree :=
  AlgEquiv.ofBijective ((RootSubset.full n).coinvariantMap hthree)
    ⟨fullCoinvariantMap_injective n hthree, fullCoinvariantMap_surjective n hthree⟩

/-- The equivalence sends every polynomial class to its constant spline class. -/
theorem fullCoinvariantEquiv_mk (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    fullCoinvariantEquiv n hthree (Ideal.Quotient.mk (coinvariantIdeal n) polynomial) =
      RootSubset.Right.quotientMap (RootSubset.full n) hthree
        ((RootSubset.full n).constantHom hthree polynomial) := rfl

/-- The full coinvariant equivalence intertwines the two actions. -/
theorem fullCoinvariantEquiv_equivariant (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (element : DihedralGroup n) (value : CoinvariantAlgebra n) :
    fullCoinvariantEquiv n hthree (coinvariantAction n element value) =
      RootSubset.Right.dotEquiv (RootSubset.full n) hthree element
        (fullCoinvariantEquiv n hthree value) :=
  (RootSubset.full n).coinvariantMap_equivariant hthree element value

/-- Every coinvariant degree maps bijectively to the corresponding full right degree. -/
theorem fullCoinvariantPieceMap_bijective (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) :
    Function.Bijective ((RootSubset.full n).coinvariantPieceMap hthree degree) := by
  let := coinvariant_homogeneousPiece_finite n degree
  let := RootSubset.Right.piece_finite (RootSubset.full n) hthree degree
  have hinj : Function.Injective ((RootSubset.full n).coinvariantPieceMap hthree degree) := by
    intro first second heq
    exact Subtype.ext (fullCoinvariantMap_injective n hthree (congrArg Subtype.val heq))
  have hdimension : Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) =
      Module.finrank ℂ (RootSubset.Right.piece (RootSubset.full n) hthree degree) := by
    rw [Schubert.Dihedral.Coinvariant.Piece.finrank_degree_fiber n hthree degree]
    have hfull := FlowupSpline.Right.piece_finrank (HessenbergIdeal.full n hthree) degree
    change Module.finrank ℂ (RootSubset.Right.piece (RootSubset.full n) hthree degree) =
      Nat.card {vertex : DihedralGroup n // (RootSubset.full n).length vertex = degree} at hfull
    rw [hfull]
    obtain ⟨vertices, hweights⟩ := exists_axial_length_equiv n hthree
    apply Nat.card_congr
    exact vertices.subtypeEquiv (fun index => by rw [RootSubset.length_full n hthree, hweights])
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension
    (f := ((RootSubset.full n).coinvariantPieceMap hthree degree).toLinearMap)).mp hinj⟩

/-- Full right quotient degrees are equivariantly the coinvariant degrees. -/
def fullCoinvariantPieceEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ) :
    Representation.Equiv (coinvariantPieceRepresentation n degree)
      (RootSubset.Right.pieceRepresentation (RootSubset.full n) hthree degree) :=
  ((RootSubset.full n).coinvariantPieceMap hthree degree).ofBijective
    (fullCoinvariantPieceMap_bijective n hthree degree)

end Schubert.DihedralSplines
