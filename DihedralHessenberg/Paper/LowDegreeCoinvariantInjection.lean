import DihedralHessenberg.Paper.FullCoinvariantProjection
import DihedralHessenberg.Paper.LowDegreeQuotientRestriction
import DihedralHessenberg.Paper.CoinvariantPieceMap

/-! Restriction of full constant coinvariants is the selected constant map. -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Restriction of full constant coinvariants is the selected constant map. -/
theorem coinvariantPieceMap_restrict (degree : ℕ)
    (value : TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :
    Right.fullPieceMap ideal degree ((RootSubset.full n).coinvariantPieceMap hthree degree value) =
      ideal.toRootSubset.coinvariantPieceMap hthree degree value := by
  apply Subtype.ext
  obtain ⟨polynomial, hpolynomial, heq⟩ :=
    (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp value.property
  change RootSubset.Right.restrict ideal.toRootSubset (RootSubset.full n) hthree
    ideal.toRootSubset.positive ((RootSubset.full n).coinvariantMap hthree value.val) =
      ideal.toRootSubset.coinvariantMap hthree value.val
  rw [← heq, RootSubset.coinvariantMap_mk, RootSubset.coinvariantMap_mk]
  rfl

/-- Constant coinvariants inject into the right quotient through the half boundary. -/
theorem coinvariantPieceMap_injective (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree ≤ half) :
    Function.Injective (ideal.toRootSubset.coinvariantPieceMap hthree degree) := by
  intro first second heq
  have hfull : (RootSubset.full n).coinvariantPieceMap hthree degree first =
      (RootSubset.full n).coinvariantPieceMap hthree degree second := by
    apply Right.fullPieceMap_injective ideal half hhalf degree hdegree
    rw [ideal.coinvariantPieceMap_restrict, ideal.coinvariantPieceMap_restrict, heq]
  apply Subtype.ext
  exact fullCoinvariantMap_injective n hthree (congrArg Subtype.val hfull)

end Schubert.DihedralSplines.HessenbergIdeal
