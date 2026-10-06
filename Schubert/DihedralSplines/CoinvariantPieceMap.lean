import Schubert.DihedralSplines.CoinvariantSplineMap
import Schubert.DihedralSplines.PaperCoordinates
import Schubert.DihedralSplines.QuotientRepresentation
import Schubert.Dihedral.CoinvariantGradedRepresentation

/-! # Homogeneous coinvariant maps into the right quotient -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- The constant coinvariant map preserves the quotient homogeneous pieces. -/
theorem coinvariantMap_mem_piece (degree : ℕ) (value : CoinvariantAlgebra n)
    (hvalue : value ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :
    selected.coinvariantMap hthree value ∈ Right.piece selected hthree degree := by
  obtain ⟨polynomial, hpolynomial, rfl⟩ :=
    (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp hvalue
  rw [selected.coinvariantMap_mk]
  exact (Right.mem_piece selected hthree degree _).2
    ⟨selected.constantHom hthree polynomial,
      selected.constantHom_mem_piece hthree degree polynomial hpolynomial, rfl⟩

/-- The degreewise constant coinvariant map intertwines the restricted actions. -/
def coinvariantPieceMap (degree : ℕ) :
    Representation.IntertwiningMap (coinvariantPieceRepresentation n degree)
      (Right.pieceRepresentation selected hthree degree) where
  toLinearMap :=
    { toFun := fun value => ⟨selected.coinvariantMap hthree value.val,
        selected.coinvariantMap_mem_piece hthree degree value.val value.property⟩
      map_add' := fun first second => Subtype.ext (map_add _ first.val second.val)
      map_smul' := fun scalar value => Subtype.ext (map_smul _ scalar value.val) }
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact selected.coinvariantMap_equivariant hthree element value.val

/-- The restricted map is the constant quotient map on underlying coinvariants. -/
theorem coinvariantPieceMap_apply (degree : ℕ)
    (value : TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :
    (selected.coinvariantPieceMap hthree degree value : Right.Quotient selected hthree) =
      selected.coinvariantMap hthree value.val := rfl

/-- A homogeneous polynomial maps to its constant spline quotient representative. -/
theorem coinvariantPieceMap_mk (degree : ℕ) (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial.IsHomogeneous degree) :
    (selected.coinvariantPieceMap hthree degree
      ⟨Ideal.Quotient.mk (coinvariantIdeal n) polynomial,
        TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _ hpolynomial⟩ :
      Right.Quotient selected hthree) =
        Right.quotientMap selected hthree (selected.constantHom hthree polynomial) := rfl

end Schubert.Dihedral.RootSubset
