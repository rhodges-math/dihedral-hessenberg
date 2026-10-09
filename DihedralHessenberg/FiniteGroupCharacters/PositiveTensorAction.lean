import DihedralHessenberg.FiniteGroupCharacters.TensorAugmentation
import DihedralHessenberg.FiniteGroupCharacters.TensorPieceAction

/-! # Actions on positive scalar tensor degree intersections -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- Constant-coefficient preserving factor actions preserve the positive tensor piece. -/
theorem positive_tensor_piece_stable {K P Q I G : Type*} [Field K] [Monoid G]
    [AddCommGroup Q] [Module K Q] (scalar : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q) (basis : Module.Basis I K Q)
    (hconstant : ∀ element polynomial, (scalar element polynomial).constantCoeff =
      polynomial.constantCoeff)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalar element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree value, value ∈ pieces degree → source element value ∈ pieces degree)
    (element : G) (degree : ℕ) (value : MvPolynomial P K ⊗[K] Q)
    (hvalue : value ∈ positiveTensor ⊓ tensorPiece pieces degree) :
    (scalar.tprod source) element value ∈ positiveTensor ⊓ tensorPiece pieces degree := by
  constructor
  · rw [← tensorAugmentation_ker basis]
    change tensorAugmentation ((scalar.tprod source) element value) = 0
    have hzero : tensorAugmentation value = 0 := by
      apply LinearMap.mem_ker.mp
      rw [tensorAugmentation_ker basis]
      exact hvalue.1
    have hequivariant := LinearMap.congr_fun
      (tensorAugmentation_equivariant scalar source hconstant element) value
    change tensorAugmentation ((scalar.tprod source) element value) =
      source element (tensorAugmentation value) at hequivariant
    rw [hequivariant, hzero, map_zero]
  · exact tensor_piece_stable scalar source pieces hscalar hsource element degree value hvalue.2

/-- The tensor action restricted to its positive scalar homogeneous part. -/
def positiveTensorPieceRepresentation {K P Q I G : Type*} [Field K] [Monoid G]
    [AddCommGroup Q] [Module K Q] (scalar : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q) (basis : Module.Basis I K Q)
    (hconstant : ∀ element polynomial, (scalar element polynomial).constantCoeff =
      polynomial.constantCoeff)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalar element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree value, value ∈ pieces degree → source element value ∈ pieces degree)
    (degree : ℕ) :
    Representation K G ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) :=
  (scalar.tprod source).subrepresentation (positiveTensor ⊓ tensorPiece pieces degree)
    (fun element value hvalue => positive_tensor_piece_stable scalar source pieces basis
      hconstant hscalar hsource element degree value hvalue)

end Schubert.FiniteGroupCharacters
