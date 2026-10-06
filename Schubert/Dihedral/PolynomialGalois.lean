import Schubert.Dihedral.InvariantAction
import Mathlib.RingTheory.IsGaloisGroup.Basic

/-! # The dihedral Galois action on its polynomial invariant extension -/

noncomputable section
namespace Schubert.Dihedral

/-- The polynomial algebra automorphisms as a multiplicative ring action. -/
@[instance_reducible]
def polynomialMulAction (n : ℕ) [NeZero n] :
    MulSemiringAction (DihedralGroup n) CoordinatePolynomial :=
  MulSemiringAction.compHom CoordinatePolynomial (polynomialAction n)

/-- The multiplicative action applies the polynomial automorphism. -/
theorem polynomialMulAction_apply (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    letI := polynomialMulAction n
    element • polynomial = polynomialAction n element polynomial := rfl

/-- The invariant-polynomial extension has the dihedral Galois group. -/
theorem polynomial_isGaloisGroup (n : ℕ) [NeZero n] :
    letI := polynomialMulAction n
    IsGaloisGroup (DihedralGroup n) (invariantSubalgebra n) CoordinatePolynomial := by
  let := polynomialMulAction n
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun {first second} hequal => polynomialAction_injective n ?_⟩
    apply AlgEquiv.ext
    exact hequal
  · refine ⟨fun element invariant polynomial => ?_⟩
    change polynomialAction n element (invariant.val * polynomial) =
      invariant.val * polynomialAction n element polynomial
    rw [map_mul, (mem_invariantSubalgebra n invariant.val).mp invariant.property element]
  · refine ⟨fun polynomial hfixed => ?_⟩
    exact ⟨⟨polynomial, (mem_invariantSubalgebra n polynomial).mpr hfixed⟩, rfl⟩

end Schubert.Dihedral
