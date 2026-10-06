import Schubert.Dihedral.InvariantsBasic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The action on the dihedral coinvariant algebra

The official polynomial action descends along the invariant-generated quotient ideal.
The resulting algebra automorphisms give the standard base-field linear representation.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The automorphism induced on the official coinvariant quotient by a group element. -/
def coinvariantActionEquiv (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    CoinvariantAlgebra n ≃ₐ[ℂ] CoinvariantAlgebra n :=
  Ideal.quotientEquivAlg _ _ (polynomialAction n element)
    (polynomialAction_map_coinvariantIdeal n element).symm

/-- The quotient automorphism acts on polynomial representatives by the polynomial action. -/
theorem coinvariantActionEquiv_mk (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    coinvariantActionEquiv n element (Ideal.Quotient.mk (coinvariantIdeal n) polynomial) =
      Ideal.Quotient.mk (coinvariantIdeal n) (polynomialAction n element polynomial) :=
  Ideal.quotientEquivAlg_mk _ _ _ polynomial

/-- The dihedral action by algebra automorphisms of its coinvariant algebra. -/
def coinvariantAction (n : ℕ) [NeZero n] :
    DihedralGroup n →* (CoinvariantAlgebra n ≃ₐ[ℂ] CoinvariantAlgebra n) where
  toFun := coinvariantActionEquiv n
  map_one' := by
    apply AlgEquiv.ext
    intro element
    obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective element
    simp only [coinvariantActionEquiv_mk, map_one, AlgEquiv.one_apply]
  map_mul' first second := by
    apply AlgEquiv.ext
    intro element
    obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective element
    simp only [coinvariantActionEquiv_mk, map_mul, AlgEquiv.mul_apply]

/-- The standard complex-linear representation on the official coinvariant quotient. -/
def coinvariantRepresentation (n : ℕ) [NeZero n] :
    Representation ℂ (DihedralGroup n) (CoinvariantAlgebra n) :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (coinvariantAction n)

/-- The coinvariant representation evaluates on a quotient polynomial representative. -/
theorem coinvariantRepresentation_mk (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    coinvariantRepresentation n element (Ideal.Quotient.mk (coinvariantIdeal n) polynomial) =
      Ideal.Quotient.mk (coinvariantIdeal n) (polynomialAction n element polynomial) :=
  coinvariantActionEquiv_mk n element polynomial

end Schubert.Dihedral
