import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Tower

/-! # Finite quotients after killing polynomial coordinates

A polynomial algebra map killing all variables factors through its constant
coefficient. Thus a quotient of a module with a finite polynomial basis is
spanned over the coefficient ring by the images of those basis vectors.
-/

namespace Schubert.Splines

variable {K P A B I : Type*} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

/-- A polynomial algebra map killing the variables evaluates constant coefficients. -/
theorem _root_.Schubert.Splines.QuotientFinite.apply_eq_constantCoeff
    (map : MvPolynomial P K →ₐ[K] A)
    (hzero : ∀ coordinate, map (MvPolynomial.X coordinate) = 0)
    (polynomial : MvPolynomial P K) :
    map polynomial = algebraMap K A (MvPolynomial.constantCoeff polynomial) := by
  have hmap : map = MvPolynomial.aeval (fun _ : P => (0 : A)) :=
    MvPolynomial.algHom_ext fun coordinate => by simpa using hzero coordinate
  rw [hmap, MvPolynomial.aeval_zero']

variable [Algebra (MvPolynomial P K) A] [IsScalarTower K (MvPolynomial P K) A]

/-- Images of a polynomial basis span a quotient whose coordinate scalars vanish. -/
theorem _root_.Schubert.Splines.QuotientFinite.span_basis_of_X_zero [Fintype I]
    (basis : Module.Basis I (MvPolynomial P K) A) (quotient : A →ₐ[K] B)
    (hsurjective : Function.Surjective quotient)
    (hzero : ∀ coordinate,
      quotient (algebraMap (MvPolynomial P K) A (MvPolynomial.X coordinate)) = 0) :
    Submodule.span K (Set.range fun index => quotient (basis index)) = ⊤ := by
  apply top_unique
  intro value _
  obtain ⟨representative, rfl⟩ := hsurjective value
  rw [← basis.sum_repr representative, map_sum]
  apply Submodule.sum_mem
  intro index _
  rw [Algebra.smul_def, map_mul]
  have hcoefficient := _root_.Schubert.Splines.QuotientFinite.apply_eq_constantCoeff
    (quotient.comp (IsScalarTower.toAlgHom K (MvPolynomial P K) A)) hzero
    (basis.repr representative index)
  change quotient (algebraMap (MvPolynomial P K) A (basis.repr representative index)) = _
    at hcoefficient
  rw [hcoefficient, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨index, rfl⟩)

/-- Killing coordinate scalars makes a finite polynomial-basis quotient finite over coefficients. -/
theorem quotient_finite_of_variables_zero [Fintype I]
    (basis : Module.Basis I (MvPolynomial P K) A) (quotient : A →ₐ[K] B)
    (hsurjective : Function.Surjective quotient)
    (hzero : ∀ coordinate,
      quotient (algebraMap (MvPolynomial P K) A (MvPolynomial.X coordinate)) = 0) :
    Module.Finite K B := by
  constructor
  rw [← _root_.Schubert.Splines.QuotientFinite.span_basis_of_X_zero basis quotient hsurjective
    hzero]
  exact Submodule.fg_span (Set.finite_range _)

end Schubert.Splines
