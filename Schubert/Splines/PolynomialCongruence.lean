import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Defs

/-! # Polynomial evaluation congruence modulo an ideal

Generator differences in an ideal imply the same congruence for every polynomial.
The principal-ideal specialization supplies reflection divisibility once the
geometric variable differences are proved.
-/

namespace Schubert.Splines

universe u v w

variable {K : Type u} {S : Type v} {T : Type w}
variable [CommRing K] [CommRing S] [Algebra K S]

/-- Algebra homomorphisms congruent on variables are congruent on every polynomial. -/
theorem polynomial_hom_sub_mem (ideal : Ideal S)
    (left right : MvPolynomial T K →ₐ[K] S)
    (generators : ∀ index, left (MvPolynomial.X index) -
      right (MvPolynomial.X index) ∈ ideal) (polynomial : MvPolynomial T K) :
    left polynomial - right polynomial ∈ ideal := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    have hleft := left.commutes scalar
    have hright := right.commutes scalar
    rw [MvPolynomial.algebraMap_eq] at hleft hright
    rw [hleft, hright, sub_self]
    exact ideal.zero_mem
  | add first second hfirst hsecond =>
    simpa only [map_add, add_sub_add_comm] using ideal.add_mem hfirst hsecond
  | mul_X polynomial index hpolynomial =>
    simpa only [map_mul] using ideal.mul_sub_mul_mem hpolynomial (generators index)

/-- Substitution preserves congruence when all substituted variables are congruent. -/
theorem polynomial_aeval_sub_mem (ideal : Ideal S) (left right : T → S)
    (generators : ∀ index, left index - right index ∈ ideal)
    (polynomial : MvPolynomial T K) :
    MvPolynomial.aeval left polynomial - MvPolynomial.aeval right polynomial ∈ ideal := by
  apply polynomial_hom_sub_mem ideal (MvPolynomial.aeval left) (MvPolynomial.aeval right)
  intro index
  simpa only [MvPolynomial.aeval_X] using generators index

end Schubert.Splines
