import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Independence of polynomials with distinct leading degrees

A finite linear dependence has a largest leading degree. Its coefficient cannot cancel
when all members of the family have distinct leading degrees.
-/

noncomputable section

open scoped MonomialOrder

namespace Schubert.Dihedral

/-- Nonzero polynomials with pairwise distinct leading degrees are linearly independent. -/
theorem _root_.Schubert.Dihedral.LeadingDegree.independent_of_injective {field index coordinate :
  Type*}
    [Field field] (order : MonomialOrder coordinate)
    (family : index → MvPolynomial coordinate field)
    (hnonzero : ∀ item, family item ≠ 0)
    (hinjective : Function.Injective (fun item => order.degree (family item))) :
    LinearIndependent field family := by
  classical
  apply linearIndependent_iff.mpr
  intro coefficients hsum
  by_contra hnonzeroCoefficients
  obtain ⟨chosen, hchosen, hmaximal⟩ := coefficients.support.exists_max_image
    (fun item => order.toSyn (order.degree (family item)))
    (Finsupp.support_nonempty_iff.mpr hnonzeroCoefficients)
  have heval := congrArg (fun polynomial : MvPolynomial coordinate field =>
    polynomial.coeff (order.degree (family chosen))) hsum
  rw [Finsupp.linearCombination_apply] at heval
  simp only [Finsupp.sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, smul_eq_mul] at heval
  rw [Finset.sum_eq_single chosen] at heval
  · have hscalar : coefficients chosen ≠ 0 := Finsupp.mem_support_iff.mp hchosen
    have hleading : (family chosen).coeff (order.degree (family chosen)) ≠ 0 :=
      (order.coeff_degree_ne_zero_iff).mpr (hnonzero chosen)
    exact mul_ne_zero hscalar hleading heval
  · intro other hother hotherNe
    have hstrict : order.degree (family other) ≺[order] order.degree (family chosen) := by
      apply lt_of_le_of_ne (hmaximal other hother)
      intro hequal
      exact hotherNe (hinjective (order.toSyn.injective hequal))
    rw [order.coeff_eq_zero_of_lt hstrict, mul_zero]
  · intro hnotChosen
    exact False.elim (hnotChosen hchosen)

end Schubert.Dihedral
