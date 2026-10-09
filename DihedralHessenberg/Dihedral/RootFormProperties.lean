import DihedralHessenberg.Dihedral.RootObjectAction

/-! # Polynomial independence properties of positive root vectors -/

namespace Schubert.Dihedral.PositiveRoot

/-- Distinct positive vectors define nonproportional polynomial forms. -/
theorem form_not_proportional {n : ℕ} (alpha beta : PositiveRoot n)
    (hne : alpha ≠ beta) (scalar : ℂ) :
    alpha.form ≠ MvPolynomial.C scalar * beta.form := by
  rw [form_index, form_index]
  exact rootPolynomial_not_scalar_multiple n alpha.index beta.index
    (fun heq => hne (index_injective n heq)) scalar

/-- Distinct positive-vector forms are not associated in the polynomial ring. -/
theorem form_not_associated {n : ℕ} (alpha beta : PositiveRoot n) (hne : alpha ≠ beta) :
    ¬ Associated alpha.form beta.form := by
  rw [form_index, form_index]
  exact rootPolynomial_not_associated n alpha.index beta.index
    (fun heq => hne (index_injective n heq))

/-- Distinct positive-vector forms have no common nonunit divisor. -/
theorem form_relPrime {n : ℕ} (alpha beta : PositiveRoot n) (hne : alpha ≠ beta) :
    IsRelPrime alpha.form beta.form := by
  rw [form_index, form_index]
  exact rootPolynomial_isRelPrime n alpha.index beta.index
    (fun heq => hne (index_injective n heq))

/-- Distinct positive-vector forms remain nonassociated after a common group action. -/
theorem action_not_associated {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha beta : PositiveRoot n) (hne : alpha ≠ beta) :
    ¬ Associated (polynomialAction n element alpha.form)
      (polynomialAction n element beta.form) := by
  rw [form_index, form_index]
  exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_nonassociate n element alpha.index
    beta.index
    (fun heq => hne (index_injective n heq))

end Schubert.Dihedral.PositiveRoot
