import Schubert.Dihedral.RootObjects
import Schubert.Dihedral.RootPolynomialAction
import Schubert.Dihedral.RootSignedConjugation

/-! # Reflection and polynomial action on root vectors -/

noncomputable section

namespace Schubert.Dihedral

/-- The positive-root carrier is finite through its alternating numbering. -/
instance positiveRootFintype (n : ℕ) : Fintype (PositiveRoot n) :=
  Fintype.ofEquiv (PositiveRootIndex n) (positiveRootEquiv n)

namespace PositiveRoot

/-- The form of a vector agrees with the form at its recovered index. -/
theorem form_index {n : ℕ} (alpha : PositiveRoot n) :
    alpha.form = rootPolynomial n alpha.index := by
  change linearPolynomial (complexify alpha.val) =
    linearPolynomial (complexify (positiveRoot n alpha.index))
  rw [index_val]

/-- Polynomial action is the linear form of the real root image. -/
theorem action_form {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha : PositiveRoot n) :
    polynomialAction n element alpha.form =
      linearPolynomial (complexify (realAction n element alpha.val)) := by
  rw [form, polynomialAction_linearPolynomial,
    realAction_complexify n element alpha.val (Or.inl alpha.property)]

/-- Distinct positive vectors have distinct alternating indices. -/
theorem index_injective (n : ℕ) : Function.Injective (index (n := n)) :=
  (positiveRootEquiv n).symm.injective

/-- Every positive-vector form is nonzero. -/
theorem form_ne_zero {n : ℕ} (alpha : PositiveRoot n) : alpha.form ≠ 0 := by
  rw [form_index]
  exact rootPolynomial_ne_zero n alpha.index

/-- Distinct positive-vector forms remain nonproportional after a common group action. -/
theorem action_not_proportional {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha beta : PositiveRoot n) (hne : alpha ≠ beta) (scalar : ℂ) :
    polynomialAction n element alpha.form ≠
      MvPolynomial.C scalar * polynomialAction n element beta.form := by
  rw [form_index, form_index]
  exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_nonproportional n element alpha.index
    beta.index
    (fun heq => hne (index_injective n heq)) scalar

/-- Distinct positive-vector forms have no common nonunit divisor after a common action. -/
theorem action_relPrime {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha beta : PositiveRoot n) (hne : alpha ≠ beta) :
    IsRelPrime (polynomialAction n element alpha.form)
      (polynomialAction n element beta.form) := by
  rw [form_index, form_index]
  exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime n element alpha.index beta.index
    (fun heq => hne (index_injective n heq))

/-- Either sign of a root image identifies its conjugated group reflection. -/
theorem signed_conjugation {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha beta : PositiveRoot n)
    (himage : realAction n element alpha.val = beta.val ∨
      realAction n element alpha.val = -beta.val) :
    beta.reflection = element * alpha.reflection * element⁻¹ := by
  apply rootReflection_of_signed_image n element alpha.index beta.index
  have haction := realAction_complexify n element alpha.val (Or.inl alpha.property)
  rcases himage with hpositive | hnegative
  · left
    simpa only [complexPositiveRoot, index_val, hpositive] using haction.symm
  · right
    have hneg : complexify (-beta.val) = -complexify beta.val := by
      funext coordinate
      simp only [complexify, Pi.neg_apply, Complex.ofReal_neg]
    simpa only [complexPositiveRoot, index_val, hnegative, hneg] using haction.symm

end PositiveRoot

end Schubert.Dihedral
