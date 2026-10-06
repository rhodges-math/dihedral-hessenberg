import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! # Binary monomial exponents in a fixed degree -/

noncomputable section
namespace Schubert.Dihedral

/-- The degree of a binary exponent is the sum of its two coordinates. -/
theorem binaryExponent_degree (exponent : Fin 2 →₀ ℕ) :
    exponent.degree = exponent 0 + exponent 1 := by
  rw [Finsupp.degree_eq_sum]
  exact Fin.sum_univ_two _

/-- A binary degree exponent is indexed by its first coordinate between zero and the degree. -/
def binaryExponentEquiv (degree : ℕ) :
    {exponent : Fin 2 →₀ ℕ // exponent.degree = degree} ≃ Fin (degree + 1) where
  toFun exponent := ⟨exponent.val 0, by
    have hdegree := exponent.property
    rw [binaryExponent_degree] at hdegree
    omega⟩
  invFun index := ⟨Finsupp.equivFunOnFinite.symm ![index.val, degree - index.val], by
    rw [binaryExponent_degree]
    change index.val + (degree - index.val) = degree
    have hbound := index.isLt
    omega⟩
  left_inv exponent := by
    apply Subtype.ext
    apply Finsupp.ext
    intro coordinate
    fin_cases coordinate
    · rfl
    · change degree - exponent.val 0 = exponent.val 1
      have hdegree := exponent.property
      rw [binaryExponent_degree] at hdegree
      omega
  right_inv index := by
    apply Fin.ext
    rfl

/-- The first coordinate is the selected binary exponent index. -/
theorem binaryExponentEquiv_first (degree : ℕ) (index : Fin (degree + 1)) :
    ((binaryExponentEquiv degree).symm index).val 0 = index.val := rfl

/-- The second coordinate complements the selected exponent to the total degree. -/
theorem binaryExponentEquiv_second (degree : ℕ) (index : Fin (degree + 1)) :
    ((binaryExponentEquiv degree).symm index).val 1 = degree - index.val := rfl

end Schubert.Dihedral
