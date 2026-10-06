import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring

/-! # Coefficients under diagonal polynomial substitution

Scaling each of two variables preserves monomial exponents and scales the coefficient
by the corresponding powers. Fixed polynomials therefore obey coefficient eigenvalue
constraints.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Diagonal substitution scales a two-variable monomial by its eigenvalue. -/
theorem aeval_diagonal_monomial {field : Type*} [CommSemiring field]
    (first second scalar : field) (exponent : Fin 2 →₀ ℕ) :
    MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then MvPolynomial.C first * MvPolynomial.X (0 : Fin 2)
        else MvPolynomial.C second * MvPolynomial.X (1 : Fin 2))
      (MvPolynomial.monomial exponent scalar) =
      MvPolynomial.monomial exponent
        (scalar * (first ^ exponent 0 * second ^ exponent 1)) := by
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [MvPolynomial.monomial_fin_two]
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Fin.isValue, hone, ↓reduceIte, mul_pow, MvPolynomial.algebraMap_eq]
  ring

/-- The coefficient of a diagonally substituted polynomial has the monomial eigenvalue. -/
theorem coeff_aeval_diagonal {field : Type*} [CommSemiring field]
    (first second : field) (polynomial : MvPolynomial (Fin 2) field)
    (exponent : Fin 2 →₀ ℕ) :
    (MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then MvPolynomial.C first * MvPolynomial.X (0 : Fin 2)
        else MvPolynomial.C second * MvPolynomial.X (1 : Fin 2)) polynomial).coeff exponent =
      polynomial.coeff exponent * (first ^ exponent 0 * second ^ exponent 1) := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | monomial other scalar =>
    rw [aeval_diagonal_monomial]
    simp only [MvPolynomial.coeff_monomial]
    split_ifs with hequal
    · subst other
      rfl
    · simp
  | add left right hleft hright =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hleft, hright, add_mul]

/-- A nonzero coefficient of a fixed polynomial must have diagonal eigenvalue one. -/
theorem diagonal_eigenvalue_eq_one_of_fixed {field : Type*} [CommRing field]
    [IsDomain field] (first second : field) (polynomial : MvPolynomial (Fin 2) field)
    (exponent : Fin 2 →₀ ℕ)
    (hfixed : MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then MvPolynomial.C first * MvPolynomial.X (0 : Fin 2)
        else MvPolynomial.C second * MvPolynomial.X (1 : Fin 2)) polynomial = polynomial)
    (hnonzero : polynomial.coeff exponent ≠ 0) :
    first ^ exponent 0 * second ^ exponent 1 = 1 := by
  have hequal := congrArg (fun p : MvPolynomial (Fin 2) field => p.coeff exponent) hfixed
  rw [coeff_aeval_diagonal] at hequal
  exact (mul_left_cancel₀ hnonzero (hequal.trans (mul_one _).symm))

end Schubert.Dihedral
