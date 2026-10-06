import Schubert.Dihedral.DistinctLeadingDegrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Schubert.Dihedral.InvariantGeneration

/-! # Independence of the two basic invariant generators

Lexicographic leading degrees distinguish every monomial in the two basic invariants.
The invertible auxiliary coordinate change transports this independence to the official
polynomial model.
-/

noncomputable section

open scoped MonomialOrder

namespace Schubert.Dihedral

/-- The auxiliary higher invariant has leading monomial x to power n. -/
theorem auxiliary_higherInvariant_leadingDegree (n : ℕ) (hpositive : 0 < n) :
    (MonomialOrder.lex (σ := Fin 2)).degree
      ((MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) ^ n +
        MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n) =
      n • Finsupp.single 0 1 := by
  let order := MonomialOrder.lex (σ := Fin 2)
  have hfirst : (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) ^ n ≠ 0 := by simp
  have hsecond : (MvPolynomial.C ((-1 : ℂ) ^ n) : CoordinatePolynomial) ≠ 0 := by simp
  have hlast : (MvPolynomial.X (1 : Fin 2) : CoordinatePolynomial) ^ n ≠ 0 := by simp
  have hstrict : n • Finsupp.single (1 : Fin 2) 1 ≺[order]
      n • Finsupp.single (0 : Fin 2) 1 := by
    rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
    refine ⟨0, ?_, ?_⟩
    · intro coordinate hcoordinate
      exact False.elim (Fin.not_lt_zero _ hcoordinate)
    · simpa using hpositive
  have hdegree := order.degree_add_of_lt (f := MvPolynomial.X 0 ^ n)
    (g := MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n)
    (by simpa only [order.degree_mul hsecond hlast, order.degree_C,
      order.degree_pow, order.degree_X, zero_add] using hstrict)
  simpa only [order.degree_pow, order.degree_X] using hdegree

/-- The auxiliary higher invariant is nonzero. -/
theorem auxiliary_higherInvariant_ne_zero (n : ℕ) (hpositive : 0 < n) :
    ((MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) ^ n +
      MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n) ≠ 0 := by
  apply (MonomialOrder.lex (σ := Fin 2)).ne_zero_of_degree_ne_zero
  rw [auxiliary_higherInvariant_leadingDegree n hpositive]
  intro hequal
  have hcoordinate := congrArg (fun exponent : Fin 2 →₀ ℕ => exponent 0) hequal
  have hzero : n = 0 := by simpa using hcoordinate
  exact (ne_of_gt hpositive) hzero

/-- Exponents of invariant monomials are determined by their leading degrees. -/
theorem basicInvariant_leadingDegree_injective (n : ℕ) (hpositive : 0 < n) :
    Function.Injective (fun exponent : Fin 2 →₀ ℕ =>
      exponent 0 • (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) +
        exponent 1 • (n • Finsupp.single 0 1)) := by
  intro first second hequal
  have hzero := congrArg (fun exponent : Fin 2 →₀ ℕ => exponent 0) hequal
  have hone := congrArg (fun exponent : Fin 2 →₀ ℕ => exponent 1) hequal
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at hzero hone
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate
  · exact hone
  · change first (1 : Fin 2) = second 1
    apply Nat.mul_right_cancel hpositive
    rw [hone] at hzero
    exact Nat.add_left_cancel hzero

end Schubert.Dihedral
