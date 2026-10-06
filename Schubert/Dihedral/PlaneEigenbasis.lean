import TauCeti.RepresentationTheory.Simple.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Schubert.Dihedral.RootPolynomial
import Schubert.Dihedral.FundamentalEigenvalues
import Schubert.Dihedral.Invariants
import Schubert.Dihedral.RotationEigenvalueSeparation
import Schubert.FiniteGroupCharacters.TwoDimensionalIrreducible

/-! # An eigenbasis and irreducibility of the defining dihedral representation

The complex plane has basis (1,i),(1,-i). The first simple reflection interchanges
these lines with coefficient minus one, and the fundamental rotation has inverse eigenvalues.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The two complex axial eigenvectors form a basis of the complex plane. -/
theorem exists_plane_eigenbasis : ∃ basis : Module.Basis (Fin 2) ℂ ComplexPlane,
    basis 0 = ![1, Complex.I] ∧ basis 1 = ![1, -Complex.I] := by
  let vectors : Fin 2 → ComplexPlane := ![![1, Complex.I], ![1, -Complex.I]]
  have hindependent : LinearIndependent ℂ vectors := by
    apply Fintype.linearIndependent_iff.mpr
    intro coefficients hsum index
    have hfirst := congrFun hsum 0
    have hsecond := congrFun hsum 1
    simp [Fin.sum_univ_two, vectors, Pi.smul_apply] at hfirst hsecond
    have hfactor : (coefficients 0 - coefficients 1) * Complex.I = 0 := by
      linear_combination hsecond
    have hdifference : coefficients 0 - coefficients 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right Complex.I_ne_zero
    fin_cases index
    · change coefficients 0 = 0
      linear_combination (hfirst + hdifference) / 2
    · change coefficients 1 = 0
      linear_combination (hfirst - hdifference) / 2
  let basis := Module.Basis.mk hindependent
    (hindependent.span_eq_top_of_card_eq_finrank (by simp [ComplexPlane])).ge
  exact ⟨basis, Module.Basis.mk_apply _ _ 0, Module.Basis.mk_apply _ _ 1⟩

/-- The fundamental rotation has inverse eigenvalue on the first axial vector. -/
theorem vectorRepresentation_rotation_first (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    vectorRepresentation n (rotation n) ![1, Complex.I] =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ • ![1, Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (rotation n) ![1, Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryU_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryU_eq_linearPolynomial]
  exact polynomialAction_rotation_auxiliaryU n hthree

/-- The fundamental rotation has positive eigenvalue on the second axial vector. -/
theorem vectorRepresentation_rotation_second (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    vectorRepresentation n (rotation n) ![1, -Complex.I] =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) • ![1, -Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (rotation n) ![1, -Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryV_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryV_eq_linearPolynomial]
  exact polynomialAction_rotation_auxiliaryV n hthree

/-- The first simple reflection sends the first axial vector to minus the second. -/
theorem vectorRepresentation_firstSimple_first (n : ℕ) [NeZero n] :
    vectorRepresentation n (firstSimpleReflection n) ![1, Complex.I] =
      (-1 : ℂ) • ![1, -Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (firstSimpleReflection n) ![1, Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryU_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryV_eq_linearPolynomial,
    polynomialAction_firstSimple_auxiliaryU]
  simp

/-- The first simple reflection sends the second axial vector to minus the first. -/
theorem vectorRepresentation_firstSimple_second (n : ℕ) [NeZero n] :
    vectorRepresentation n (firstSimpleReflection n) ![1, -Complex.I] =
      (-1 : ℂ) • ![1, Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (firstSimpleReflection n) ![1, -Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryV_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryU_eq_linearPolynomial,
    polynomialAction_firstSimple_auxiliaryV]
  simp

/-- The complex plane representation is irreducible for dihedral order at least three. -/
theorem vectorRepresentation_irreducible (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Representation.IsIrreducible (vectorRepresentation n) := by
  obtain ⟨basis, hfirst, hsecond⟩ := exists_plane_eigenbasis
  apply _root_.Schubert.FiniteGroupCharacters.DiagonalSwap.irreducible
    (vectorRepresentation n) basis (rotation n) (firstSimpleReflection n)
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) (-1) (-1)
  · simpa only [pow_one] using rotationEigenvalue_inverse_pow_ne n 1 (by omega) (by omega)
  · exact neg_ne_zero.mpr one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero
  · rw [hfirst]
    exact vectorRepresentation_rotation_first n hthree
  · rw [hsecond]
    exact vectorRepresentation_rotation_second n hthree
  · rw [hfirst, hsecond]
    exact vectorRepresentation_firstSimple_first n
  · rw [hfirst, hsecond]
    exact vectorRepresentation_firstSimple_second n
/-- The finite-dimensional plane realization is a simple representation object. -/
theorem vectorRepresentation_simple (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    CategoryTheory.Simple (FDRep.of (vectorRepresentation n)) :=
  (FDRep.simple_iff_isIrreducible _).mpr (vectorRepresentation_irreducible n hthree)
end Schubert.Dihedral



