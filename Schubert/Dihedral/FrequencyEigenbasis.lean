import Schubert.Dihedral.FrequencyRepresentation
import Schubert.Dihedral.PlaneEigenbasis
import Schubert.Dihedral.RotationTraceSeparation
import Schubert.FiniteGroupCharacters.CharacterBasis

/-! # Eigenvectors and irreducibility of dihedral frequencies

The two axial eigenlines persist under frequency pullback. They are distinct exactly
away from the doubled frequencies divisible by the rotation order.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every rotation acts on u by the inverse power of its primitive eigenvalue. -/
theorem polynomialAction_r_auxiliaryU_pow (n : ℕ) [NeZero n] (exponent : ZMod n) :
    polynomialAction n (.r exponent) auxiliaryU =
      MvPolynomial.C ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ exponent.val) *
        auxiliaryU := by
  rw [polynomialAction_r_auxiliaryU]
  have hangle : (((-(2 * Real.pi * exponent.val / n) : ℝ) : ℂ) * Complex.I) =
      (exponent.val : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I / n) := by
    push_cast
    ring
  rw [hangle, Complex.exp_nat_mul, Complex.exp_neg]

/-- Every rotation acts on v by the positive power of its primitive eigenvalue. -/
theorem polynomialAction_r_auxiliaryV_pow (n : ℕ) [NeZero n] (exponent : ZMod n) :
    polynomialAction n (.r exponent) auxiliaryV =
      MvPolynomial.C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent.val) *
        auxiliaryV := by
  rw [polynomialAction_r_auxiliaryV]
  have hangle : (((2 * Real.pi * exponent.val / n : ℝ) : ℂ) * Complex.I) =
      (exponent.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / n) := by
    push_cast
    ring
  rw [hangle, Complex.exp_nat_mul]

/-- Every rotation is diagonal on the first axial vector. -/
theorem vectorRepresentation_r_first (n : ℕ) [NeZero n] (exponent : ZMod n) :
    vectorRepresentation n (.r exponent) ![1, Complex.I] =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ exponent.val • ![1, Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (.r exponent) ![1, Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryU_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryU_eq_linearPolynomial]
  exact polynomialAction_r_auxiliaryU_pow n exponent

/-- Every rotation is diagonal on the second axial vector. -/
theorem vectorRepresentation_r_second (n : ℕ) [NeZero n] (exponent : ZMod n) :
    vectorRepresentation n (.r exponent) ![1, -Complex.I] =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent.val • ![1, -Complex.I] := by
  apply linearPolynomial_injective
  change linearPolynomial (vectorOperator n (.r exponent) ![1, -Complex.I]) = _
  rw [← polynomialAction_linearPolynomial, ← auxiliaryV_eq_linearPolynomial,
    linearPolynomial_smul, ← auxiliaryV_eq_linearPolynomial]
  exact polynomialAction_r_auxiliaryV_pow n exponent

/-- Frequency rotation has the inverse frequency eigenvalue on the first axial vector. -/
theorem frequencyRepresentation_rotation_first (n : ℕ) [NeZero n] (frequency : ZMod n) :
    frequencyRepresentation n frequency (rotation n) ![1, Complex.I] =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency.val • ![1, Complex.I] := by
  change vectorRepresentation n (dihedralFrequencyHom n frequency (rotation n)) _ = _
  rw [rotation_eq_r_one, dihedralFrequencyHom_r, mul_one]
  exact vectorRepresentation_r_first n frequency

/-- Frequency rotation has the positive frequency eigenvalue on the second axial vector. -/
theorem frequencyRepresentation_rotation_second (n : ℕ) [NeZero n] (frequency : ZMod n) :
    frequencyRepresentation n frequency (rotation n) ![1, -Complex.I] =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency.val • ![1, -Complex.I] := by
  change vectorRepresentation n (dihedralFrequencyHom n frequency (rotation n)) _ = _
  rw [rotation_eq_r_one, dihedralFrequencyHom_r, mul_one]
  exact vectorRepresentation_r_second n frequency

/-- Frequency pullback retains the signed first-to-second simple-reflection interchange. -/
theorem _root_.Schubert.Dihedral.Frequency.s1_first (n : ℕ) [NeZero n] (frequency : ZMod n) :
    frequencyRepresentation n frequency (firstSimpleReflection n) ![1, Complex.I] =
      (-1 : ℂ) • ![1, -Complex.I] := by
  change vectorRepresentation n (DihedralGroup.sr (frequency * 0)) _ = _
  rw [mul_zero]
  exact vectorRepresentation_firstSimple_first n

/-- Frequency pullback retains the signed second-to-first simple-reflection interchange. -/
theorem _root_.Schubert.Dihedral.Frequency.s1_second (n : ℕ) [NeZero n] (frequency : ZMod n) :
    frequencyRepresentation n frequency (firstSimpleReflection n) ![1, -Complex.I] =
      (-1 : ℂ) • ![1, Complex.I] := by
  change vectorRepresentation n (DihedralGroup.sr (frequency * 0)) _ = _
  rw [mul_zero]
  exact vectorRepresentation_firstSimple_second n

/-- Every nonexceptional frequency representation is irreducible. -/
theorem frequencyRepresentation_irreducible (n : ℕ) [NeZero n] (frequency : ZMod n)
    (hfrequency : ¬ n ∣ 2 * frequency.val) :
    Representation.IsIrreducible (frequencyRepresentation n frequency) := by
  obtain ⟨basis, hfirst, hsecond⟩ := exists_plane_eigenbasis
  apply _root_.Schubert.FiniteGroupCharacters.DiagonalSwap.irreducible
    (frequencyRepresentation n frequency) basis (rotation n) (firstSimpleReflection n)
    ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency.val)
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency.val) (-1) (-1)
  · exact fun hequal => hfrequency ((rotationEigenvalue_inverse_pow_eq_iff _ _).mp hequal)
  · exact neg_ne_zero.mpr one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero
  · rw [hfirst]
    exact frequencyRepresentation_rotation_first n frequency
  · rw [hsecond]
    exact frequencyRepresentation_rotation_second n frequency
  · rw [hfirst, hsecond]
    exact _root_.Schubert.Dihedral.Frequency.s1_first n frequency
  · rw [hfirst, hsecond]
    exact _root_.Schubert.Dihedral.Frequency.s1_second n frequency

/-- Nonexceptional frequency objects are simple finite-dimensional representation objects. -/
theorem frequencyFDRep_simple (n : ℕ) [NeZero n] (frequency : ZMod n)
    (hfrequency : ¬ n ∣ 2 * frequency.val) : CategoryTheory.Simple (frequencyFDRep n frequency) :=
  (FDRep.simple_iff_isIrreducible _).mpr
    (frequencyRepresentation_irreducible n frequency hfrequency)

/-- The frequency trace of the fundamental rotation is its inverse eigenvalue sum. -/
theorem _root_.Schubert.Dihedral.Frequency.character_rotation (n : ℕ) [NeZero n] (frequency : ZMod
  n) :
    (frequencyRepresentation n frequency).character (rotation n) =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency.val +
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency.val := by
  obtain ⟨basis, hfirst, hsecond⟩ := exists_plane_eigenbasis
  rw [_root_.Schubert.FiniteGroupCharacters.Eigenbasis.character_eq_sum
    (frequencyRepresentation n frequency) basis (rotation n)
    ![(Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency.val,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency.val]]
  · simp [Fin.sum_univ_two]
  · intro index
    fin_cases index
    · simpa [hfirst] using frequencyRepresentation_rotation_first n frequency
    · simpa [hsecond] using frequencyRepresentation_rotation_second n frequency

end Schubert.Dihedral
