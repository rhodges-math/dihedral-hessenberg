import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # The polynomial variable ideal and constant coefficients

The variable ideal is precisely the augmentation kernel over any coefficient ring.
-/

namespace Schubert.Splines

variable {K P : Type*} [CommRing K]

/-- A polynomial belongs to the variable ideal exactly when its constant coefficient vanishes. -/
theorem _root_.Schubert.Splines.PolynomialAugmentation.mem_iff_constantCoeff_zero (polynomial :
  MvPolynomial P K) :
    polynomial ∈ MvPolynomial.idealOfVars P K ↔
      MvPolynomial.constantCoeff polynomial = 0 := by
  rw [← pow_one (MvPolynomial.idealOfVars P K),
    MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h exponent hdegree
    have hexponent : exponent = 0 :=
      (Finsupp.degree_eq_zero_iff exponent).mp (by omega)
    subst exponent
    exact h

end Schubert.Splines
