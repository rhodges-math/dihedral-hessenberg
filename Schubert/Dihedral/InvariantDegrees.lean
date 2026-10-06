import Schubert.Dihedral.InvariantPolynomialRing
import Schubert.Dihedral.PolynomialGrading

/-! # Homogeneous degrees of the basic dihedral invariants

The auxiliary coordinates have degree one, and the two algebraically independent
invariant generators have exact degrees two and n.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The auxiliary coordinate u is homogeneous of degree one. -/
theorem auxiliaryU_isHomogeneous : auxiliaryU.IsHomogeneous 1 := by
  rw [auxiliaryU_eq_linearPolynomial]
  exact linearPolynomial_isHomogeneous _

/-- The auxiliary coordinate v is homogeneous of degree one. -/
theorem auxiliaryV_isHomogeneous : auxiliaryV.IsHomogeneous 1 := by
  rw [auxiliaryV_eq_linearPolynomial]
  exact linearPolynomial_isHomogeneous _

/-- The quadratic invariant is homogeneous of degree two. -/
theorem quadraticInvariant_isHomogeneous : quadraticInvariant.IsHomogeneous 2 :=
  auxiliaryU_isHomogeneous.mul auxiliaryV_isHomogeneous

/-- The signed higher invariant is homogeneous of degree n. -/
theorem higherInvariant_isHomogeneous (n : ℕ) : (higherInvariant n).IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.add
  · simpa only [one_mul] using auxiliaryU_isHomogeneous.pow n
  · simpa only [one_mul] using
      (auxiliaryV_isHomogeneous.pow n).C_mul ((-1 : ℂ) ^ n)

/-- The auxiliary coordinate u is nonzero. -/
theorem auxiliaryU_ne_zero : auxiliaryU ≠ 0 := by
  rw [← auxiliaryCoordinateEquiv_X_zero]
  exact (auxiliaryCoordinateEquiv.toRingEquiv.map_ne_zero_iff).mpr (by simp)

/-- The auxiliary coordinate v is nonzero. -/
theorem auxiliaryV_ne_zero : auxiliaryV ≠ 0 := by
  rw [← auxiliaryCoordinateEquiv_X_one]
  exact (auxiliaryCoordinateEquiv.toRingEquiv.map_ne_zero_iff).mpr (by simp)

/-- The quadratic invariant is nonzero. -/
theorem quadraticInvariant_ne_zero : quadraticInvariant ≠ 0 :=
  mul_ne_zero auxiliaryU_ne_zero auxiliaryV_ne_zero

/-- The signed higher invariant is nonzero for positive n. -/
theorem higherInvariant_ne_zero (n : ℕ) (hpositive : 0 < n) : higherInvariant n ≠ 0 := by
  have hmap : auxiliaryCoordinateEquiv
      ((MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) ^ n +
        MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n) = higherInvariant n := by
    simp [auxiliaryCoordinateEquiv, auxiliaryCoordinateHom, higherInvariant]
  rw [← hmap]
  exact (auxiliaryCoordinateEquiv.toRingEquiv.map_ne_zero_iff).mpr
    (auxiliary_higherInvariant_ne_zero n hpositive)

/-- The quadratic invariant has exact total degree two. -/
theorem quadraticInvariant_totalDegree : quadraticInvariant.totalDegree = 2 :=
  quadraticInvariant_isHomogeneous.totalDegree quadraticInvariant_ne_zero

/-- The signed higher invariant has exact total degree n for positive n. -/
theorem higherInvariant_totalDegree (n : ℕ) (hpositive : 0 < n) :
    (higherInvariant n).totalDegree = n :=
  (higherInvariant_isHomogeneous n).totalDegree (higherInvariant_ne_zero n hpositive)

end Schubert.Dihedral
