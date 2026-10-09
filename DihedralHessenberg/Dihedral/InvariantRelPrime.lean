import Mathlib.RingTheory.Polynomial.UniqueFactorization
import DihedralHessenberg.Dihedral.InvariantDegrees
import DihedralHessenberg.Dihedral.RootPolynomial

/-! # Relative primeness of the basic invariant generators

The auxiliary coordinates are irreducible. Evaluation on either coordinate axis
shows that neither divides the higher invariant, so their product is relatively prime to it.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The auxiliary coordinate u is irreducible. -/
theorem auxiliaryU_irreducible : Irreducible auxiliaryU := by
  rw [auxiliaryU_eq_linearPolynomial]
  apply linearPolynomial_irreducible
  intro hzero
  have hfirst := congrFun hzero 0
  simp at hfirst

/-- The auxiliary coordinate v is irreducible. -/
theorem auxiliaryV_irreducible : Irreducible auxiliaryV := by
  rw [auxiliaryV_eq_linearPolynomial]
  apply linearPolynomial_irreducible
  intro hzero
  have hfirst := congrFun hzero 0
  simp at hfirst

/-- The auxiliary coordinate u does not divide the higher invariant for positive n. -/
theorem auxiliaryU_not_dvd_higherInvariant (n : ℕ) (hpositive : 0 < n) :
    ¬ auxiliaryU ∣ higherInvariant n := by
  rintro ⟨polynomial, hequal⟩
  have hinverseU : auxiliaryCoordinateEquiv.symm auxiliaryU = MvPolynomial.X 0 := by
    rw [← auxiliaryCoordinateEquiv_X_zero, AlgEquiv.symm_apply_apply]
  have hinverseV : auxiliaryCoordinateEquiv.symm auxiliaryV = MvPolynomial.X 1 := by
    rw [← auxiliaryCoordinateEquiv_X_one, AlgEquiv.symm_apply_apply]
  have heval := congrArg
    (fun polynomial => MvPolynomial.eval ![(0 : ℂ), 1]
      (auxiliaryCoordinateEquiv.symm polynomial)) hequal
  simp [higherInvariant, hinverseU, hinverseV, hpositive.ne'] at heval

/-- The auxiliary coordinate v does not divide the higher invariant for positive n. -/
theorem auxiliaryV_not_dvd_higherInvariant (n : ℕ) (hpositive : 0 < n) :
    ¬ auxiliaryV ∣ higherInvariant n := by
  rintro ⟨polynomial, hequal⟩
  have hinverseU : auxiliaryCoordinateEquiv.symm auxiliaryU = MvPolynomial.X 0 := by
    rw [← auxiliaryCoordinateEquiv_X_zero, AlgEquiv.symm_apply_apply]
  have hinverseV : auxiliaryCoordinateEquiv.symm auxiliaryV = MvPolynomial.X 1 := by
    rw [← auxiliaryCoordinateEquiv_X_one, AlgEquiv.symm_apply_apply]
  have heval := congrArg
    (fun polynomial => MvPolynomial.eval ![(1 : ℂ), 0]
      (auxiliaryCoordinateEquiv.symm polynomial)) hequal
  simp [higherInvariant, hinverseU, hinverseV, hpositive.ne'] at heval

/-- The auxiliary coordinate u is relatively prime to the higher invariant. -/
theorem auxiliaryU_isRelPrime_higherInvariant (n : ℕ) (hpositive : 0 < n) :
    IsRelPrime auxiliaryU (higherInvariant n) :=
  auxiliaryU_irreducible.isRelPrime_iff_not_dvd.mpr
    (auxiliaryU_not_dvd_higherInvariant n hpositive)

/-- The auxiliary coordinate v is relatively prime to the higher invariant. -/
theorem auxiliaryV_isRelPrime_higherInvariant (n : ℕ) (hpositive : 0 < n) :
    IsRelPrime auxiliaryV (higherInvariant n) :=
  auxiliaryV_irreducible.isRelPrime_iff_not_dvd.mpr
    (auxiliaryV_not_dvd_higherInvariant n hpositive)

/-- The two basic invariant generators are relatively prime for positive n. -/
theorem basicInvariants_isRelPrime (n : ℕ) (hpositive : 0 < n) :
    IsRelPrime quadraticInvariant (higherInvariant n) :=
  (auxiliaryU_isRelPrime_higherInvariant n hpositive).mul_left
    (auxiliaryV_isRelPrime_higherInvariant n hpositive)

end Schubert.Dihedral

