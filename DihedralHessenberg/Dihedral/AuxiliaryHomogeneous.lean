import DihedralHessenberg.Dihedral.InvariantDegrees
import TauCeti.RingTheory.MvPolynomial.Finrank

/-! # Preservation of degree by the auxiliary polynomial coordinate equivalence -/

noncomputable section
namespace Schubert.Dihedral

/-- Auxiliary coordinate substitution preserves the polynomial homogeneous degree. -/
theorem auxiliaryCoordinateHom_homogeneous {degree : ℕ} {polynomial : CoordinatePolynomial}
    (hpolynomial : polynomial.IsHomogeneous degree) :
    (auxiliaryCoordinateHom polynomial).IsHomogeneous degree := by
  change (MvPolynomial.aeval ![auxiliaryU, auxiliaryV] polynomial).IsHomogeneous degree
  have hcoordinates : ∀ coordinate : Fin 2,
      (![auxiliaryU, auxiliaryV] coordinate).IsHomogeneous 1 := by
    intro coordinate
    fin_cases coordinate
    · exact auxiliaryU_isHomogeneous
    · exact auxiliaryV_isHomogeneous
  simpa only [one_mul] using hpolynomial.aeval _ hcoordinates

/-- Inverse auxiliary substitution also preserves the homogeneous degree. -/
theorem auxiliaryCoordinateInverse_homogeneous {degree : ℕ} {polynomial : CoordinatePolynomial}
    (hpolynomial : polynomial.IsHomogeneous degree) :
    (auxiliaryCoordinateInverseHom polynomial).IsHomogeneous degree := by
  unfold auxiliaryCoordinateInverseHom
  have hcoordinates : ∀ coordinate : Fin 2,
      (![MvPolynomial.C ((2 : ℂ)⁻¹) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X 0 - MvPolynomial.X 1)]
        coordinate : CoordinatePolynomial).IsHomogeneous 1 := by
    intro coordinate
    fin_cases coordinate
    · exact ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).add
        (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))).C_mul _
    · exact ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).sub
        (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))).C_mul _
  simpa only [one_mul] using hpolynomial.aeval _ hcoordinates

/-- The polynomial degree piece is preserved by the auxiliary coordinate equivalence. -/
def auxiliaryPieceEquiv (degree : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree ≃ₗ[ℂ]
      MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree where
  toFun value := ⟨auxiliaryCoordinateHom value.val,
    auxiliaryCoordinateHom_homogeneous value.property⟩
  invFun value := ⟨auxiliaryCoordinateInverseHom value.val,
    auxiliaryCoordinateInverse_homogeneous value.property⟩
  left_inv value := by
    apply Subtype.ext
    change auxiliaryCoordinateEquiv.symm (auxiliaryCoordinateEquiv value.val) = value.val
    exact auxiliaryCoordinateEquiv.symm_apply_apply value.val
  right_inv value := by
    apply Subtype.ext
    change auxiliaryCoordinateEquiv (auxiliaryCoordinateEquiv.symm value.val) = value.val
    exact auxiliaryCoordinateEquiv.apply_symm_apply value.val
  map_add' first second := Subtype.ext (map_add _ first.val second.val)
  map_smul' scalar value := Subtype.ext (map_smul _ scalar value.val)

/-- Auxiliary monomials give a basis of the polynomial homogeneous component. -/
def auxiliaryPieceBasis (degree : ℕ) :
    Module.Basis {exponent : Fin 2 →₀ ℕ // exponent.degree = degree} ℂ
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree) :=
  (TauCeti.homogeneousMonomialBasis degree).map (auxiliaryPieceEquiv degree)

/-- Each auxiliary homogeneous basis vector is the substituted monomial. -/
theorem auxiliaryPieceBasis_apply (degree : ℕ)
    (exponent : {exponent : Fin 2 →₀ ℕ // exponent.degree = degree}) :
    (auxiliaryPieceBasis degree exponent).val =
      auxiliaryCoordinateHom (MvPolynomial.monomial exponent.val 1) := by
  rw [auxiliaryPieceBasis, Module.Basis.map_apply]
  change auxiliaryCoordinateHom (TauCeti.homogeneousMonomialBasis degree exponent).val = _
  rw [TauCeti.coe_homogeneousMonomialBasis]

end Schubert.Dihedral
