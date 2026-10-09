import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import DihedralHessenberg.Splines.BasisIdealCoordinates
import DihedralHessenberg.Splines.IdealScalarExtension
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Descent of a basis through an algebra augmentation

A basis over an augmented complex algebra descends to a complex basis after
quotienting by the extension of the augmentation kernel.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A basis over an augmented algebra descends, with its vectors as quotient classes. -/
theorem exists_augmentation_quotient_basis {R A I : Type*} [CommRing R] [CommRing A]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
    (augmentation : R →ₐ[ℂ] ℂ) (basis : Module.Basis I R A) :
    ∃ quotientBasis : Module.Basis I ℂ
        (A ⧸ Ideal.map (algebraMap R A) (RingHom.ker augmentation)),
      ∀ index, quotientBasis index =
        Ideal.Quotient.mk (Ideal.map (algebraMap R A) (RingHom.ker augmentation))
          (basis index) := by
  classical
  let ideal := Ideal.map (algebraMap R A) (RingHom.ker augmentation)
  let coordinates : A →ₗ[ℂ] (I →₀ ℂ) :=
    (Finsupp.mapRange.linearMap augmentation.toLinearMap).comp
      (basis.repr.toLinearMap.restrictScalars ℂ)
  have hkernel (value : A) : coordinates value = 0 ↔ value ∈ ideal := by
    have hmembership : value ∈ ideal ↔ value ∈
        (RingHom.ker augmentation) • (⊤ : Submodule R A) := by
      change value ∈ (Ideal.map (algebraMap R A)
        (RingHom.ker augmentation)).restrictScalars R ↔ _
      rw [Schubert.Splines.mapIdeal_restrictScalars_eq_smul_top]
    rw [hmembership, Schubert.Splines.mem_ideal_smul_top_iff_basis_coordinates basis]
    simp only [RingHom.mem_ker]
    constructor
    · intro hzero index
      exact Finsupp.ext_iff.mp hzero index
    · intro hzero
      exact Finsupp.ext fun index => hzero index
  have hsurjective : Function.Surjective coordinates := by
    intro coefficients
    refine ⟨basis.repr.symm (coefficients.mapRange (algebraMap ℂ R) (by simp)), ?_⟩
    ext index
    change augmentation (basis.repr
      (basis.repr.symm (coefficients.mapRange (algebraMap ℂ R) (by simp))) index) = _
    rw [basis.repr.apply_symm_apply, Finsupp.mapRange_apply, augmentation.commutes]
    rfl
  let quotientCoordinates := (ideal.restrictScalars ℂ).liftQ coordinates (by
    intro value hvalue
    exact (hkernel value).mpr hvalue)
  have hbijective : Function.Bijective quotientCoordinates := by
    constructor
    · apply (injective_iff_map_eq_zero quotientCoordinates).mpr
      intro value hzero
      obtain ⟨representative, rfl⟩ := (ideal.restrictScalars ℂ).mkQ_surjective value
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((hkernel representative).mp hzero)
    · intro coefficients
      obtain ⟨representative, hrepresentative⟩ := hsurjective coefficients
      exact ⟨Submodule.Quotient.mk representative, hrepresentative⟩
  let quotientBasis : Module.Basis I ℂ (A ⧸ ideal) :=
    ⟨LinearEquiv.ofBijective quotientCoordinates hbijective⟩
  refine ⟨quotientBasis, ?_⟩
  intro index
  apply quotientBasis.apply_eq_iff.mpr
  ext coordinate
  change augmentation (basis.repr (basis index) coordinate) =
    (Finsupp.single index (1 : ℂ)) coordinate
  rw [basis.repr_self]
  by_cases hequal : index = coordinate
  · subst coordinate
    simp
  · simp [hequal]

end Schubert.Dihedral
