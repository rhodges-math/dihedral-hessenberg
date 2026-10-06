import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Distinct algebra maps separate the columns of a square basis evaluation matrix. -/

noncomputable section
namespace Schubert.Splines
variable {R A I : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Fintype I]

/-- Distinct algebra maps separate the columns of a square basis evaluation matrix. -/
theorem orbit_basis_independent (basis : Module.Basis I R A)
    (maps : I → A →ₐ[R] A) (hinj : Function.Injective maps) :
    LinearIndependent A (fun index => fun element => maps element (basis index)) := by
  have hmaps := (linearIndependent_algHom_toLinearMap R A A).comp maps hinj
  have hrows : LinearIndependent A (fun element => fun index => maps element (basis index)) := by
    exact hmaps.map' (basis.constr A).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (basis.constr A).symm.injective)
  exact (Matrix.linearIndependent_col_iff_row
    (A := fun element index => maps element (basis index))).mpr hrows

/-- Base extension of faithful square orbit evaluation is injective. -/
theorem orbit_tensor_injective (basis : Module.Basis I R A)
    (maps : I → A →ₐ[R] A) (hinj : Function.Injective maps) :
    Function.Injective
      ((LinearMap.pi fun element => (maps element).toLinearMap).liftBaseChange A) := by
  apply (LinearMap.liftBaseChange_injective_iff _ basis).mpr
  exact orbit_basis_independent basis maps hinj

end Schubert.Splines
