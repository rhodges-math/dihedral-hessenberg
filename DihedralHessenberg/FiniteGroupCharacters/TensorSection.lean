import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Intertwining

/-! # Polynomial scalar extensions of equivariant linear sections -/

noncomputable section

open scoped TensorProduct

namespace Schubert.FiniteGroupCharacters

variable {K R Q M : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable [AddCommGroup Q] [AddCommGroup M] [Module K Q] [Module K M] [Module R M]
variable [IsScalarTower K R M]

/-- A linear lift extends by scalar multiplication to the standard base-change tensor. -/
def tensorLift (lift : Q →ₗ[K] M) : R ⊗[K] Q →ₗ[R] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun scalar => scalar • lift
      map_add' := fun first second => add_smul first second lift
      map_smul' := fun first second => (smul_smul first second lift).symm }

/-- Scalar extension sends a pure tensor to its scalar times the lift. -/
theorem tensorLift_tmul (lift : Q →ₗ[K] M) (scalar : R) (value : Q) :
    tensorLift lift (scalar ⊗ₜ[K] value) = scalar • lift value := rfl

/-- A lifted basis gives a scalar-extension linear equivalence. -/
theorem tensorLift_equiv {I : Type*} (basis : Module.Basis I K Q)
    (lifted : Module.Basis I R M) (lift : Q →ₗ[K] M)
    (hlift : ∀ index, lift (basis index) = lifted index) :
    ∃ equivalence : R ⊗[K] Q ≃ₗ[R] M, equivalence.toLinearMap = tensorLift lift := by
  let equivalence := (basis.baseChange R).equiv lifted (Equiv.refl I)
  refine ⟨equivalence, ?_⟩
  apply (basis.baseChange R).ext
  intro index
  change ((basis.baseChange R).equiv lifted (Equiv.refl I))
    ((basis.baseChange R) index) = tensorLift lift ((basis.baseChange R) index)
  rw [Module.Basis.equiv_apply, Module.Basis.baseChange_apply, tensorLift_tmul,
    one_smul, hlift]
  rfl

/-- Scalar-compatible actions make the tensor lift an intertwiner for diagonal action. -/
def tensorLiftIntertwiner {G : Type*} [Monoid G]
    (scalarAction : Representation K G R) (source : Representation K G Q)
    (target : Representation K G M) (lift : source.IntertwiningMap target)
    (hscalar : ∀ element scalar value,
      target element (scalar • value) = scalarAction element scalar • target element value) :
    (Representation.tprod scalarAction source).IntertwiningMap target where
  toLinearMap := (tensorLift lift.toLinearMap).restrictScalars K
  isIntertwining' element := by
    apply TensorProduct.ext'
    intro scalar value
    change tensorLift lift.toLinearMap
      ((Representation.tprod scalarAction source) element (scalar ⊗ₜ[K] value)) =
        target element (tensorLift lift.toLinearMap (scalar ⊗ₜ[K] value))
    rw [Representation.tprod_apply, TensorProduct.map_tmul, tensorLift_tmul, tensorLift_tmul]
    change scalarAction element scalar • lift (source element value) =
      target element (scalar • lift value)
    rw [lift.isIntertwining source target]
    exact (hscalar element scalar (lift value)).symm

/-- An equivariant lifted basis gives an isomorphism with diagonal scalar extension. -/
theorem tensorRepresentation_equiv {G I : Type*} [Monoid G]
    (scalarAction : Representation K G R) (source : Representation K G Q)
    (target : Representation K G M) (lift : source.IntertwiningMap target)
    (hscalar : ∀ element scalar value,
      target element (scalar • value) = scalarAction element scalar • target element value)
    (basis : Module.Basis I K Q) (lifted : Module.Basis I R M)
    (hlift : ∀ index, lift (basis index) = lifted index) :
    Nonempty (Representation.Equiv (Representation.tprod scalarAction source) target) := by
  obtain ⟨equivalence, hequivalence⟩ := tensorLift_equiv basis lifted lift.toLinearMap hlift
  let intertwiner := tensorLiftIntertwiner scalarAction source target lift hscalar
  have hlinear : (equivalence.restrictScalars K).toLinearMap = intertwiner.toLinearMap :=
    congrArg (fun linearMap => linearMap.restrictScalars K) hequivalence
  refine ⟨Representation.Equiv.mk (equivalence.restrictScalars K) ?_⟩
  intro element
  rw [hlinear]
  exact intertwiner.isIntertwining' element

end Schubert.FiniteGroupCharacters
