import Schubert.FiniteGroupCharacters.TensorAugmentation

/-! # Exact transport of polynomial augmentation kernels -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters
variable {K P Q M : Type*} [CommRing K] [AddCommGroup Q] [Module K Q]
variable [AddCommGroup M] [Module K M]

/-- A normalized scalar-extension map composes with projection as augmentation. -/
theorem tensorAugmentation_comp (equivalence : MvPolynomial P K ⊗[K] Q ≃ₗ[K] M)
    (projection : M →ₗ[K] Q)
    (hpure : ∀ polynomial value, projection (equivalence (polynomial ⊗ₜ[K] value)) =
      polynomial.constantCoeff • value) :
    projection.comp equivalence.toLinearMap = tensorAugmentation := by
  apply TensorProduct.ext'
  intro polynomial value
  exact hpure polynomial value

/-- The positive scalar tensor span maps exactly onto the projection kernel. -/
theorem positive_tensor_map {I : Type*} (basis : Module.Basis I K Q)
    (equivalence : MvPolynomial P K ⊗[K] Q ≃ₗ[K] M) (projection : M →ₗ[K] Q)
    (hpure : ∀ polynomial value, projection (equivalence (polynomial ⊗ₜ[K] value)) =
      polynomial.constantCoeff • value) :
    (positiveTensor (K := K) (P := P) (Q := Q)).map equivalence.toLinearMap =
      LinearMap.ker projection := by
  have hprojection := tensorAugmentation_comp equivalence projection hpure
  have happly : ∀ tensor, projection (equivalence tensor) = tensorAugmentation tensor :=
    fun tensor => LinearMap.congr_fun hprojection tensor
  ext value
  constructor
  · rintro ⟨tensor, htensor, rfl⟩
    change projection (equivalence tensor) = 0
    rw [happly]
    exact LinearMap.mem_ker.mp ((tensorAugmentation_ker basis).symm ▸ htensor)
  · intro hvalue
    refine ⟨equivalence.symm value, ?_, equivalence.apply_symm_apply value⟩
    rw [← tensorAugmentation_ker basis]
    change tensorAugmentation (equivalence.symm value) = 0
    rw [← happly, equivalence.apply_symm_apply]
    exact hvalue

/-- Exact homogeneous scalar extension transports the whole removed-ideal degree intersection. -/
theorem positive_tensor_degree_map {I : Type*} (basis : Module.Basis I K Q)
    (equivalence : MvPolynomial P K ⊗[K] Q ≃ₗ[K] M) (projection : M →ₗ[K] Q)
    (hpure : ∀ polynomial value, projection (equivalence (polynomial ⊗ₜ[K] value)) =
      polynomial.constantCoeff • value)
    (sourcePiece : Submodule K (MvPolynomial P K ⊗[K] Q)) (targetPiece : Submodule K M)
    (hdegree : sourcePiece.map equivalence.toLinearMap = targetPiece) :
    (positiveTensor ⊓ sourcePiece).map equivalence.toLinearMap =
      LinearMap.ker projection ⊓ targetPiece := by
  rw [Submodule.map_inf _ equivalence.injective, positive_tensor_map basis equivalence projection
    hpure, hdegree]

end Schubert.FiniteGroupCharacters
