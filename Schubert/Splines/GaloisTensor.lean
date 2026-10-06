import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-! # The canonical tensor splitting of a finite Galois extension -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Splines

variable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L]

/-- Evaluation of a balanced tensor through the Galois action. -/
def galoisTensorMap : L ⊗[K] L →ₐ[L] (G → L) :=
  AlgHom.liftEquiv K L L (G → L)
    (AlgHom.pi fun g => (MulSemiringAction.toAlgAut G K L g).toAlgHom)

omit [Finite G] in
/-- Pure tensors have their Galois-product values. -/
theorem galoisTensorMap_tmul (a b : L) (g : G) :
    galoisTensorMap G K L (a ⊗ₜ[K] b) g = a * g • b := rfl

/-- The Galois tensor evaluation is surjective. -/
theorem galoisTensorMap_surjective : Function.Surjective (galoisTensorMap G K L) := by
  classical
  let := Fintype.ofFinite G
  let f := (galoisTensorMap G K L).toLinearMap
  apply LinearMap.dualMap_injective_iff.mp
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro phi hphi
  let c : G → L := fun g => phi (Pi.basisFun L G g)
  have hsum : ∑ g, c g • (MulSemiringAction.toAlgAut G K L g).toLinearMap = 0 := by
    ext b
    have hzero := DFunLike.congr_fun hphi (1 ⊗ₜ[K] b)
    change phi (f (1 ⊗ₜ[K] b)) = 0 at hzero
    have hrepr := congrArg phi ((Pi.basisFun L G).sum_repr (f (1 ⊗ₜ[K] b)))
    simp only [map_sum, map_smul, Pi.basisFun_repr, LinearMap.sum_apply,
      LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul] at hrepr ⊢
    simpa [c, f, galoisTensorMap_tmul, mul_comm] using hrepr.trans hzero
  have hli : LinearIndependent L
      (fun g : G => (MulSemiringAction.toAlgAut G K L g).toLinearMap) := by
    exact (linearIndependent_algHom_toLinearMap K L L).comp
      (fun g => (MulSemiringAction.toAlgAut G K L g).toAlgHom)
      (by
        intro a b hab
        have : FaithfulSMul G L := IsGaloisGroup.faithful K
        apply eq_of_smul_eq_smul (α := L)
        exact fun x => DFunLike.congr_fun hab x)
  have hc : ∀ g, c g = 0 := (Fintype.linearIndependent_iff.mp hli) c hsum
  apply (Pi.basisFun L G).ext
  intro g
  exact hc g

/-- The tensor evaluation is bijective in the finite Galois extension. -/
theorem galoisTensorMap_bijective : Function.Bijective (galoisTensorMap G K L) := by
  classical
  let := Fintype.ofFinite G
  have : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  have hdim : Module.finrank L (L ⊗[K] L) = Module.finrank L (G → L) := by
    rw [Module.finrank_baseChange]
    simpa [Module.finrank_pi, Nat.card_eq_fintype_card] using
      (IsGaloisGroup.card_eq_finrank G K L).symm
  have hsurj := galoisTensorMap_surjective G K L
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- The canonical splitting algebra isomorphism of the finite Galois tensor square. -/
def galoisTensorEquiv : L ⊗[K] L ≃ₐ[L] (G → L) :=
  AlgEquiv.ofBijective (galoisTensorMap G K L) (galoisTensorMap_bijective G K L)

/-- The splitting isomorphism has the Galois evaluation on every pure tensor. -/
theorem galoisTensorEquiv_tmul (a b : L) (g : G) :
    galoisTensorEquiv G K L (a ⊗ₜ[K] b) g = a * g • b := rfl

end Schubert.Splines
