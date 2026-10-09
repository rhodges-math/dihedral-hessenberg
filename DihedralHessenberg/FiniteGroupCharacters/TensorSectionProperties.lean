import DihedralHessenberg.FiniteGroupCharacters.TensorSection

/-! # Pure-tensor formulas for equivariant scalar extension -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- An equivariant basis lift has a pure-tensor formula. -/
theorem tensor_equiv_apply {K R Q M G I : Type*} [CommRing K] [CommRing R] [Algebra K R]
    [AddCommGroup Q] [AddCommGroup M] [Module K Q] [Module K M] [Module R M]
    [IsScalarTower K R M] [Monoid G]
    (scalarAction : Representation K G R) (source : Representation K G Q)
    (target : Representation K G M) (lift : source.IntertwiningMap target)
    (hscalar : ∀ element scalar value,
      target element (scalar • value) = scalarAction element scalar • target element value)
    (basis : Module.Basis I K Q) (lifted : Module.Basis I R M)
    (hlift : ∀ index, lift (basis index) = lifted index) :
    ∃ equivalence : Representation.Equiv (Representation.tprod scalarAction source) target,
      ∀ scalar value, equivalence (scalar ⊗ₜ[K] value) = scalar • lift value := by
  obtain ⟨equivalence, hequivalence⟩ := tensorLift_equiv basis lifted lift.toLinearMap hlift
  let intertwiner := tensorLiftIntertwiner scalarAction source target lift hscalar
  have hlinear : (equivalence.restrictScalars K).toLinearMap = intertwiner.toLinearMap :=
    congrArg (fun linearMap => linearMap.restrictScalars K) hequivalence
  let equivariant : Representation.Equiv (Representation.tprod scalarAction source) target :=
    Representation.Equiv.mk (equivalence.restrictScalars K) (fun element => by
      rw [hlinear]
      exact intertwiner.isIntertwining' element)
  refine ⟨equivariant, ?_⟩
  intro scalar value
  change equivalence (scalar ⊗ₜ[K] value) = _
  exact congrArg (fun linearMap => linearMap (scalar ⊗ₜ[K] value)) hequivalence

end Schubert.FiniteGroupCharacters
