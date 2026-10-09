import DihedralHessenberg.FiniteGroupCharacters.TensorPieceBasis

/-! # Augmentation kernels of ordinary polynomial scalar tensors -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters
variable {K P Q : Type*} [CommRing K] [AddCommGroup Q] [Module K Q]

/-- Evaluation of the polynomial scalar at zero on the ordinary tensor carrier. -/
def tensorAugmentation : MvPolynomial P K ⊗[K] Q →ₗ[K] Q :=
  TensorProduct.lift
    { toFun := fun polynomial => polynomial.constantCoeff • LinearMap.id
      map_add' := fun first second => by simp [map_add, add_smul]
      map_smul' := fun scalar polynomial => by simp [smul_smul] }

/-- Augmentation evaluates the constant polynomial coefficient on each pure tensor. -/
theorem tensorAugmentation_tmul (polynomial : MvPolynomial P K) (value : Q) :
    tensorAugmentation (polynomial ⊗ₜ[K] value) = polynomial.constantCoeff • value := rfl

/-- The ordinary positive scalar-degree tensor span. -/
def positiveTensor : Submodule K (MvPolynomial P K ⊗[K] Q) :=
  Submodule.span K {value | ∃ (exponent : P →₀ ℕ) (vector : Q), exponent ≠ 0 ∧
    value = MvPolynomial.monomial exponent 1 ⊗ₜ[K] vector}

/-- Augmentation coordinates are the zero-exponent coordinates of the tensor basis. -/
theorem tensorAugmentation_coordinate {I : Type*} (basis : Module.Basis I K Q)
    (value : MvPolynomial P K ⊗[K] Q) (index : I) :
    basis.repr (tensorAugmentation value) index =
      ((MvPolynomial.basisMonomials P K).tensorProduct basis).repr value (0, index) := by
  have hlinear : (basis.coord index).comp tensorAugmentation =
      (((MvPolynomial.basisMonomials P K).tensorProduct basis).coord (0, index)) := by
    apply TensorProduct.ext'
    intro polynomial vector
    change basis.repr (tensorAugmentation (polynomial ⊗ₜ[K] vector)) index = _
    rw [tensorAugmentation_tmul, map_smul]
    change (polynomial.constantCoeff • basis.repr vector) index =
      ((MvPolynomial.basisMonomials P K).tensorProduct basis).repr
        (polynomial ⊗ₜ[K] vector) (0, index)
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    change polynomial.constantCoeff * basis.repr vector index =
      basis.repr vector index * polynomial.coeff 0
    rw [MvPolynomial.constantCoeff_eq, mul_comm]
  exact congrArg (fun map => map value) hlinear

/-- The augmentation kernel is exactly the positive polynomial scalar-degree tensor span. -/
theorem tensorAugmentation_ker {I : Type*} (basis : Module.Basis I K Q) :
    LinearMap.ker (tensorAugmentation (P := P) (Q := Q)) =
      positiveTensor (K := K) (P := P) (Q := Q) := by
  classical
  let tower := (MvPolynomial.basisMonomials P K).tensorProduct basis
  apply le_antisymm
  · intro value hvalue
    have hzero : ∀ index, tower.repr value (0, index) = 0 := by
      intro index
      rw [← tensorAugmentation_coordinate basis value index]
      rw [LinearMap.mem_ker.mp hvalue, map_zero, Finsupp.zero_apply]
    rw [← tower.linearCombination_repr value, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro pair _
    by_cases hexponent : pair.1 = 0
    · have hpair : pair = (0, pair.2) := Prod.ext hexponent rfl
      rw [hpair, hzero, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨pair.1, basis pair.2, hexponent, ?_⟩
      exact Module.Basis.tensorProduct_apply' _ _ pair
  · apply Submodule.span_le.mpr
    rintro value ⟨exponent, vector, hne, rfl⟩
    change tensorAugmentation (MvPolynomial.monomial exponent 1 ⊗ₜ[K] vector) = 0
    rw [tensorAugmentation_tmul]
    simp [MvPolynomial.constantCoeff_monomial, hne]


/-- Constant-coefficient preservation intertwines augmentation with the tensor action. -/
theorem tensorAugmentation_equivariant {G : Type*} [Monoid G]
    (scalar : Representation K G (MvPolynomial P K)) (source : Representation K G Q)
    (hscalar : ∀ element polynomial, (scalar element polynomial).constantCoeff =
      polynomial.constantCoeff) (element : G) :
    tensorAugmentation.comp ((scalar.tprod source) element) =
      (source element).comp tensorAugmentation := by
  apply TensorProduct.ext'
  intro polynomial value
  change tensorAugmentation ((scalar.tprod source) element (polynomial ⊗ₜ[K] value)) =
    source element (tensorAugmentation (polynomial ⊗ₜ[K] value))
  rw [Representation.tprod_apply, TensorProduct.map_tmul, tensorAugmentation_tmul,
    tensorAugmentation_tmul, hscalar, map_smul]

end Schubert.FiniteGroupCharacters
