import DihedralHessenberg.Paper.HessenbergTensorFree
import DihedralHessenberg.Paper.OrbitScalarRepresentation

/-! # Graded equivariant freeness over the orbit coordinate subalgebra -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral.RootSubset.Right

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Polynomial homogeneity is exactly orbit scalar homogeneity. -/
theorem scalarEquiv_mem_piece (degree : ℕ) (polynomial : CoordinatePolynomial) :
    scalarEquiv selected hthree polynomial ∈ scalarPiece selected hthree degree ↔
      polynomial.IsHomogeneous degree := by
  constructor
  · intro hmember
    have hidentity := hmember 1
    change (polynomialAction n 1 polynomial).IsHomogeneous degree at hidentity
    rw [map_one] at hidentity
    exact hidentity
  · intro hpolynomial
    exact selected.orbitHom_mem_piece hthree degree polynomial hpolynomial

/-- Orbit scalar degree maps back to the polynomial degree. -/
theorem scalarEquiv_symm_homogeneous (degree : ℕ)
    (scalar : (selected.orbitHom hthree).range)
    (hscalar : scalar ∈ scalarPiece selected hthree degree) :
    ((scalarEquiv selected hthree).symm scalar).IsHomogeneous degree := by
  apply (scalarEquiv_mem_piece selected hthree degree _).mp
  simpa only [AlgEquiv.apply_symm_apply] using hscalar

end Schubert.Dihedral.RootSubset.Right

namespace Schubert.DihedralSplines.HessenbergIdeal.Right

open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The spline action is its graded extension by the orbit-coordinate subalgebra. -/
theorem orbit_tensor_free :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod (RootSubset.Right.scalarRepresentation ideal.toRootSubset hthree)
          (RootSubset.Right.representation ideal.toRootSubset hthree))
        (ideal.toRootSubset.splineRepresentation hthree),
      (∀ degree, (Submodule.span ℂ
        {value | ∃ (scalarDegree valueDegree : ℕ)
          (scalar : (ideal.toRootSubset.orbitHom hthree).range)
          (vector : RootSubset.Right.Quotient ideal.toRootSubset hthree),
          scalarDegree + valueDegree = degree ∧
          scalar ∈ RootSubset.Right.scalarPiece ideal.toRootSubset hthree scalarDegree ∧
          vector ∈ RootSubset.Right.piece ideal.toRootSubset hthree valueDegree ∧
          value = scalar ⊗ₜ[ℂ] vector}).map equivalence.toLinearMap =
        ideal.toRootSubset.piece degree) ∧
      (∀ value : RootSubset.Right.Quotient ideal.toRootSubset hthree,
        RootSubset.Right.quotientMap ideal.toRootSubset hthree
          (equivalence (1 ⊗ₜ[ℂ] value)) = value) := by
  let selected := ideal.toRootSubset
  let source := RootSubset.Right.representation selected hthree
  let scalar := (RootSubset.Right.scalarActionEquiv selected hthree).symm
  let reindex : Representation.Equiv
      (Representation.tprod (RootSubset.Right.scalarRepresentation selected hthree) source)
      (Representation.tprod (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
        source) := Representation.Equiv.mk
    (TensorProduct.congr scalar.toLinearEquiv (LinearEquiv.refl ℂ _)) (fun element => by
      apply TensorProduct.ext'
      intro coefficient value
      change TensorProduct.congr scalar.toLinearEquiv (LinearEquiv.refl ℂ _)
        ((Representation.tprod (RootSubset.Right.scalarRepresentation selected hthree) source)
          element (coefficient ⊗ₜ[ℂ] value)) =
        (Representation.tprod (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
          source) element
          (TensorProduct.congr scalar.toLinearEquiv (LinearEquiv.refl ℂ _)
            (coefficient ⊗ₜ[ℂ] value))
      simp only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply]
      congr 1
      exact scalar.toIntertwiningMap.isIntertwining _ _ element coefficient)
  obtain ⟨original, hdegrees, hnormalized⟩ := tensor_free ideal
  refine ⟨reindex.trans original, ?_, ?_⟩
  · intro degree
    have hspan : (Submodule.span ℂ
        {value | ∃ (scalarDegree valueDegree : ℕ)
          (coefficient : (selected.orbitHom hthree).range)
          (vector : RootSubset.Right.Quotient selected hthree),
          scalarDegree + valueDegree = degree ∧
          coefficient ∈ RootSubset.Right.scalarPiece selected hthree scalarDegree ∧
          vector ∈ RootSubset.Right.piece selected hthree valueDegree ∧
          value = coefficient ⊗ₜ[ℂ] vector}).map reindex.toLinearMap =
        Schubert.FiniteGroupCharacters.tensorPiece (P := Fin 2)
          (RootSubset.Right.piece selected hthree) degree := by
      rw [Submodule.map_span]
      unfold Schubert.FiniteGroupCharacters.tensorPiece
      congr 1
      ext value
      constructor
      · rintro ⟨tensor, ⟨scalarDegree, valueDegree, coefficient, vector,
          hdegree, hcoefficient, hvector, rfl⟩, rfl⟩
        refine ⟨scalarDegree, valueDegree,
          (RootSubset.Right.scalarEquiv selected hthree).symm coefficient, vector,
          hdegree, RootSubset.Right.scalarEquiv_symm_homogeneous selected hthree
            scalarDegree coefficient hcoefficient, hvector, ?_⟩
        exact TensorProduct.congr_tmul _ _ _ _
      · rintro ⟨scalarDegree, valueDegree, polynomial, vector,
          hdegree, hpolynomial, hvector, rfl⟩
        refine ⟨RootSubset.Right.scalarEquiv selected hthree polynomial ⊗ₜ[ℂ] vector,
          ⟨scalarDegree, valueDegree, RootSubset.Right.scalarEquiv selected hthree polynomial,
            vector, hdegree, (RootSubset.Right.scalarEquiv_mem_piece selected hthree
              scalarDegree polynomial).mpr hpolynomial, hvector, rfl⟩, ?_⟩
        change TensorProduct.congr scalar.toLinearEquiv (LinearEquiv.refl ℂ _)
          (_ ⊗ₜ[ℂ] vector) = polynomial ⊗ₜ[ℂ] vector
        rw [TensorProduct.congr_tmul]
        change (RootSubset.Right.scalarEquiv selected hthree).symm
          (RootSubset.Right.scalarEquiv selected hthree polynomial) ⊗ₜ[ℂ] vector = _
        rw [AlgEquiv.symm_apply_apply]
    change Submodule.map (original.toLinearMap.comp reindex.toLinearMap) _ = _
    rw [Submodule.map_comp, hspan]
    exact hdegrees degree
  · intro value
    change RootSubset.Right.quotientMap selected hthree
      (original (TensorProduct.congr scalar.toLinearEquiv (LinearEquiv.refl ℂ _)
        (1 ⊗ₜ[ℂ] value))) = value
    rw [TensorProduct.congr_tmul]
    change RootSubset.Right.quotientMap selected hthree
      (original ((RootSubset.Right.scalarEquiv selected hthree).symm 1 ⊗ₜ[ℂ] value)) = value
    rw [map_one]
    exact hnormalized value

end Schubert.DihedralSplines.HessenbergIdeal.Right
