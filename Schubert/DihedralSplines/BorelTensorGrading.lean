import Schubert.DihedralSplines.BorelEquivalence
import Schubert.Dihedral.CoinvariantHomogeneousBasis
import Schubert.Dihedral.InvariantFreeness
import Schubert.DihedralSplines.PaperGrading
import Schubert.FiniteGroupCharacters.EmbeddedHomogeneousBasis
import Mathlib.RingTheory.AlgebraTower

/-! The ordinary total-degree span of homogeneous pure tensors over the invariants. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- The ordinary total-degree span of homogeneous pure tensors over the invariants. -/
def borelTensorPiece (n : ℕ) [NeZero n] (degree : ℕ) : Submodule ℂ
    (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :=
  Submodule.span ℂ {value | ∃ firstDegree secondDegree first second,
    first.IsHomogeneous firstDegree ∧ second.IsHomogeneous secondDegree ∧
      firstDegree + secondDegree = degree ∧
        value = first ⊗ₜ[invariantSubalgebra n] second}

/-- The Borel map restricted to complex scalar linearity. -/
def borelLinearMap (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial →ₗ[ℂ]
      (RootSubset.full n).Spline := by
  letI := (RootSubset.full n).leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial (RootSubset.full n).Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((RootSubset.full n).constantHom hthree).commutes _
  exact (borelHom n hthree).toLinearMap.restrictScalars ℂ

/-- The complex linear map retains the full spline value. -/
theorem borelLinearMap_apply (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (value : CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :
    borelLinearMap n hthree value = borelHom n hthree value := rfl

/-- Orbit evaluation takes ordinary homogeneous tensors to homogeneous splines. -/
theorem borelTensorPiece_le_comap (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ) :
    borelTensorPiece n degree ≤ ((RootSubset.full n).piece degree).comap
      (borelLinearMap n hthree) := by
  let := (RootSubset.full n).leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial (RootSubset.full n).Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((RootSubset.full n).constantHom hthree).commutes _
  apply Submodule.span_le.mpr
  rintro value ⟨firstDegree, secondDegree, first, second, hfirst, hsecond, hdegree, rfl⟩
  intro vertex
  change MvPolynomial.IsHomogeneous
    ((borelHom n hthree (first ⊗ₜ[invariantSubalgebra n] second)).val vertex) degree
  rw [borelHom_tmul, ← hdegree]
  exact hfirst.mul (polynomialAction_isHomogeneous n vertex hsecond)

private theorem exists_piece_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis ((Fin 2 →₀ ℕ) × (Fin n × Fin 2)) ℂ
        (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial),
      ∀ index, basis index ∈ borelTensorPiece n (index.1.degree +
        (if index.2.1.val = 0 then if index.2.2 = 0 then 0 else n
          else if index.2.2 = 0 then n - index.2.1.val else index.2.1.val)) := by
  obtain ⟨axialBasis, haxialBasis⟩ := exists_invariant_axial_basis n hthree
  let tensorBasis := axialBasis.baseChange CoordinatePolynomial
  let basis := (MvPolynomial.basisMonomials (Fin 2) ℂ).smulTower tensorBasis
  refine ⟨basis, fun index => ?_⟩
  dsimp only [basis, tensorBasis]
  rw [Module.Basis.smulTower_apply, Module.Basis.baseChange_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  apply Submodule.subset_span
  refine ⟨_, _, _, _, MvPolynomial.isHomogeneous_monomial _ rfl, ?_, rfl, rfl⟩
  rw [haxialBasis]
  exact axial_rotation_block_isHomogeneous n index.2.1 index.2.2

/-- The ordinary tensor degree is exactly the preimage of the spline degree. -/
theorem borelTensorPiece_eq_comap (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ) :
    borelTensorPiece n degree = ((RootSubset.full n).piece degree).comap
      (borelLinearMap n hthree) := by
  let := (RootSubset.full n).leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial (RootSubset.full n).Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((RootSubset.full n).constantHom hthree).commutes _
  let := (RootSubset.full n).gradedAlgebra hthree
  obtain ⟨basis, hbasis⟩ := exists_piece_basis n hthree
  have hhomogeneous := fun index => borelTensorPiece_le_comap n hthree _ (hbasis index)
  apply le_antisymm (borelTensorPiece_le_comap n hthree degree)
  rw [Schubert.FiniteGroupCharacters.EmbeddedBasis.piece_eq_span_degree
    (RootSubset.full n).piece (borelLinearMap n hthree)
      (borelHom_injective n hthree) basis _ hhomogeneous degree]
  apply Submodule.span_le.mpr
  rintro value ⟨index, rfl⟩
  have hmember := hbasis index.val
  rw [index.property] at hmember
  exact hmember

/-- The Borel equivalence preserves every ordinary total homogeneous degree exactly. -/
theorem borelTensorPiece_map (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ) :
    (borelTensorPiece n degree).map (borelLinearMap n hthree) =
      (RootSubset.full n).piece degree := by
  rw [borelTensorPiece_eq_comap]
  exact Submodule.map_comap_eq_of_surjective (borelHom_surjective n hthree) _

end Schubert.DihedralSplines
