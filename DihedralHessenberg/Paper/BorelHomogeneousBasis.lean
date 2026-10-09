import DihedralHessenberg.Paper.BorelSplineMap
import DihedralHessenberg.Dihedral.CoinvariantHomogeneousBasis
import DihedralHessenberg.Dihedral.InvariantFreeness
import DihedralHessenberg.Paper.PaperGrading
import Mathlib.RingTheory.AlgebraTower

/-! The tensor monomial tower evaluates in the exact sum of its two degrees. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- The tensor monomial tower evaluates in the exact sum of its two degrees. -/
theorem exists_borel_homogeneous_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis ((Fin 2 →₀ ℕ) × (Fin n × Fin 2)) ℂ
        (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial),
      ∀ index, borelHom n hthree (basis index) ∈ (RootSubset.full n).piece
        (index.1.degree +
          (if index.2.1.val = 0 then if index.2.2 = 0 then 0 else n
            else if index.2.2 = 0 then n - index.2.1.val else index.2.1.val)) := by
  obtain ⟨axialBasis, haxialBasis⟩ := exists_invariant_axial_basis n hthree
  let tensorBasis := axialBasis.baseChange CoordinatePolynomial
  let basis := (MvPolynomial.basisMonomials (Fin 2) ℂ).smulTower tensorBasis
  refine ⟨basis, fun index vertex => ?_⟩
  have hevaluation : (borelHom n hthree (basis index)).val vertex =
      (MvPolynomial.basisMonomials (Fin 2) ℂ index.1) *
        polynomialAction n vertex (axialBasis index.2) := by
    dsimp only [basis, tensorBasis]
    rw [Module.Basis.smulTower_apply, Module.Basis.baseChange_apply]
    change tensorEvaluation n (_ • (1 ⊗ₜ[invariantSubalgebra n] _)) vertex = _
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, tensorEvaluation_tmul, one_mul]
  change ((borelHom n hthree (basis index)).val vertex).IsHomogeneous _
  rw [hevaluation, haxialBasis]
  exact (MvPolynomial.isHomogeneous_monomial _ rfl).mul
    (polynomialAction_isHomogeneous n vertex
      (axial_rotation_block_isHomogeneous n index.2.1 index.2.2))

end Schubert.DihedralSplines
