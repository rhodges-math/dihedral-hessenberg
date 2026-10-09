import DihedralHessenberg.Paper.BorelHomogeneousBasis
import DihedralHessenberg.Paper.SchubertBasis
import DihedralHessenberg.Paper.LowDegreeSplineRestriction
import DihedralHessenberg.Paper.PaperCoordinates
import DihedralHessenberg.Splines.MatchedBasisSurjective
import DihedralHessenberg.Dihedral.AxialLength

/-! The Borel tensor map is onto the full geometric spline algebra. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

private theorem borel_surjective_of_weights (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (vertices : (Fin n × Fin 2) ≃ DihedralGroup n)
    (hweights : ∀ index, length n hthree (vertices index) =
      (if index.1.val = 0 then if index.2 = 0 then 0 else n
        else if index.2 = 0 then n - index.1.val else index.1.val)) :
    Function.Surjective (borelHom n hthree) := by
  classical
  let := (RootSubset.full n).leftAlgebra hthree
  let := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial (RootSubset.full n).Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((RootSubset.full n).constantHom hthree).commutes _
  let := (RootSubset.full n).gradedAlgebra hthree
  obtain ⟨sourceBasis, hsource⟩ := exists_borel_homogeneous_basis n hthree
  obtain ⟨schubertBasis, _, hschubert⟩ := SchubertSpline.homogeneous_basis n hthree
  let originalBasis : Module.Basis (DihedralGroup n) CoordinatePolynomial
      (RootSubset.full n).Spline := schubertBasis
  let targetBasis := (MvPolynomial.basisMonomials (Fin 2) ℂ).smulTower originalBasis
  have htarget : ∀ index, targetBasis index ∈ (RootSubset.full n).piece
      (index.1.degree + length n hthree index.2) := by
    intro index
    dsimp only [targetBasis]
    rw [Module.Basis.smulTower_apply]
    exact RootSubset.Left.smul_mem_piece (RootSubset.full n) hthree _ _ _
      (MvPolynomial.isHomogeneous_monomial _ rfl) _ (hschubert index.2).1
  apply Schubert.Splines.surjective_of_matched_bases (RootSubset.full n).piece
    ((RootSubset.full n).piece_isInternal hthree)
    (fun degree => (HessenbergIdeal.full n hthree).splinePiece_finite degree)
    ((borelHom n hthree).toLinearMap.restrictScalars ℂ)
    (borelHom_injective n hthree) sourceBasis targetBasis _ _ hsource htarget
    (Equiv.prodCongr (Equiv.refl (Fin 2 →₀ ℕ)) vertices)
  intro index
  change index.1.degree + length n hthree (vertices index.2) = _
  rw [hweights]

/-- The Borel tensor map is onto the full geometric spline algebra. -/
theorem borelHom_surjective (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.Surjective (borelHom n hthree) := by
  obtain ⟨vertices, hweights⟩ := exists_axial_length_equiv n hthree
  exact borel_surjective_of_weights n hthree vertices hweights

/-- The full spline algebra is the tensor product over the invariant algebra. -/
def borelEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    letI := (RootSubset.full n).leftAlgebra hthree
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial ≃ₐ[CoordinatePolynomial]
      (RootSubset.full n).Spline := by
  letI := (RootSubset.full n).leftAlgebra hthree
  exact AlgEquiv.ofBijective (borelHom n hthree)
    ⟨borelHom_injective n hthree, borelHom_surjective n hthree⟩

/-- The algebra equivalence retains the exact orbit evaluation of pure tensors. -/
theorem borelEquiv_tmul (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (first second : CoordinatePolynomial) (element : DihedralGroup n) :
    (borelEquiv n hthree (first ⊗ₜ[invariantSubalgebra n] second)).val element =
      first * polynomialAction n element second := rfl

end Schubert.DihedralSplines
