import Schubert.DihedralSplines.LowDegreeSplineRestriction
import Schubert.DihedralSplines.QuotientRestriction
import Schubert.Splines.IdealBasisLift
import Schubert.Splines.PolynomialBasisCoordinates
import Schubert.Splines.PolynomialAugmentation
import Schubert.DihedralSplines.PaperCoordinates

/-! # Low-degree preimages of the geometric right coordinate ideal -/

noncomputable section
namespace Schubert.Dihedral.RootSubset.Right
variable {n : ℕ} (selected larger : RootSubset n) (hthree : 3 ≤ n)
variable (hsubset : (selected : Set RealPlane) ⊆ larger)

/-- Restriction is linear and multiplicative for orbit polynomial scalars. -/
def splineRestrict :
    letI := larger.rightAlgebra hthree
    letI := selected.rightAlgebra hthree
    larger.Spline →ₐ[CoordinatePolynomial] selected.Spline := by
  letI := larger.rightAlgebra hthree
  letI := selected.rightAlgebra hthree
  exact { toRingHom := (selected.restrict larger hsubset).toRingHom
          commutes' := fun polynomial => selected.restrict_orbit larger hthree hsubset polynomial }
end Schubert.Dihedral.RootSubset.Right

namespace Schubert.Dihedral.RootSubset.Left
variable {n : ℕ} (selected larger : RootSubset n) (hthree : 3 ≤ n)
variable (hsubset : (selected : Set RealPlane) ⊆ larger)

/-- Restriction is linear and multiplicative for constant polynomial scalars. -/
def splineRestrict :
    letI := larger.leftAlgebra hthree
    letI := selected.leftAlgebra hthree
    larger.Spline →ₐ[CoordinatePolynomial] selected.Spline := by
  letI := larger.leftAlgebra hthree
  letI := selected.leftAlgebra hthree
  exact { toRingHom := (selected.restrict larger hsubset).toRingHom
          commutes' := fun polynomial =>
            selected.restrict_constant larger hthree hsubset polynomial }
end Schubert.Dihedral.RootSubset.Left

namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A low-degree right coordinate-ideal element has a full-spline ideal preimage. -/
theorem rightIdeal_preimage (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree ≤ half) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece degree)
    (hideal : value ∈ RootSubset.Right.ideal ideal.toRootSubset hthree) :
    ∃ original ∈ RootSubset.Right.ideal (RootSubset.full n) hthree,
      ideal.toRootSubset.restrictFull original = value := by
  classical
  let := ideal.toRootSubset.rightAlgebra hthree
  let := (RootSubset.full n).rightAlgebra hthree
  let := ideal.toRootSubset.gradedAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial ideal.toRootSubset.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ =>
      ((ideal.toRootSubset.orbitHom hthree).commutes _).symm
  let basis := FlowupSpline.Right.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈
      ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Right.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hcoords : ∀ vertex, basis.repr value vertex ∈ MvPolynomial.idealOfVars (Fin 2) ℂ := by
    apply (mem_ideal_smul_top_iff_basis_coordinates basis
      (MvPolynomial.idealOfVars (Fin 2) ℂ) value).mp
    have hmem : value ∈ (RootSubset.Right.ideal ideal.toRootSubset hthree).restrictScalars
        CoordinatePolynomial := hideal
    rw [RootSubset.Right.ideal_smul_top] at hmem
    exact hmem
  apply ideal_basis_preimage (MvPolynomial.idealOfVars (Fin 2) ℂ)
    (RootSubset.Right.splineRestrict ideal.toRootSubset (RootSubset.full n) hthree
      ideal.toRootSubset.positive) basis value hcoords
  intro vertex hnonzero
  have hweight : ideal.toRootSubset.length vertex < degree := by
    by_contra hnot
    have hconstant := polynomial_basis_repr_constant ideal.toRootSubset.piece basis
      ideal.toRootSubset.length hbasis
      (fun sd vd p v hp hv => RootSubset.Right.smul_mem_piece ideal.toRootSubset hthree
        sd vd p hp v hv) degree hhomogeneous vertex (by omega)
    have hzero := (PolynomialAugmentation.mem_iff_constantCoeff_zero
      (basis.repr value vertex)).mp (hcoords vertex)
    rw [hconstant, hzero, MvPolynomial.C_0] at hnonzero
    exact hnonzero rfl
  obtain ⟨original, horiginal⟩ := ideal.fullPieceMap_surjective half hhalf
    (ideal.toRootSubset.length vertex) (by omega) ⟨basis vertex, hbasis vertex⟩
  refine ⟨original.val, ?_⟩
  exact congrArg Subtype.val horiginal
/-- A low-degree left coordinate-ideal element has a full-spline ideal preimage. -/
theorem leftIdeal_preimage (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree ≤ half) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece degree)
    (hideal : value ∈ RootSubset.Left.ideal ideal.toRootSubset hthree) :
    ∃ original ∈ RootSubset.Left.ideal (RootSubset.full n) hthree,
      ideal.toRootSubset.restrictFull original = value := by
  classical
  let := ideal.toRootSubset.leftAlgebra hthree
  let := (RootSubset.full n).leftAlgebra hthree
  let := ideal.toRootSubset.gradedAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial ideal.toRootSubset.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ =>
      ((ideal.toRootSubset.constantHom hthree).commutes _).symm
  let basis := FlowupSpline.Left.basis ideal
  have hbasis : ∀ vertex, basis vertex ∈
      ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) := by
    intro vertex
    rw [FlowupSpline.Left.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hcoords : ∀ vertex, basis.repr value vertex ∈ MvPolynomial.idealOfVars (Fin 2) ℂ := by
    apply (mem_ideal_smul_top_iff_basis_coordinates basis
      (MvPolynomial.idealOfVars (Fin 2) ℂ) value).mp
    have hmem : value ∈ (RootSubset.Left.ideal ideal.toRootSubset hthree).restrictScalars
        CoordinatePolynomial := hideal
    rw [RootSubset.Left.ideal_smul_top] at hmem
    exact hmem
  apply ideal_basis_preimage (MvPolynomial.idealOfVars (Fin 2) ℂ)
    (RootSubset.Left.splineRestrict ideal.toRootSubset (RootSubset.full n) hthree
      ideal.toRootSubset.positive) basis value hcoords
  intro vertex hnonzero
  have hweight : ideal.toRootSubset.length vertex < degree := by
    by_contra hnot
    have hconstant := polynomial_basis_repr_constant ideal.toRootSubset.piece basis
      ideal.toRootSubset.length hbasis
      (fun sd vd p v hp hv => RootSubset.Left.smul_mem_piece ideal.toRootSubset hthree
        sd vd p hp v hv) degree hhomogeneous vertex (by omega)
    have hzero := (PolynomialAugmentation.mem_iff_constantCoeff_zero
      (basis.repr value vertex)).mp (hcoords vertex)
    rw [hconstant, hzero, MvPolynomial.C_0] at hnonzero
    exact hnonzero rfl
  obtain ⟨original, horiginal⟩ := ideal.fullPieceMap_surjective half hhalf
    (ideal.toRootSubset.length vertex) (by omega) ⟨basis vertex, hbasis vertex⟩
  refine ⟨original.val, ?_⟩
  exact congrArg Subtype.val horiginal

end Schubert.DihedralSplines.HessenbergIdeal
