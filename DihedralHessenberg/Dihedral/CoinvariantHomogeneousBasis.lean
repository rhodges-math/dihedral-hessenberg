import DihedralHessenberg.Dihedral.CoinvariantFinite
import DihedralHessenberg.Splines.HomogeneousBasis
import DihedralHessenberg.Dihedral.CoinvariantBasis
import DihedralHessenberg.Dihedral.CoinvariantHomogeneous

/-! # Homogeneous axial bases of the coinvariant algebra

The axial quotient vectors have their polynomial degrees. Restricting
this finite homogeneous basis identifies each degree dimension with its degree fiber.
-/

noncomputable section

namespace Schubert.Dihedral

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Each axial rotation-block polynomial has its indicated homogeneous degree. -/
theorem axial_rotation_block_isHomogeneous (n : ℕ) (index : Fin n) (coordinate : Fin 2) :
    ((if index.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
      else ![auxiliaryU ^ (n - index.val), auxiliaryV ^ index.val]) coordinate).IsHomogeneous
        (if index.val = 0 then if coordinate = 0 then 0 else n
          else if coordinate = 0 then n - index.val else index.val) := by
  by_cases hzero : index.val = 0
  · simp only [hzero, ite_true]
    fin_cases coordinate
    · exact MvPolynomial.isHomogeneous_one _ _
    · simpa using auxiliaryU_isHomogeneous.pow n
  · simp only [hzero, ite_false]
    fin_cases coordinate
    · simpa using auxiliaryU_isHomogeneous.pow (n - index.val)
    · simpa using auxiliaryV_isHomogeneous.pow index.val

/-- The coinvariant algebra has an axial basis homogeneous in the descended polynomial grading. -/
theorem _root_.Schubert.Dihedral.Coinvariant.exists_homogeneous_axial_basis (n : ℕ) [NeZero n]
  (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis (Fin n × Fin 2) ℂ (CoinvariantAlgebra n),
      ∀ index, basis index ∈ TauCeti.GradedAlgebra.quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
        (if index.1.val = 0 then if index.2 = 0 then 0 else n
          else if index.2 = 0 then n - index.1.val else index.1.val) := by
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  refine ⟨basis, fun index => ?_⟩
  rw [hbasis]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
    (axial_rotation_block_isHomogeneous n index.1 index.2)

/-- Every coinvariant degree piece is finite-dimensional. -/
theorem coinvariant_homogeneousPiece_finite (n : ℕ) [NeZero n] (degree : ℕ) :
    Module.Finite ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) := by
  have := coinvariantAlgebra_finite n
  exact Module.Finite.of_injective (Submodule.subtype _) (Submodule.subtype_injective _)

/-- Coinvariant degree dimensions count the degrees of the explicit axial basis. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.finrank_degree_fiber (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) (degree : ℕ) :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) =
      Nat.card {index : Fin n × Fin 2 //
        (if index.1.val = 0 then if index.2 = 0 then 0 else n
          else if index.2 = 0 then n - index.1.val else index.1.val) = degree} := by
  let := TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
    (coinvariantIdeal_isHomogeneous n hthree)
  obtain ⟨basis, hbasis⟩ := _root_.Schubert.Dihedral.Coinvariant.exists_homogeneous_axial_basis n
    hthree
  exact Schubert.Splines.homogeneousPieceBasis_finrank _ basis _ hbasis degree

end Schubert.Dihedral
