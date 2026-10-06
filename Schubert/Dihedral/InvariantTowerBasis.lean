import Mathlib.RingTheory.AlgebraTower
import Schubert.Dihedral.InvariantFreeness
import Schubert.Dihedral.InvariantMonomialBasis
import Schubert.Dihedral.CoinvariantHomogeneousBasis
import Schubert.Splines.ArbitraryHomogeneousBasis
import TauCeti.RingTheory.MvPolynomial.Finrank

/-! # A homogeneous invariant tower basis of the polynomial algebra

The invariant monomial basis and the finite axial basis combine by the standard scalar
tower construction. Their degrees add in the polynomial grading.
-/

noncomputable section

namespace Schubert.Dihedral

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Invariant monomials times the axial invariant-module basis form a complex polynomial basis. -/
theorem exists_invariant_tower_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis ((Fin 2 →₀ ℕ) × (Fin n × Fin 2)) ℂ CoordinatePolynomial,
      ∀ index, basis index =
        (quadraticInvariant ^ index.1 0 * higherInvariant n ^ index.1 1) *
          ((if index.2.1.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
            else ![auxiliaryU ^ (n - index.2.1.val), auxiliaryV ^ index.2.1.val]) index.2.2) := by
  obtain ⟨invariantBasis, hinvariantBasis⟩ := exists_invariant_monomial_basis n hthree
  obtain ⟨axialBasis, haxialBasis⟩ := exists_invariant_axial_basis n hthree
  refine ⟨invariantBasis.smulTower axialBasis, fun index => ?_⟩
  rw [Module.Basis.smulTower_apply]
  change (invariantBasis index.1 : CoordinatePolynomial) * axialBasis index.2 = _
  rw [hinvariantBasis, haxialBasis]

/-- The invariant tower basis is homogeneous in the polynomial grading. -/
theorem exists_homogeneous_invariant_tower_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis ((Fin 2 →₀ ℕ) × (Fin n × Fin 2)) ℂ CoordinatePolynomial,
      ∀ index, basis index ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℂ
        (2 * index.1 0 + n * index.1 1 +
          (if index.2.1.val = 0 then if index.2.2 = 0 then 0 else n
            else if index.2.2 = 0 then n - index.2.1.val else index.2.1.val)) := by
  obtain ⟨basis, hbasis⟩ := exists_invariant_tower_basis n hthree
  refine ⟨basis, fun index => ?_⟩
  change (basis index).IsHomogeneous _
  rw [hbasis]
  exact (invariant_monomial_isHomogeneous n index.1).mul
    (axial_rotation_block_isHomogeneous n index.2.1 index.2.2)

/-- The polynomial degree dimension counts weighted invariant monomials times axial classes. -/
theorem invariant_tower_degree_fiber_card (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) :
    Nat.card {index : (Fin 2 →₀ ℕ) × (Fin n × Fin 2) //
      2 * index.1 0 + n * index.1 1 +
        (if index.2.1.val = 0 then if index.2.2 = 0 then 0 else n
          else if index.2.2 = 0 then n - index.2.1.val else index.2.1.val) = degree} =
      degree + 1 := by
  obtain ⟨basis, hbasis⟩ := exists_homogeneous_invariant_tower_basis n hthree
  rw [← Schubert.Splines.arbitraryHomogeneousPieceBasis_finrank
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) basis _ hbasis degree]
  exact TauCeti.finrank_homogeneousSubmodule_fin_two ℂ degree

end Schubert.Dihedral
