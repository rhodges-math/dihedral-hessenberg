import Mathlib.Data.Finsupp.Weight
import Schubert.Dihedral.InvariantMonomialBasis
import Schubert.FiniteGroupCharacters.EmbeddedHomogeneousBasis

/-! # Homogeneous pieces of the invariant algebra

The invariant subalgebra inherits its homogeneous subspaces by comapping the ordinary
polynomial grading. Each degree has a basis of the weighted invariant monomials of that degree.
-/

noncomputable section

namespace Schubert.Dihedral

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive generator weights have finite invariant monomial degree fibers. -/
theorem invariant_monomial_degree_fiber_finite (n degree : ℕ) (hpositive : 0 < n) :
    Finite {exponent : Fin 2 →₀ ℕ // 2 * exponent 0 + n * exponent 1 = degree} := by
  let weights (index : Fin 2) : ℕ := if index = 0 then 2 else n
  have hweights : ∀ index, weights index ≠ 0 := by
    intro index
    fin_cases index <;> simp [weights, hpositive.ne']
  have hfinite := Finsupp.finite_of_nat_weight_eq weights hweights degree
  have hequal : {exponent : Fin 2 →₀ ℕ | Finsupp.weight weights exponent = degree} =
      {exponent : Fin 2 →₀ ℕ | 2 * exponent 0 + n * exponent 1 = degree} := by
    ext exponent
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_two, weights, mul_comm]
  rw [hequal] at hfinite
  exact hfinite.to_subtype

/-- The invariant homogeneous piece has its weighted monomial basis. -/
theorem exists_invariant_homogeneousPiece_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) :
    ∃ basis : Module.Basis
        {exponent : Fin 2 →₀ ℕ // 2 * exponent 0 + n * exponent 1 = degree} ℂ
        ((MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree).comap
          (invariantSubalgebra n).val.toLinearMap),
      ∀ exponent, ((basis exponent : invariantSubalgebra n) : CoordinatePolynomial) =
        quadraticInvariant ^ exponent.val 0 * higherInvariant n ^ exponent.val 1 := by
  obtain ⟨basis, hbasis⟩ := exists_invariant_monomial_basis n hthree
  have hhomogeneous (exponent : Fin 2 →₀ ℕ) :
      (invariantSubalgebra n).val.toLinearMap (basis exponent) ∈
        MvPolynomial.homogeneousSubmodule (Fin 2) ℂ
          (2 * exponent 0 + n * exponent 1) := by
    change (basis exponent : CoordinatePolynomial).IsHomogeneous _
    rw [hbasis]
    exact invariant_monomial_isHomogeneous n exponent
  obtain ⟨restrictedBasis, hrestricted⟩ :=
    Schubert.FiniteGroupCharacters.exists_embedded_homogeneousPiece_basis
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (invariantSubalgebra n).val.toLinearMap
      Subtype.val_injective basis (fun exponent => 2 * exponent 0 + n * exponent 1)
      hhomogeneous degree
  refine ⟨restrictedBasis, fun exponent => ?_⟩
  rw [hrestricted]
  exact hbasis exponent.val

/-- The invariant degree dimension is the cardinality of its weighted monomial fiber. -/
theorem _root_.Schubert.Dihedral.Invariants.Piece.finrank_degree_fiber (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) (degree : ℕ) :
    Module.finrank ℂ ((MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree).comap
      (invariantSubalgebra n).val.toLinearMap) =
      Nat.card {exponent : Fin 2 →₀ ℕ // 2 * exponent 0 + n * exponent 1 = degree} := by
  obtain ⟨basis, _⟩ := exists_invariant_homogeneousPiece_basis n hthree degree
  exact Module.finrank_eq_nat_card_basis basis

/-- Every invariant degree piece is finite-dimensional. -/
theorem invariant_homogeneousPiece_finite (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) :
    Module.Finite ℂ ((MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree).comap
      (invariantSubalgebra n).val.toLinearMap) := by
  let := invariant_monomial_degree_fiber_finite n degree (by omega)
  obtain ⟨basis, _⟩ := exists_invariant_homogeneousPiece_basis n hthree degree
  exact Module.Finite.of_basis basis

end Schubert.Dihedral
