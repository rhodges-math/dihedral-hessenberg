import Schubert.Dihedral.AxialDegreeCard
import Schubert.Dihedral.CoinvariantHomogeneousBasis

/-! # The dihedral coinvariant Hilbert function

The homogeneous quotient has dimensions one in degrees zero and n,
two in every degree strictly between them, and zero in all higher degrees.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The coinvariant degree dimensions are 1, then 2 in intermediate degrees, then 1. -/
theorem coinvariant_homogeneousPiece_finrank (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) =
      if degree = 0 ∨ degree = n then 1 else if degree < n then 2 else 0 := by
  rw [_root_.Schubert.Dihedral.Coinvariant.Piece.finrank_degree_fiber n hthree,
    axial_rotation_block_degree_fiber_card n degree (by omega)]

/-- The degree-zero coinvariant piece is one-dimensional. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.finrank_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
  :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) 0) = 1 := by
  simp [coinvariant_homogeneousPiece_finrank n hthree]

/-- The top coinvariant piece is one-dimensional. -/
theorem coinvariant_homogeneousPiece_finrank_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) n) = 1 := by
  simp [coinvariant_homogeneousPiece_finrank n hthree]

/-- Every intermediate coinvariant piece is two-dimensional. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.finrank_middle (n : ℕ) [NeZero n] (hthree : 3 ≤
  n)
    (degree : ℕ) (hpositive : 0 < degree) (hbelow : degree < n) :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) = 2 := by
  simp [coinvariant_homogeneousPiece_finrank n hthree, hpositive.ne', hbelow.ne, hbelow]

/-- All coinvariant pieces above the top degree have dimension zero. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.finrank_above (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (habove : n < degree) :
    Module.finrank ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) = 0 := by
  have hpositive : 0 < degree := by omega
  simp [coinvariant_homogeneousPiece_finrank n hthree, hpositive.ne', habove.ne', habove.not_gt]

/-- The coinvariant homogeneous submodules vanish above degree n. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.eq_bot_above (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (habove : n < degree) :
    TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
      (coinvariantIdeal n) degree = ⊥ := by
  have := coinvariant_homogeneousPiece_finite n degree
  exact Submodule.finrank_eq_zero.mp
    (_root_.Schubert.Dihedral.Coinvariant.Piece.finrank_above n hthree degree habove)

/-- A homogeneous polynomial of degree above n belongs to the coinvariant ideal. -/
theorem homogeneous_mem_coinvariantIdeal_of_n_lt (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (habove : n < degree) (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial.IsHomogeneous degree) : polynomial ∈ coinvariantIdeal n := by
  have hpiece := TauCeti.GradedAlgebra.mk_mem_quotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) hpolynomial
  rw [_root_.Schubert.Dihedral.Coinvariant.Piece.eq_bot_above n hthree degree habove] at hpiece
  exact Ideal.Quotient.eq_zero_iff_mem.mp hpiece

end Schubert.Dihedral
