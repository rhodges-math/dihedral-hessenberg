import DihedralHessenberg.Paper.FamilyProjection
import DihedralHessenberg.Paper.PaperQuotientFinite
import DihedralHessenberg.Splines.DimensionPolynomial
import DihedralHessenberg.Paper.HessenbergVectorPolynomial

/-! # Geometric triangular quotient degree counts and rank polynomials -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

namespace Left

/-- The full rank polynomial of the finite geometric quotient. -/
def rankPolynomial (ideal : HessenbergIdeal n hthree) : Polynomial ℕ := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  exact Schubert.Splines.Graded.dimensionPolynomial
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.piece_isInternal ideal.toRootSubset hthree)

/-- Every coefficient equals the quotient-piece dimension, in every degree. -/
theorem rankPolynomial_coeff (ideal : HessenbergIdeal n hthree) (degree : ℕ) :
    (rankPolynomial ideal).coeff degree =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := rfl

end Left

namespace Right

/-- The full rank polynomial of the finite geometric quotient. -/
def rankPolynomial (ideal : HessenbergIdeal n hthree) : Polynomial ℕ := by
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  exact Schubert.Splines.Graded.dimensionPolynomial
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.piece_isInternal ideal.toRootSubset hthree)

/-- Every coefficient equals the quotient-piece dimension, in every degree. -/
theorem rankPolynomial_coeff (ideal : HessenbergIdeal n hthree) (degree : ℕ) :
    (rankPolynomial ideal).coeff degree =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := rfl

end Right

end Schubert.DihedralSplines.HessenbergIdeal

namespace Schubert.DihedralSplines.TriangularFamily

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

namespace Left

/-- A qualifying family gives the quotient degree multiplicities. -/
theorem piece_finrank (family : TriangularFamily ideal) (degree : ℕ) :
    Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) =
      Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} := by
  classical
  have hbackend := _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_of_triangular
    ideal.indexed
    family.backend family.backend_support family.backend_diagonal family.backend_bound degree
  change Module.finrank ℂ
      ((dihedralGradedReflectionData n hthree).leftQuotientPiece
        (ideal.indexed.roots : Set (PositiveRootIndex n)) degree) = _ at hbackend
  rw [ideal.indexed_roots] at hbackend
  simp_rw [← ideal.length_indexed] at hbackend
  exact (RootSubset.Left.pieceEquiv ideal.toRootSubset hthree degree).finrank_eq.trans hbackend

/-- No quotient degree above the selected-root cardinality contributes to the rank polynomial. -/
theorem piece_finrank_above (family : TriangularFamily ideal) (degree : ℕ)
    (hdegree : ideal.carrier.ncard < degree) :
    Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) = 0 := by
  classical
  rw [piece_finrank family, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hempty : (Finset.univ.filter fun vertex : DihedralGroup n =>
      ideal.toRootSubset.length vertex = degree) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro vertex hvertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvertex
    have hbound := ideal.indexed.length_le_card_roots vertex
    rw [← ideal.length_indexed, ← ideal.ncard_indexed] at hbound
    omega
  rw [hempty, Finset.card_empty]

/-- The full quotient rank polynomial equals the displayed H-length sum. -/
theorem rankPolynomial_eq (family : TriangularFamily ideal) :
    HessenbergIdeal.Left.rankPolynomial ideal = ideal.lengthPolynomial := by
  classical
  apply Polynomial.ext
  intro degree
  rw [HessenbergIdeal.Left.rankPolynomial_coeff, piece_finrank family, ideal.coeff,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end Left

namespace Right

/-- A qualifying family gives the quotient degree multiplicities. -/
theorem piece_finrank (family : TriangularFamily ideal) (degree : ℕ) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) =
      Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} := by
  classical
  have hbackend := _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_of_triangular
    ideal.indexed
    family.backend family.backend_support family.backend_diagonal family.backend_bound degree
  change Module.finrank ℂ
      ((dihedralGradedReflectionData n hthree).rightQuotientPiece
        (ideal.indexed.roots : Set (PositiveRootIndex n)) degree) = _ at hbackend
  rw [ideal.indexed_roots] at hbackend
  simp_rw [← ideal.length_indexed] at hbackend
  exact (RootSubset.Right.pieceEquiv ideal.toRootSubset hthree degree).finrank_eq.trans hbackend

/-- No quotient degree above the selected-root cardinality contributes to the rank polynomial. -/
theorem piece_finrank_above (family : TriangularFamily ideal) (degree : ℕ)
    (hdegree : ideal.carrier.ncard < degree) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) = 0 := by
  classical
  rw [piece_finrank family, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hempty : (Finset.univ.filter fun vertex : DihedralGroup n =>
      ideal.toRootSubset.length vertex = degree) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro vertex hvertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvertex
    have hbound := ideal.indexed.length_le_card_roots vertex
    rw [← ideal.length_indexed, ← ideal.ncard_indexed] at hbound
    omega
  rw [hempty, Finset.card_empty]

/-- The full quotient rank polynomial equals the displayed H-length sum. -/
theorem rankPolynomial_eq (family : TriangularFamily ideal) :
    HessenbergIdeal.Right.rankPolynomial ideal = ideal.lengthPolynomial := by
  classical
  apply Polynomial.ext
  intro degree
  rw [HessenbergIdeal.Right.rankPolynomial_coeff, piece_finrank family, ideal.coeff,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end Right

end Schubert.DihedralSplines.TriangularFamily
