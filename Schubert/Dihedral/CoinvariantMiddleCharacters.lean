import Schubert.Dihedral.CoinvariantPieceBasis
import Schubert.Dihedral.CoinvariantAxialRepresentation

/-! # Characters on the middle coinvariant degree pieces -/

noncomputable section

namespace Schubert.Dihedral.Coinvariant.Middle

/-- Every middle-degree rotation has the sum of its two axial eigenvalues as character. -/
theorem character_r (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (hpositive : 0 < degree) (hbelow : degree < n) (coordinate : ZMod n) :
    (coinvariantPieceFDRep n degree).character (.r coordinate) =
      ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^ degree +
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^ degree := by
  obtain ⟨basis, hfirst, hsecond⟩ :=
    exists_coinvariant_middle_piece_basis n hthree degree hpositive hbelow
  rw [coinvariantPieceFDRep_character]
  rw [Schubert.FiniteGroupCharacters.Eigenbasis.character_eq_sum
    (coinvariantPieceRepresentation n degree) basis (.r coordinate)
    ![((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^ degree,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^ degree]]
  · simp [Fin.sum_univ_two]
  · intro index
    apply Subtype.ext
    fin_cases index
    · change coinvariantRepresentation n (.r coordinate) (basis 0 : CoinvariantAlgebra n) =
        ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^ degree •
          (basis 0 : CoinvariantAlgebra n)
      rw [hfirst]
      exact Coinvariant.r_u_pow n coordinate degree
    · change coinvariantRepresentation n (.r coordinate) (basis 1 : CoinvariantAlgebra n) =
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^ degree •
          (basis 1 : CoinvariantAlgebra n)
      rw [hsecond]
      exact Coinvariant.r_v_pow n coordinate degree

/-- A middle-degree simple reflection has zero character. -/
theorem character_s1 (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (hpositive : 0 < degree) (hbelow : degree < n) :
    (coinvariantPieceFDRep n degree).character (firstSimpleReflection n) = 0 := by
  obtain ⟨basis, hfirst, hsecond⟩ :=
    exists_coinvariant_middle_piece_basis n hthree degree hpositive hbelow
  rw [coinvariantPieceFDRep_character]
  apply Schubert.FiniteGroupCharacters.representation_character_eq_zero_of_swap
    (coinvariantPieceRepresentation n degree) basis (firstSimpleReflection n)
    ((-1 : ℂ) ^ degree) ((-1 : ℂ) ^ degree)
  · apply Subtype.ext
    simpa only [coinvariantPieceRepresentation_apply_coe, Submodule.coe_smul, hfirst, hsecond]
      using Coinvariant.s1_u_pow n degree
  · apply Subtype.ext
    simpa only [coinvariantPieceRepresentation_apply_coe, Submodule.coe_smul, hfirst, hsecond]
      using Coinvariant.s1_v_pow n degree

/-- Every reflection has zero character on a middle coinvariant degree piece. -/
theorem character_sr (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (hpositive : 0 < degree) (hbelow : degree < n) (coordinate : ZMod n) :
    (coinvariantPieceFDRep n degree).character (.sr coordinate) = 0 := by
  obtain ⟨basis, hfirst, hsecond⟩ :=
    exists_coinvariant_middle_piece_basis n hthree degree hpositive hbelow
  rw [coinvariantPieceFDRep_character]
  apply Schubert.FiniteGroupCharacters.representation_character_eq_zero_of_swap
    (coinvariantPieceRepresentation n degree) basis (.sr coordinate)
    (((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^ degree *
      (-1 : ℂ) ^ degree)
    ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^ degree *
      (-1 : ℂ) ^ degree)
  · apply Subtype.ext
    change coinvariantRepresentation n (.sr coordinate) (basis 0 : CoinvariantAlgebra n) = _
    rw [hfirst]
    have hgroup : DihedralGroup.sr coordinate =
        firstSimpleReflection n * DihedralGroup.r coordinate := by
      simp [firstSimpleReflection, DihedralGroup.sr_mul_r]
    rw [hgroup, map_mul, Module.End.mul_apply, Coinvariant.r_u_pow,
      map_smul, Coinvariant.s1_u_pow, smul_smul]
    simp only [Submodule.coe_smul, hsecond]
  · apply Subtype.ext
    change coinvariantRepresentation n (.sr coordinate) (basis 1 : CoinvariantAlgebra n) = _
    rw [hsecond]
    have hgroup : DihedralGroup.sr coordinate =
        firstSimpleReflection n * DihedralGroup.r coordinate := by
      simp [firstSimpleReflection, DihedralGroup.sr_mul_r]
    rw [hgroup, map_mul, Module.End.mul_apply, Coinvariant.r_v_pow,
      map_smul, Coinvariant.s1_v_pow, smul_smul]
    simp only [Submodule.coe_smul, hfirst]

end Schubert.Dihedral.Coinvariant.Middle
