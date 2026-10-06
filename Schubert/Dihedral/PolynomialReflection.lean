import Schubert.Dihedral.BinaryPolynomialBasis

/-! # Reflection traces of homogeneous binary polynomial actions -/

noncomputable section
namespace Schubert.Dihedral

/-- Any reflection reverses the monomial index and multiplies by its rotation weight. -/
theorem binaryPolynomialBasis_sr (n : ℕ) [NeZero n] (degree : ℕ)
    (coordinate : ZMod n) (index : Fin (degree + 1)) :
    polynomialPieceRepresentation n degree (.sr coordinate)
        (binaryPolynomialBasis degree index) =
      (ZMod.stdAddChar ((((degree : ℤ) - 2 * index.val : ℤ) : ZMod n) * coordinate) *
        (-1 : ℂ) ^ degree) • binaryPolynomialBasis degree index.rev := by
  have hgroup : DihedralGroup.sr coordinate = firstSimpleReflection n * .r coordinate := by
    simp [firstSimpleReflection, DihedralGroup.sr_mul_r]
  rw [hgroup, map_mul]
  change polynomialPieceRepresentation n degree (firstSimpleReflection n)
    (polynomialPieceRepresentation n degree (.r coordinate)
      (binaryPolynomialBasis degree index)) = _
  rw [binaryPolynomialBasis_r, map_smul, binaryPolynomialBasis_s1, smul_smul]

/-- A reflection diagonal entry is one precisely at the middle monomial. -/
theorem binaryPolynomialBasis_sr_diagonal (n : ℕ) [NeZero n] (degree : ℕ)
    (coordinate : ZMod n) (index : Fin (degree + 1)) :
    (binaryPolynomialBasis degree).repr
      (polynomialPieceRepresentation n degree (.sr coordinate)
        (binaryPolynomialBasis degree index)) index = if index.rev = index then 1 else 0 := by
  classical
  rw [binaryPolynomialBasis_sr, map_smul]
  by_cases hfixed : index.rev = index
  · have hdegree : degree = 2 * index.val := by
      have hval := congrArg Fin.val hfixed
      have hbound := index.isLt
      simp only [Fin.val_rev] at hval
      omega
    have heven : Even degree := ⟨index.val, by omega⟩
    have hweight : (degree : ℤ) - 2 * index.val = 0 := by omega
    simp [hfixed, hweight, heven.neg_one_pow]
  · simp [hfixed, Module.Basis.repr_self]

/-- Reversal has one fixed index in even degree and none in odd degree. -/
theorem binary_index_fixed_sum (degree : ℕ) :
    (∑ index : Fin (degree + 1), if index.rev = index then (1 : ℂ) else 0) =
      if Even degree then 1 else 0 := by
  classical
  by_cases heven : Even degree
  · obtain ⟨half, hhalf⟩ := heven
    have hdegree : degree = 2 * half := by omega
    let middle : Fin (degree + 1) := ⟨half, by omega⟩
    have hfixed : middle.rev = middle := by
      apply Fin.ext
      simp only [Fin.val_rev]
      dsimp [middle]
      omega
    rw [ite_eq_left ⟨half, hhalf⟩]
    rw [Finset.sum_eq_single middle]
    · simp [hfixed]
    · intro index _ hne
      have hnot : index.rev ≠ index := by
        intro heq
        apply hne
        apply Fin.ext
        have hval := congrArg Fin.val heq
        have hbound := index.isLt
        simp only [Fin.val_rev] at hval
        change index.val = half
        omega
      simp [hnot]
    · simp
  · rw [ite_eq_right heven]
    apply Finset.sum_eq_zero
    intro index _
    have hnot : index.rev ≠ index := by
      intro heq
      apply heven
      refine ⟨index.val, ?_⟩
      have hval := congrArg Fin.val heq
      have hbound := index.isLt
      simp only [Fin.val_rev] at hval
      omega
    simp [hnot]

/-- Every reflection has the parity character of the polynomial degree. -/
theorem polynomialPiece_character_sr (n : ℕ) [NeZero n]
    (degree : ℕ) (coordinate : ZMod n) :
    (polynomialPieceFDRep n degree).character (.sr coordinate) =
      if Even degree then 1 else 0 := by
  classical
  change LinearMap.trace ℂ _ (polynomialPieceRepresentation n degree (.sr coordinate)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (binaryPolynomialBasis degree), Matrix.trace]
  calc
    _ = ∑ index : Fin (degree + 1), if index.rev = index then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, binaryPolynomialBasis_sr_diagonal]
    _ = _ := binary_index_fixed_sum degree

end Schubert.Dihedral
