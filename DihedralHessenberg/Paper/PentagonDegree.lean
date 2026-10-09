import DihedralHessenberg.Paper.PentagonIdeal
import DihedralHessenberg.Dihedral.RootInversionSigns

/-! # Inversion degrees in the pentagon example -/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral
open scoped Classical

private theorem inversions_rotation (coordinate : ZMod 5) :
    ideal.indexed.inversions (.r coordinate) =
      ({0, 1, 2} : Finset (Fin 5)).filter (fun index =>
        5 ≤ (angularIndex index + 2 * coordinate.val) % 10) := by
  ext index
  simp only [HessenbergSpace.inversions, Finset.mem_inter, indexed_roots,
    mem_rightInversions_r_iff, Finset.mem_filter]

private theorem inversions_reflection (coordinate : ZMod 5) :
    ideal.indexed.inversions (.sr coordinate) =
      ({0, 1, 2} : Finset (Fin 5)).filter (fun index =>
        (angularIndex index + 2 * coordinate.val) % 10 = 0 ∨
          5 < (angularIndex index + 2 * coordinate.val) % 10) := by
  ext index
  simp only [HessenbergSpace.inversions, Finset.mem_inter, indexed_roots,
    mem_rightInversions_sr_iff, Finset.mem_filter]

/-- The ten displayed vertices have their word lengths. -/
theorem word_lengths (row : Fin 10) :
    length 5 (by decide) (vertices row) =
      (![0, 1, 1, 2, 2, 3, 3, 4, 4, 5] : Fin 10 → ℕ) row := by
  fin_cases row <;>
    norm_num only [vertices, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
      DihedralGroup.r_zero, pow_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change length 5 (by decide) (.r 0) = 0
    rw [length_r]
    decide
  · change length 5 (by decide) (.sr 1) = 1
    rw [length_sr]
    decide
  · change length 5 (by decide) (.sr 0) = 1
    rw [length_sr]
    decide
  · change length 5 (by decide) (.r 1) = 2
    rw [length_r]
    decide
  · change length 5 (by decide) (.r 4) = 2
    rw [length_r]
    decide
  · change length 5 (by decide) (.sr 2) = 3
    rw [length_sr]
    decide
  · change length 5 (by decide) (.sr 4) = 3
    rw [length_sr]
    decide
  · change length 5 (by decide) (.r 2) = 4
    rw [length_r]
    decide
  · change length 5 (by decide) (.r 3) = 4
    rw [length_r]
    decide
  · change length 5 (by decide) (.sr 3) = 5
    rw [length_sr]
    decide

/-- Their selected-root inversion degrees are zero, four ones, four twos, and three. -/
theorem degrees (row : Fin 10) :
    ideal.toRootSubset.length (vertices row) =
      (![0, 1, 1, 1, 2, 1, 2, 2, 2, 3] : Fin 10 → ℕ) row := by
  rw [ideal.length_indexed, HessenbergSpace.length]
  fin_cases row <;>
    norm_num only [vertices, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
      DihedralGroup.r_zero, pow_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change (ideal.indexed.inversions (.r 0)).card = 0
    rw [inversions_rotation]
    decide
  · change (ideal.indexed.inversions (.sr 1)).card = 1
    rw [inversions_reflection]
    decide
  · change (ideal.indexed.inversions (.sr 0)).card = 1
    rw [inversions_reflection]
    decide
  · change (ideal.indexed.inversions (.r 1)).card = 1
    rw [inversions_rotation]
    decide
  · change (ideal.indexed.inversions (.r 4)).card = 2
    rw [inversions_rotation]
    decide
  · change (ideal.indexed.inversions (.sr 2)).card = 1
    rw [inversions_reflection]
    decide
  · change (ideal.indexed.inversions (.sr 4)).card = 2
    rw [inversions_reflection]
    decide
  · change (ideal.indexed.inversions (.r 2)).card = 2
    rw [inversions_rotation]
    decide
  · change (ideal.indexed.inversions (.r 3)).card = 2
    rw [inversions_rotation]
    decide
  · change (ideal.indexed.inversions (.sr 3)).card = 3
    rw [inversions_reflection]
    decide

/-- The last displayed word is the longest element. -/
theorem last_vertex : vertices 9 = longestElement 5 (by decide) :=
  (length_eq_longest 5 (by decide) _).mp (word_lengths 9)

/-- The generating polynomial is the pentagon rank polynomial. -/
theorem polynomial : ideal.lengthPolynomial =
    1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X^2 + Polynomial.X^3 := by
  rw [ideal.lengthPolynomial_odd 1 (by simpa using cardinality)]
  norm_num [Finset.sum_range_succ]
  ring

end Schubert.DihedralSplines.Pentagon
