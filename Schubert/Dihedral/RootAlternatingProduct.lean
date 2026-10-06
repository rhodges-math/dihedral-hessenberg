import Schubert.Dihedral.RootAlternatingWords

/-! # Alternating reflection product formulas -/

namespace Schubert.Dihedral.PositiveRoot

/-- The empty alternating product is the identity. -/
theorem alternating_zero {n : ℕ} (alpha beta : PositiveRoot n) :
    alpha.alternatingProduct beta 0 = 1 := rfl

/-- An alternating product begins with its prescribed first reflection. -/
theorem alternating_succ {n : ℕ} (alpha beta : PositiveRoot n) (size : ℕ) :
    alpha.alternatingProduct beta (size + 1) =
      alpha.reflection * beta.alternatingProduct alpha size := by
  unfold alternatingProduct
  rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_concat,
    List.map_cons, List.prod_cons]

/-- Even alternating products are powers of the two-reflection product. -/
theorem alternating_even {n : ℕ} (alpha beta : PositiveRoot n) (half : ℕ) :
    alpha.alternatingProduct beta (2 * half) =
      (alpha.reflection * beta.reflection) ^ half := by
  induction half with
  | zero => rw [Nat.mul_zero, alternating_zero, pow_zero]
  | succ half ih =>
    have hsize : 2 * (half + 1) = (2 * half + 1) + 1 := by omega
    rw [hsize, alternating_succ, alternating_succ, ih, pow_succ', mul_assoc]

/-- Odd alternating products end with their first reflection. -/
theorem alternating_odd {n : ℕ} (alpha beta : PositiveRoot n) (half : ℕ) :
    alpha.alternatingProduct beta (2 * half + 1) =
      (alpha.reflection * beta.reflection) ^ half * alpha.reflection := by
  induction half with
  | zero => rw [Nat.mul_zero, zero_add, alternating_succ, alternating_zero, pow_zero,
      mul_one, one_mul]
  | succ half ih =>
    have hsize : 2 * (half + 1) + 1 = ((2 * half + 1) + 1) + 1 := by omega
    rw [hsize, alternating_succ, alternating_succ, ih, pow_succ', mul_assoc, mul_assoc]

end Schubert.Dihedral.PositiveRoot
