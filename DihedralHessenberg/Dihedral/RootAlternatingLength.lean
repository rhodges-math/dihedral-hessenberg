import DihedralHessenberg.Dihedral.RootAlternatingProduct
import DihedralHessenberg.Dihedral.AlternatingPrefixes

/-! # Lengths of alternating simple-root products -/

namespace Schubert.Dihedral.PositiveRoot

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A bounded alternating product of the two simple vectors has its specified length. -/
theorem alternating_length (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (size : ℕ) (hbound : size ≤ n) :
    length n hthree (alpha.alternatingProduct beta size) = size := by
  obtain ⟨simple, rfl, rfl⟩ := simple_pair_index alpha beta hpair
  have heq : (simpleRoot n hthree simple).alternatingProduct
      (simpleRoot n hthree simple.rev) size = alternatingPrefixProduct n hthree simple size := by
    simpa only [Fin.rev_rev, alternatingPrefixProduct] using
      alternatingProduct_indexed n hthree simple.rev size
  rw [heq, length_alternatingPrefixProduct n hthree simple size hbound]

/-- The other simple reflection ascends at a bounded alternating product. -/
theorem alternating_ascent (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (size : ℕ) (hbound : size + 1 ≤ n) :
    length n hthree (alpha.reflection * beta.alternatingProduct alpha size) = size + 1 := by
  rw [← alternating_succ]
  exact alternating_length alpha beta hpair (size + 1) hbound

/-- The first simple reflection descends at a nonempty bounded alternating product. -/
theorem alternating_descent (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (size : ℕ) (hpositive : 0 < size) (hbound : size ≤ n) :
    length n hthree (beta.reflection * beta.alternatingProduct alpha size) + 1 = size := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  rw [alternating_succ, ← mul_assoc, beta.reflection_square, one_mul,
    alternating_length alpha beta hpair previous (by omega)]

end Schubert.Dihedral.PositiveRoot
