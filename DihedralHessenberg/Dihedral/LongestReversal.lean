import DihedralHessenberg.Dihedral.LongestLength
import DihedralHessenberg.Dihedral.RankTwoRootVectors

/-! # Longest-element length complementation and Bruhat reversal -/

namespace Schubert.Dihedral

/-- Left multiplication by the longest element complements canonical length. -/
theorem length_longest_mul (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    length n hthree (longestElement n hthree * element) = n - length n hthree element :=
  length_alternatingWord_top_mul n hthree element

/-- Left multiplication by the longest element reverses canonical Bruhat order. -/
theorem bruhat_longest_mul (n : ℕ) (hthree : 3 ≤ n) (first second : DihedralGroup n) :
    BruhatLE n hthree (longestElement n hthree * first) (longestElement n hthree * second) ↔
      BruhatLE n hthree second first := by
  rw [bruhatLE_iff_eq_or_length_lt, bruhatLE_iff_eq_or_length_lt,
    mul_left_cancel_iff, length_longest_mul, length_longest_mul]
  have hfirst := length_le_polygon_parameter n hthree first
  have hsecond := length_le_polygon_parameter n hthree second
  constructor
  · rintro (heq | hlt)
    · exact Or.inl heq.symm
    · exact Or.inr (by omega)
  · rintro (heq | hlt)
    · exact Or.inl heq.symm
    · exact Or.inr (by omega)

end Schubert.Dihedral
