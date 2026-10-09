import DihedralHessenberg.Dihedral.CyclicVertices
import DihedralHessenberg.Dihedral.ReflectionIndex

/-! # Parity of reflected cyclic vertices -/

namespace Schubert.Dihedral.Cyclic

/-- Right multiplication by a root reflection exchanges cyclic position parity. -/
theorem reflection_parity {n : ℕ} {hthree : 3 ≤ n} (first second : Fin (2 * n))
    (alpha : PositiveRoot n)
    (heq : vertex n hthree second = vertex n hthree first * alpha.reflection) :
    Even first.val ↔ ¬Even second.val := by
  rw [Nat.even_iff, Nat.even_iff]
  rw [normal, normal, PositiveRoot.reflection, rootReflection_eq_sr] at heq
  by_cases hfirst : first.val % 2 = 0
  · by_cases hsecond : second.val % 2 = 0
    · rw [ite_eq_left hfirst, ite_eq_left hsecond, DihedralGroup.r_mul_sr] at heq
      cases heq
    · simp only [hfirst, hsecond, not_false_eq_true]
  · by_cases hsecond : second.val % 2 = 0
    · simp only [hfirst, hsecond, not_true_eq_false]
    · rw [ite_eq_right hfirst, ite_eq_right hsecond, DihedralGroup.sr_mul_sr] at heq
      cases heq

end Schubert.Dihedral.Cyclic
