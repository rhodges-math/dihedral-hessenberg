import Schubert.Dihedral.AlternatingDistinct
import Schubert.Dihedral.LongestElement

/-! # Canonical length fibers in rank two

There is one element of length zero, two elements of each length strictly between
zero and n, and one element of length n.
-/

namespace Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- The intermediate length fiber consists of the two alternating products. -/
theorem filter_length_eq_pair (degree : ℕ) (hshort : degree < n) :
    (Finset.univ.filter fun element : DihedralGroup n => length n hthree element = degree) =
      {(coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 degree),
        (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 1 0 degree)} := by
  classical
  ext element
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hlength
    obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element
    rw [hlength] at hprod
    fin_cases first <;> fin_cases second
    · exact (hne rfl).elim
    · exact Or.inl hprod.symm
    · exact Or.inr hprod.symm
    · exact (hne rfl).elim
  · rintro (rfl | rfl)
    · exact length_alternatingWord n hthree 0 1 (by decide) degree hshort.le
    · exact length_alternatingWord n hthree 1 0 (by decide) degree hshort.le

/-- Exactly two dihedral elements have each intermediate canonical length. -/
theorem card_length_eq_of_positive_lt (degree : ℕ) (hpositive : 0 < degree)
    (hshort : degree < n) :
    (Finset.univ.filter fun element : DihedralGroup n => length n hthree element = degree).card =
      2 := by
  classical
  rw [filter_length_eq_pair degree hshort]
  exact Finset.card_pair (alternatingWord_swap_ne n hthree degree hpositive hshort)

/-- Exactly one dihedral element has canonical length zero. -/
theorem card_length_eq_zero :
    (Finset.univ.filter fun element : DihedralGroup n => length n hthree element = 0).card = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun element : DihedralGroup n =>
      length n hthree element = 0) = {1} := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (coxeterSystem n hthree).length_eq_zero_iff
  rw [hfilter, Finset.card_singleton]

/-- Exactly one dihedral element has canonical length n. -/
theorem card_length_eq_n :
    (Finset.univ.filter fun element : DihedralGroup n => length n hthree element = n).card = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun element : DihedralGroup n =>
      length n hthree element = n) =
      {(coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)} := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact length_eq_n_iff_eq_alternatingWord n hthree element
  rw [hfilter, Finset.card_singleton]

end Schubert.Dihedral
