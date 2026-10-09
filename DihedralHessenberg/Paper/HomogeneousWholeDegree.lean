import DihedralHessenberg.Paper.PaperGrading
import DihedralHessenberg.Paper.HomogeneousFamily

/-! # The degree of a nonzero homogeneous spline -/

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

/-- A nonzero homogeneous spline has its whole-spline degree. -/
theorem homogeneous_degree {degree : ℕ} {value : selected.Spline}
    (hvalue : value ∈ selected.piece degree) (hnonzero : value ≠ 0) :
    selected.degree value = degree := by
  classical
  have hexists : ∃ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hnonzero
    apply Subtype.ext
    exact funext hnot
  obtain ⟨vertex, hvertex⟩ := hexists
  apply le_antisymm
  · exact (selected.degree_le_iff value degree).2 fun current =>
      (hvalue current).totalDegree_le
  · rw [← (hvalue vertex).totalDegree hvertex]
    exact Finset.le_sup (f := fun current =>
      ((value : DihedralGroup n → CoordinatePolynomial) current).totalDegree)
      (Finset.mem_univ vertex)

/-- A nonzero spline belongs to at most one homogeneous degree. -/
theorem homogeneous_degree_unique {first second : ℕ} {value : selected.Spline}
    (hfirst : value ∈ selected.piece first) (hsecond : value ∈ selected.piece second)
    (hnonzero : value ≠ 0) : first = second :=
  (selected.homogeneous_degree hfirst hnonzero).symm.trans
    (selected.homogeneous_degree hsecond hnonzero)

end Schubert.Dihedral.RootSubset
