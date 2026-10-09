import DihedralHessenberg.Paper.PaperFull
import DihedralHessenberg.Paper.PaperGrading
import DihedralHessenberg.Dihedral.RankTwoRootVectors

/-! # Homogeneous upper splines and the full Schubert top -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- A homogeneous geometric spline with nonzero diagonal and Bruhat-upper support. -/
structure HomogeneousAt {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (vertex : DihedralGroup n) where
  /-- The polynomial-valued spline. -/
  value : ideal.toRootSubset.Spline
  /-- Its values are homogeneous of the H-inversion degree. -/
  homogeneous : value ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex)
  /-- All values outside the Bruhat upper ideal vanish. -/
  support : ∀ current, ¬ BruhatLE n hthree vertex current →
    (value : DihedralGroup n → CoordinatePolynomial) current = 0
  /-- Its diagonal value is nonzero. -/
  diagonal : (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0

namespace SchubertSpline

/-- The product of the untransformed forms of all positive roots. -/
def topProduct (n : ℕ) : CoordinatePolynomial := ∏ alpha : PositiveRoot n, alpha.form

/-- The Schubert top function has the positive-form product only at the longest element. -/
def topFunction (n : ℕ) (hthree : 3 ≤ n) : DihedralGroup n → CoordinatePolynomial :=
  fun vertex => if vertex = longestElement n hthree then topProduct n else 0

/-- Every positive-root form divides the Schubert top product. -/
theorem form_dvd_topProduct (n : ℕ) (alpha : PositiveRoot n) :
    alpha.form ∣ topProduct n := by
  classical
  exact Finset.dvd_prod_of_mem (fun beta : PositiveRoot n => beta.form) (Finset.mem_univ alpha)

/-- The untransformed positive-root product is nonzero. -/
theorem topProduct_ne_zero (n : ℕ) : topProduct n ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun alpha _ => alpha.form_ne_zero)

/-- The positive-root product is homogeneous of the number of positive vectors. -/
theorem topProduct_homogeneous (n : ℕ) : (topProduct n).IsHomogeneous n := by
  classical
  have hcard : Fintype.card (PositiveRoot n) = n := by
    simpa using (Fintype.card_congr (positiveRootEquiv n)).symm
  have hproduct := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun alpha : PositiveRoot n => alpha.form) (fun _ => 1) (fun alpha _ => by
      rw [alpha.form_index]
      exact rootPolynomial_isHomogeneous n alpha.index)
  simpa [topProduct, hcard] using hproduct

/-- The fixed-form left conditions make the Schubert top function a full spline. -/
theorem topFunction_isSpline (n : ℕ) (hthree : 3 ≤ n) :
    (RootSubset.full n).IsSpline (topFunction n hthree) := by
  apply (RootSubset.full_iff_left n hthree _).mpr
  intro vertex alpha
  have hdivides := form_dvd_topProduct n alpha
  change alpha.form ∣ (if vertex = longestElement n hthree then topProduct n else 0) -
    (if alpha.reflection * vertex = longestElement n hthree then topProduct n else 0)
  by_cases hvertex : vertex = longestElement n hthree
  · by_cases hreflect : alpha.reflection * vertex = longestElement n hthree
    · simp only [ite_eq_left hvertex, ite_eq_left hreflect, sub_self]
      exact dvd_zero _
    · simpa only [ite_eq_left hvertex, ite_eq_right hreflect, sub_zero] using hdivides
  · by_cases hreflect : alpha.reflection * vertex = longestElement n hthree
    · simpa only [ite_eq_right hvertex, ite_eq_left hreflect, zero_sub] using hdivides.neg_right
    · simp only [ite_eq_right hvertex, ite_eq_right hreflect, sub_self]
      exact dvd_zero _

/-- The full geometric Schubert top spline. -/
def top (n : ℕ) (hthree : 3 ≤ n) : (HessenbergIdeal.full n hthree).toRootSubset.Spline :=
  ⟨topFunction n hthree, topFunction_isSpline n hthree⟩

/-- Its evaluation is the untransformed positive-root product at the longest element. -/
theorem top_apply (n : ℕ) (hthree : 3 ≤ n) (vertex : DihedralGroup n) :
    (top n hthree : DihedralGroup n → CoordinatePolynomial) vertex =
      if vertex = longestElement n hthree then ∏ alpha : PositiveRoot n, alpha.form else 0 := rfl

/-- The Schubert top has nonzero value at the longest element. -/
theorem top_nonzero (n : ℕ) (hthree : 3 ≤ n) :
    (top n hthree : DihedralGroup n → CoordinatePolynomial) (longestElement n hthree) ≠ 0 := by
  simpa [top_apply, topProduct] using topProduct_ne_zero n

/-- Every value of the Schubert top is homogeneous of the Coxeter top degree. -/
theorem top_homogeneous (n : ℕ) (hthree : 3 ≤ n) :
    top n hthree ∈ (HessenbergIdeal.full n hthree).toRootSubset.piece n := by
  intro vertex
  rw [top_apply]
  by_cases heq : vertex = longestElement n hthree
  · simpa [heq, topProduct] using topProduct_homogeneous n
  · simp only [ite_eq_right heq]
    exact MvPolynomial.isHomogeneous_zero _ _ _

/-- The Schubert top is supported above the longest element in Bruhat order. -/
theorem top_support (n : ℕ) (hthree : 3 ≤ n) (vertex : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree (longestElement n hthree) vertex) :
    (top n hthree : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
  rw [top_apply]
  apply ite_eq_right
  intro heq
  apply hnot
  rw [heq]
  exact bruhatLE_refl n hthree _

end SchubertSpline

end Schubert.DihedralSplines
