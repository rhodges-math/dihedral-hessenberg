import Schubert.DihedralSplines.SchubertRecursion
import Schubert.Dihedral.RootSubsetCard
import Schubert.Dihedral.LeftAscentBijection
import Schubert.Dihedral.RootNormal

/-! # The product of left-inversion root forms -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral
open scoped BigOperators Classical

/-- The untransformed product over the positive left-inversion vectors. -/
def diagonalProduct (n : ℕ) (vertex : DihedralGroup n) : CoordinatePolynomial :=
  ∏ alpha ∈ (Finset.univ : Finset (PositiveRoot n)).filter
    (fun alpha => alpha.val ∈ leftInversionSet n vertex), alpha.form

/-- No left-inversion form occurs at the identity. -/
theorem diagonalProduct_one (n : ℕ) (hthree : 3 ≤ n) : diagonalProduct n 1 = 1 := by
  have hempty : (Finset.univ : Finset (PositiveRoot n)).filter
      (fun alpha => alpha.val ∈ leftInversionSet n 1) = ∅ := by
    apply Finset.ext
    intro alpha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hinversion
      rw [← alpha.index_val, mem_leftInversionSet n hthree,
        mem_leftInversions, Schubert.Dihedral.length_one] at hinversion
      exact False.elim ((Nat.not_lt_zero _) hinversion)
    · intro hfalse
      simp at hfalse
  simp only [diagonalProduct, hempty, Finset.prod_empty]

/-- Every product of left-inversion forms is nonzero. -/
theorem diagonalProduct_ne_zero (n : ℕ) (vertex : DihedralGroup n) :
    diagonalProduct n vertex ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun alpha _ => alpha.form_ne_zero)

/-- At the longest element, the left-inversion product is the full Schubert top. -/
theorem diagonalProduct_top (n : ℕ) (hthree : 3 ≤ n) :
    diagonalProduct n (longestElement n hthree) = topProduct n := by
  have hfilter : (Finset.univ : Finset (PositiveRoot n)).filter
      (fun beta => beta.val ∈ leftInversionSet n (longestElement n hthree)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro beta _
    rw [← beta.index_val, mem_leftInversionSet n hthree]
    change beta.index ∈ leftInversions n hthree
      ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n))
    rw [IndexedInversions.left_top]
    exact Finset.mem_univ _
  simp only [diagonalProduct, hfilter, topProduct]

/-- The insertion and geometric action on left inversions give the exact product recurrence. -/
theorem diagonalProduct_ascent {n : ℕ} [NeZero n] (hthree : 3 ≤ n)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (vertex : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1) :
    diagonalProduct n (alpha.reflection * vertex) =
      alpha.form * polynomialAction n alpha.reflection (diagonalProduct n vertex) := by
  let current := (Finset.univ : Finset (PositiveRoot n)).filter
    (fun beta => beta.val ∈ leftInversionSet n (alpha.reflection * vertex))
  have hmem : alpha ∈ current := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [alpha.left_ascent hthree hsimple vertex hascent]
    exact Set.mem_insert _ _
  obtain ⟨equivalence, himage⟩ := alpha.left_ascent_equiv hthree hsimple vertex hascent
  have herase : (∏ beta ∈ current.erase alpha, beta.form) =
      ∏ beta : {beta : PositiveRoot n //
        beta.val ∈ leftInversionSet n (alpha.reflection * vertex) ∧ beta ≠ alpha},
          beta.val.form := by
    apply Finset.prod_subtype
    intro beta
    simp only [Finset.mem_erase, current, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have horiginal : diagonalProduct n vertex =
      ∏ beta : {beta : PositiveRoot n // beta.val ∈ leftInversionSet n vertex},
        beta.val.form := by
    apply Finset.prod_subtype
    intro beta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (∏ beta ∈ current, beta.form) = _
  rw [← Finset.mul_prod_erase current (fun beta => beta.form) hmem, herase, horiginal,
    map_prod]
  congr 1
  rw [← equivalence.prod_comp (fun beta => beta.val.form)]
  apply Finset.prod_congr rfl
  intro beta _
  rw [PositiveRoot.action_form]
  change linearPolynomial (complexify (equivalence beta).val.val) = _
  rw [himage]

/-- Acting on the ascending product cancels the reflection and negates the inserted form. -/
theorem diagonalProduct_reflect {n : ℕ} [NeZero n] (hthree : 3 ≤ n)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (vertex : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1) :
    polynomialAction n alpha.reflection (diagonalProduct n (alpha.reflection * vertex)) =
      -(alpha.form * diagonalProduct n vertex) := by
  have hinvolution (polynomial : CoordinatePolynomial) :
      polynomialAction n alpha.reflection (polynomialAction n alpha.reflection polynomial) =
        polynomial := by
    change (polynomialAction n alpha.reflection * polynomialAction n alpha.reflection)
      polynomial = polynomial
    rw [← map_mul, alpha.reflection_square, map_one]
    rfl
  rw [diagonalProduct_ascent hthree alpha hsimple vertex hascent, map_mul,
    alpha.reflection_form, hinvolution, neg_mul]

/-- Every Schubert spline has the exact untransformed left-inversion product diagonal. -/
theorem diagonal_product (n : ℕ) (hthree : 3 ≤ n) [NeZero n] (vertex : DihedralGroup n) :
    (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) vertex =
      diagonalProduct n vertex := by
  generalize hmeasure : n - length n hthree vertex = measure
  induction measure using Nat.strong_induction_on generalizing vertex with
  | h measure ih =>
    by_cases hidentity : vertex = 1
    · subst vertex
      rw [spline_one, diagonalProduct_one n hthree]
      rfl
    by_cases htop : vertex = longestElement n hthree
    · subst vertex
      rw [spline_top, top_apply, diagonalProduct_top]
      simp only [ite_true, topProduct]
    let alpha := ascentRoot n hthree vertex hidentity htop
    have hsimple := (ascentRoot_spec n hthree vertex hidentity htop).1
    have hascent := (ascentRoot_spec n hthree vertex hidentity htop).2
    change (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) at hsimple
    change length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1 at hascent
    have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
    have hless : n - length n hthree (alpha.reflection * vertex) < measure := by omega
    have htail := ih _ hless (alpha.reflection * vertex) rfl
    have hzero : (spline n hthree (alpha.reflection * vertex) :
        DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
      apply support
      intro hcomparison
      have hlength := bruhatLE_length_le n hthree hcomparison
      omega
    rw [spline_step n hthree vertex hidentity htop]
    apply mul_left_cancel₀ alpha.form_ne_zero
    rw [difference_mul, hzero]
    change 0 - polynomialAction n alpha.reflection
      ((spline n hthree (alpha.reflection * vertex) :
        DihedralGroup n → CoordinatePolynomial) (alpha.reflection⁻¹ * vertex)) = _
    rw [alpha.reflection_inv, htail,
      diagonalProduct_reflect hthree alpha hsimple vertex hascent, zero_sub, neg_neg]

end Schubert.DihedralSplines.SchubertSpline
