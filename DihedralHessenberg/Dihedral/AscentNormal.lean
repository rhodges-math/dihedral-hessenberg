import DihedralHessenberg.Dihedral.AlternatingAppend
import DihedralHessenberg.Dihedral.RankTwoRootVectors

/-! # Alternating normal forms determined by an ascent -/

namespace Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem actual_normal (element : DihedralGroup n) :
    ∃ alpha beta : PositiveRoot n,
      ((alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
        (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) ∧
      element = alpha.alternatingProduct beta (length n hthree element) := by
  obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element⁻¹
  have hswap : second = first.rev := by fin_cases first <;> fin_cases second <;> simp_all
  subst second
  refine ⟨simpleRoot n hthree first.rev, simpleRoot n hthree first, ?_, ?_⟩
  · fin_cases first
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rw [PositiveRoot.alternatingProduct_indexed, CoxeterSystem.wordProd_reverse,
      ← length_inv n hthree element, hprod, inv_inv]

/-- A simple left ascent determines the opposite-root alternating normal form. -/
theorem left_ascent_normal (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (element : DihedralGroup n) (hpositive : 0 < length n hthree element)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    element = beta.alternatingProduct alpha (length n hthree element) := by
  obtain ⟨first, second, horientation, hnormal⟩ := actual_normal element
  have hbound := length_le_polygon_parameter n hthree element
  have hpairs : (first = alpha ∧ second = beta) ∨ (first = beta ∧ second = alpha) := by
    rcases horientation with hfirst | hsecond <;> rcases hpair with halpha | hbeta
    · exact Or.inl ⟨hfirst.1.trans halpha.1.symm, hfirst.2.trans halpha.2.symm⟩
    · exact Or.inr ⟨hfirst.1.trans hbeta.2.symm, hfirst.2.trans hbeta.1.symm⟩
    · exact Or.inr ⟨hsecond.1.trans halpha.2.symm, hsecond.2.trans halpha.1.symm⟩
    · exact Or.inl ⟨hsecond.1.trans hbeta.1.symm, hsecond.2.trans hbeta.2.symm⟩
  rcases hpairs with hfirst | hsecond
  · rw [hfirst.1, hfirst.2] at hnormal
    have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
        (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
      rcases hpair with hfirst | hsecond
      · exact Or.inr ⟨hfirst.2, hfirst.1⟩
      · exact Or.inl ⟨hsecond.2, hsecond.1⟩
    have hdescent := PositiveRoot.alternating_descent beta alpha hreverse _ hpositive hbound
    rw [← hnormal] at hdescent
    omega
  · simpa only [hsecond.1, hsecond.2] using hnormal


/-- The successive right-ascent prefixes follow the two folded polygon chains. -/
theorem right_ascent_prefix_length (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (element : DihedralGroup n) (hpositive : 0 < length n hthree element)
    (hascent : length n hthree (element * alpha.reflection) = length n hthree element + 1)
    (size : ℕ) (hbound : length n hthree element + size ≤ 2 * n) :
    length n hthree (element * alpha.alternatingProduct beta size) =
      min (length n hthree element + size) (2 * n - (length n hthree element + size)) := by
  have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
    rcases hpair with hfirst | hsecond
    · exact Or.inr ⟨hfirst.2, hfirst.1⟩
    · exact Or.inl ⟨hsecond.2, hsecond.1⟩
  have hinvAscent : length n hthree (alpha.reflection * element⁻¹) =
      length n hthree element⁻¹ + 1 := by
    have hinv : alpha.reflection * element⁻¹ = (element * alpha.reflection)⁻¹ := by
      rw [mul_inv_rev, PositiveRoot.reflection_inv]
    rw [hinv, length_inv, length_inv]
    exact hascent
  have hnormal := left_ascent_normal alpha beta hpair element⁻¹
    (by simpa only [length_inv] using hpositive) hinvAscent
  rw [length_inv] at hnormal
  have hnormalInv := congrArg (fun x : DihedralGroup n => x⁻¹) hnormal
  rw [inv_inv, PositiveRoot.alternating_inv] at hnormalInv
  by_cases heven : Even (length n hthree element)
  · rw [ite_eq_left heven] at hnormalInv
    have hconcat := PositiveRoot.alternating_append alpha beta (length n hthree element) size
    rw [ite_eq_left heven, ← hnormalInv] at hconcat
    rw [← hconcat]
    exact PositiveRoot.alternating_folded_length alpha beta hpair _ hbound
  · rw [ite_eq_right heven] at hnormalInv
    have hconcat := PositiveRoot.alternating_append beta alpha (length n hthree element) size
    rw [ite_eq_right heven, ← hnormalInv] at hconcat
    rw [← hconcat]
    exact PositiveRoot.alternating_folded_length beta alpha hreverse _ hbound

end Schubert.Dihedral
