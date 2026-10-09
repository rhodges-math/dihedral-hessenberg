import DihedralHessenberg.Paper.PaperGraph
import DihedralHessenberg.Dihedral.RootFormProperties

/-! # Edge labels and conjugate reflections

The label `t_{w(α)}` of the edge from `w` to `w s_α` is, up to sign, the linear form `t_β` of a
positive root `β` exactly when `s_β w = w s_α`.
-/

noncomputable section
namespace Schubert.Dihedral.RootSubset
open Schubert.Dihedral

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

omit [NeZero n] in
private theorem form_neg (vector : RealPlane) :
    linearPolynomial (complexify (-vector)) = -linearPolynomial (complexify vector) := by
  simp only [linearPolynomial, complexify, Pi.neg_apply, Complex.ofReal_neg, map_neg]
  ring

/-- The label of the edge from `w` to `w s_α` is `± t_β` exactly when `s_β w = w s_α`. -/
theorem edgeLabel_eq_form_iff (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hmem : alpha.val ∈ selected) (beta : PositiveRoot n) :
    (selected.edgeLabel (selected.edge vertex alpha hmem) = beta.form ∨
      selected.edgeLabel (selected.edge vertex alpha hmem) = -beta.form) ↔
      beta.reflection * vertex = vertex * alpha.reflection := by
  rw [edgeLabel_edge]
  -- the image of `α` is a positive root `γ` up to sign, and its reflection is `w s_α w⁻¹`
  obtain ⟨gamma, hgamma⟩ : ∃ gamma : PositiveRoot n,
      realAction n vertex alpha.val = gamma.val ∨ realAction n vertex alpha.val = -gamma.val := by
    rcases realAction_mem n vertex alpha.val (Or.inl alpha.property) with hpositive | hnegative
    · exact ⟨⟨_, hpositive⟩, Or.inl rfl⟩
    · exact ⟨⟨_, hnegative⟩, Or.inr (neg_neg _).symm⟩
  have hreflection := PositiveRoot.signed_conjugation vertex alpha gamma hgamma
  have hconjugate : beta.reflection * vertex = vertex * alpha.reflection ↔ beta = gamma := by
    constructor
    · intro hcommute
      apply PositiveRoot.reflection_injective n
      rw [hreflection, ← hcommute]
      group
    · rintro rfl
      rw [hreflection]
      group
  rw [hconjugate]
  have hlabel : linearPolynomial (complexify (realAction n vertex alpha.val)) = gamma.form ∨
      linearPolynomial (complexify (realAction n vertex alpha.val)) = -gamma.form := by
    rcases hgamma with himage | himage
    · exact Or.inl (by rw [himage]; rfl)
    · exact Or.inr (by rw [himage, form_neg]; rfl)
  constructor
  · intro hbeta
    by_contra hne
    have hdistinct : gamma ≠ beta := fun heq => hne heq.symm
    rcases hlabel with hfirst | hfirst <;> rcases hbeta with hsecond | hsecond
    · refine PositiveRoot.form_not_proportional gamma beta hdistinct 1 ?_
      simp only [map_one, one_mul]
      linear_combination hsecond - hfirst
    · refine PositiveRoot.form_not_proportional gamma beta hdistinct (-1) ?_
      simp only [map_neg, map_one, neg_one_mul]
      linear_combination hsecond - hfirst
    · refine PositiveRoot.form_not_proportional gamma beta hdistinct (-1) ?_
      simp only [map_neg, map_one, neg_one_mul]
      linear_combination hfirst - hsecond
    · refine PositiveRoot.form_not_proportional gamma beta hdistinct 1 ?_
      simp only [map_one, one_mul]
      linear_combination hfirst - hsecond
  · rintro rfl
    exact hlabel

end Schubert.Dihedral.RootSubset
