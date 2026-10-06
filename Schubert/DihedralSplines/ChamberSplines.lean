import Schubert.Dihedral.RootFrame
import Schubert.DihedralSplines.PaperSpline

/-! # Spline invariance under the signed representatives of a root chamber -/

noncomputable section
namespace Schubert.Dihedral.Separator

open Schubert.DihedralSplines

private theorem form_neg (vector : RealPlane) :
    linearPolynomial (complexify (-vector)) = -linearPolynomial (complexify vector) := by
  have heq : complexify (-vector) = -complexify vector := by
    funext coordinate
    simp only [complexify, Pi.neg_apply, Complex.ofReal_neg]
  rw [heq]
  simp only [linearPolynomial, Pi.neg_apply, map_neg]
  ring

private theorem choose_condition {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (alpha : PositiveRoot n) (vertex : DihedralGroup n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    linearPolynomial (complexify (realAction n vertex (data.choose alpha).val)) ∣
        value vertex - value (vertex * (data.reflectionEquiv hthree (data.choose alpha)).val) ↔
      linearPolynomial (complexify (realAction n vertex alpha.val)) ∣
        value vertex - value (vertex * alpha.reflection) := by
  rw [data.reflection_choose]
  unfold choose
  split_ifs
  · rfl
  · rw [realAction_neg, form_neg, neg_dvd]

/-- Choosing a signed root representative preserves every edge-label ideal. -/
theorem label_ideal_signs {n : ℕ} (data : Separator n) (alpha : PositiveRoot n)
    (vertex : DihedralGroup n) :
    Ideal.span {linearPolynomial (complexify (realAction n vertex (data.choose alpha).val))} =
      Ideal.span {linearPolynomial (complexify (realAction n vertex alpha.val))} := by
  unfold choose
  split_ifs
  · rfl
  · rw [realAction_neg, form_neg, Ideal.span_singleton_neg]

/-- Any generic chamber chooses signs without changing the geometric spline condition. -/
theorem spline_signs {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (selected : RootSubset n) (value : DihedralGroup n → CoordinatePolynomial) :
    selected.IsSpline value ↔
      ∀ vertex (alpha : data.Positive),
        alpha.val ∈ (fun beta : PositiveRoot n => (data.choose beta).val) ''
          {beta | beta.val ∈ selected} →
        linearPolynomial (complexify (realAction n vertex alpha.val)) ∣
          value vertex - value (vertex * (data.reflectionEquiv hthree alpha).val) := by
  constructor
  · intro hvalue vertex alpha halpha
    obtain ⟨beta, hbeta, heq⟩ := halpha
    have hroot : data.choose beta = alpha := Subtype.ext heq
    rw [← hroot]
    apply (choose_condition data hthree beta vertex value).mpr
    have hsame : selected.root beta.val hbeta = beta := Subtype.ext rfl
    simpa only [hsame] using hvalue vertex beta.val hbeta
  · intro hvalue vertex vector hvector
    let beta := selected.root vector hvector
    have hcondition := hvalue vertex (data.choose beta) ⟨beta, hvector, rfl⟩
    exact (choose_condition data hthree beta vertex value).mp hcondition

/-- The set of spline functions is unchanged when a generic chamber chooses root signs. -/
theorem spline_set_signs {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (selected : RootSubset n) :
    (selected.splineAlgebra : Set (DihedralGroup n → CoordinatePolynomial)) =
      {value | ∀ vertex (alpha : data.Positive),
        alpha.val ∈ (fun beta : PositiveRoot n => (data.choose beta).val) ''
          {beta | beta.val ∈ selected} →
        linearPolynomial (complexify (realAction n vertex alpha.val)) ∣
          value vertex - value (vertex * (data.reflectionEquiv hthree alpha).val)} := by
  ext value
  exact data.spline_signs hthree selected value

end Schubert.Dihedral.Separator
