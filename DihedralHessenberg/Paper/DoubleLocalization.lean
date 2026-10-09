import DihedralHessenberg.Dihedral.DoubleCoinvariant
import DihedralHessenberg.Dihedral.PolynomialPullback
import DihedralHessenberg.Paper.BorelEquivalence
import DihedralHessenberg.Paper.SchubertBasis

/-! # Double polynomial classes and full Schubert splines -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines.DoubleCoinvariant
open Schubert.Dihedral

/-- The double polynomial presentation localizes to the full spline algebra. -/
def localization (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    letI := Dihedral.DoubleCoinvariant.firstAlgebra n
    letI := (RootSubset.full n).leftAlgebra hthree
    Dihedral.DoubleCoinvariant.Presentation n ≃ₐ[CoordinatePolynomial]
      (RootSubset.full n).Spline := by
  letI := Dihedral.DoubleCoinvariant.firstAlgebra n
  letI := (RootSubset.full n).leftAlgebra hthree
  exact (Dihedral.DoubleCoinvariant.scalarEquiv n hthree).trans (borelEquiv n hthree)

/-- The first polynomial copy evaluates as the constant spline. -/
theorem localization_first (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) (vertex : DihedralGroup n) :
    (localization n hthree (Dihedral.DoubleCoinvariant.firstMap n polynomial)).val vertex =
      polynomial := by
  change (borelEquiv n hthree
    (Dihedral.DoubleCoinvariant.scalarEquiv n hthree
      (Dihedral.DoubleCoinvariant.firstMap n polynomial))).val vertex = _
  rw [show Dihedral.DoubleCoinvariant.scalarEquiv n hthree
      (Dihedral.DoubleCoinvariant.firstMap n polynomial) =
      polynomial ⊗ₜ[invariantSubalgebra n] 1 from
    Dihedral.DoubleCoinvariant.tensorEquiv_first n hthree polynomial]
  rw [borelEquiv_tmul]
  simp

/-- The second polynomial copy evaluates under the vertex action. -/
theorem localization_second (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) (vertex : DihedralGroup n) :
    (localization n hthree (Dihedral.DoubleCoinvariant.secondMap n polynomial)).val vertex =
      polynomialAction n vertex polynomial := by
  change (borelEquiv n hthree
    (Dihedral.DoubleCoinvariant.scalarEquiv n hthree
      (Dihedral.DoubleCoinvariant.secondMap n polynomial))).val vertex = _
  rw [show Dihedral.DoubleCoinvariant.scalarEquiv n hthree
      (Dihedral.DoubleCoinvariant.secondMap n polynomial) =
      1 ⊗ₜ[invariantSubalgebra n] polynomial from
    Dihedral.DoubleCoinvariant.tensorEquiv_second n hthree polynomial]
  rw [borelEquiv_tmul, one_mul]

/-- The double presentation has the basis of equivariant Schubert classes. -/
theorem schubert_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    letI := Dihedral.DoubleCoinvariant.firstAlgebra n
    letI := (RootSubset.full n).leftAlgebra hthree
    ∃ basis : Module.Basis (DihedralGroup n) CoordinatePolynomial
        (Dihedral.DoubleCoinvariant.Presentation n),
      ∀ vertex, localization n hthree (basis vertex) = SchubertSpline.spline n hthree vertex := by
  let := Dihedral.DoubleCoinvariant.firstAlgebra n
  let := (RootSubset.full n).leftAlgebra hthree
  let := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
  obtain ⟨basis, hbasis⟩ := SchubertSpline.left_basis n hthree
  let original : Module.Basis (DihedralGroup n) CoordinatePolynomial
      (RootSubset.full n).Spline := basis
  refine ⟨original.map (localization n hthree).symm.toLinearEquiv, ?_⟩
  intro vertex
  change localization n hthree ((localization n hthree).symm (original vertex)) = _
  rw [AlgEquiv.apply_symm_apply]
  exact hbasis vertex

/-- Localization has exactly the finite-Coxeter left reflection divisibility conditions. -/
theorem localization_image (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    (∃ polynomial : Dihedral.DoubleCoinvariant.Presentation n,
      (localization n hthree polynomial).val = value) ↔
        ∀ vertex (alpha : PositiveRoot n),
          alpha.form ∣ value vertex - value (alpha.reflection * vertex) := by
  let := Dihedral.DoubleCoinvariant.firstAlgebra n
  let := (RootSubset.full n).leftAlgebra hthree
  constructor
  · rintro ⟨polynomial, rfl⟩
    exact (RootSubset.full_iff_left n hthree _).mp (localization n hthree polynomial).property
  · intro hvalue
    let spline : (RootSubset.full n).Spline :=
      ⟨value, (RootSubset.full_iff_left n hthree value).mpr hvalue⟩
    exact ⟨(localization n hthree).symm spline,
      congrArg Subtype.val ((localization n hthree).apply_symm_apply spline)⟩

/-- A polynomial class localizes by the action in its second coordinate pair. -/
theorem localization_mk (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : Dihedral.DoubleCoinvariant.DoublePolynomial) (vertex : DihedralGroup n) :
    (localization n hthree (Ideal.Quotient.mk (Dihedral.DoubleCoinvariant.relations n)
      polynomial)).val vertex =
      MvPolynomial.aeval (Sum.elim MvPolynomial.X
        (fun index => polynomialAction n vertex (MvPolynomial.X index))) polynomial := by
  let := Dihedral.DoubleCoinvariant.firstAlgebra n
  let := Dihedral.DoubleCoinvariant.firstTower n
  let := (RootSubset.full n).leftAlgebra hthree
  let evaluation : (RootSubset.full n).Spline →ₐ[ℂ] CoordinatePolynomial :=
    (Pi.evalAlgHom ℂ (fun _ : DihedralGroup n => CoordinatePolynomial) vertex).comp
      (RootSubset.full n).splineAlgebra.val
  have hmaps : (evaluation.comp ((localization n hthree).restrictScalars ℂ)).comp
      (Ideal.Quotient.mkₐ ℂ (Dihedral.DoubleCoinvariant.relations n)) =
      MvPolynomial.aeval (Sum.elim MvPolynomial.X
        (fun index => polynomialAction n vertex (MvPolynomial.X index))) := by
    ext1 coordinate
    cases coordinate with
    | inl index =>
        simpa [evaluation, Dihedral.DoubleCoinvariant.firstMap] using
          localization_first n hthree (MvPolynomial.X index) vertex
    | inr index =>
        simpa [evaluation, Dihedral.DoubleCoinvariant.secondMap] using
          localization_second n hthree (MvPolynomial.X index) vertex
  exact AlgHom.congr_fun hmaps polynomial

/-- The root condition uses the coefficientwise complexification of its real form. -/
theorem root_form_real {n : ℕ} (alpha : PositiveRoot n) :
    alpha.form = MvPolynomial.map Complex.ofRealHom
      (MvPolynomial.C (alpha.val 0) * MvPolynomial.X 0 +
        MvPolynomial.C (alpha.val 1) * MvPolynomial.X 1) := by
  simp [PositiveRoot.form, linearPolynomial, complexify]

/-- A double polynomial class localizes by the inverse geometric substitution. -/
theorem localization_inverse (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : Dihedral.DoubleCoinvariant.DoublePolynomial) (vertex : DihedralGroup n) :
    (localization n hthree (Ideal.Quotient.mk (Dihedral.DoubleCoinvariant.relations n)
      polynomial)).val vertex =
      MvPolynomial.aeval (Sum.elim MvPolynomial.X (inverseCoordinate n vertex)) polynomial := by
  simpa only [polynomialAction_inverse_X] using localization_mk n hthree polynomial vertex

end Schubert.DihedralSplines.DoubleCoinvariant
